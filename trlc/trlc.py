#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2022 Bayerische Motoren Werke Aktiengesellschaft (BMW AG)
#
# This file is part of the TRLC Python Reference Implementation.
#
# TRLC is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TRLC is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with TRLC. If not, see <https://www.gnu.org/licenses/>.

import os
from argparse import ArgumentParser

from trlc import ast
from trlc import lint
from trlc.errors import TRLC_Error, Location, Message_Handler
from trlc.parser import Parser
from trlc.version import TRLC_VERSION


class Source_Manager:
    """Dependency and source manager for TRLC.

    This is the main entry point when using the Python API. Create an
    instance of this, register the files you want to look at, and
    finally call the process method.

    :param mh: The message handler to use
    :type mh: Message_Handler

    """
    def __init__(self, mh):
        assert isinstance(mh, Message_Handler)
        self.mh          = mh
        self.stab        = ast.Symbol_Table.create_global_table(mh)
        self.rsl_files   = {}
        self.check_files = {}
        self.trlc_files  = {}
        self.packages    = {}

    def create_parser(self, file_name):
        assert os.path.isfile(file_name)
        return Parser(mh           = self.mh,
                      stab         = self.stab,
                      file_name    = file_name)

    def register_package(self, package_name, file_name=None):
        if package_name in self.packages:
            self.packages[package_name]["file"] = file_name
        else:
            self.packages[package_name] = {"name" : package_name,
                                           "deps" : set(),
                                           "file" : file_name}

    def register_dependency(self, package_name, import_name):
        if import_name not in self.packages:
            self.register_package(import_name)
        self.packages[package_name]["deps"].add(import_name)

    def register_file(self, file_name):
        """Schedule a file for parsing.

        :param file_name: name of the file
        :type file_name: str
        :raise AssertionError: if the file does not exist
        :raise AssertionError: if the file is registed more than once
        :raise TRLC_Error: if the file is not a rsl/check/trlc file
        """
        assert os.path.isfile(file_name)

        if file_name.endswith(".rsl"):
            self.register_rsl_file(file_name)
        elif file_name.endswith(".check"):
            self.register_check_file(file_name)
        elif file_name.endswith(".trlc"):
            self.register_trlc_file(file_name)
        else:
            self.mh.error(Location(os.path.basename(file_name)),
                          "is not a rsl, check, or trlc file")

    def register_directory(self, dir_name):
        """Schedule a directory tree for parsing.

        :param dir_name: name of the directory
        :type file_name: str
        :raise AssertionError: if the directory does not exist
        :raise AssertionError: if any item in the directory is already \
        registered
        """
        assert os.path.isdir(dir_name)

        for path, _, files in os.walk(dir_name):
            for file_name in files:
                if file_name.endswith(".rsl"):
                    self.register_rsl_file(os.path.join(path, file_name))
                elif file_name.endswith(".check"):
                    self.register_check_file(os.path.join(path, file_name))
                elif file_name.endswith(".trlc"):
                    self.register_trlc_file(os.path.join(path, file_name))

    def register_rsl_file(self, file_name):
        assert os.path.isfile(file_name)
        assert file_name not in self.rsl_files

        self.rsl_files[file_name] = self.create_parser(file_name)
        self.rsl_files[file_name].parse_rsl_header()

        self.register_package(
            package_name = self.rsl_files[file_name].pkg.name,
            file_name    = file_name)
        for import_name in self.rsl_files[file_name].raw_deps:
            self.register_dependency(
                package_name = self.rsl_files[file_name].pkg.name,
                import_name  = import_name.value)

    def register_check_file(self, file_name):
        assert os.path.isfile(file_name)
        assert file_name not in self.check_files

        self.check_files[file_name] = self.create_parser(file_name)

    def register_trlc_file(self, file_name):
        assert os.path.isfile(file_name)
        assert file_name not in self.trlc_files

        self.trlc_files[file_name] = self.create_parser(file_name)

    def parse_rsl_files(self):
        # First, check that each package import is known
        for parser in self.rsl_files.values():
            for t_import in parser.raw_deps:
                parser.deps.append(parser.stab.lookup(self.mh,
                                                      t_import,
                                                      ast.Package))

        # Second, parse packages that have no unparsed
        # dependencies. Keep doing it until we parse everything or
        # until we have reached a fix point (in which case we have a
        # cycle in our dependencies).
        processed_packages = set()
        while self.packages:
            work_list = [pkg_name
                         for pkg_name, pkg in self.packages.items()
                         if pkg_name not in processed_packages and
                            pkg["deps"] <= processed_packages]

            if not work_list:
                conflicts = list(self.packages)
                for name in sorted(conflicts):
                    print("> %s depends on %s" %
                          (name,
                           ", ".join(sorted(set(self.packages[name]["deps"]) -
                                            processed_packages))))
                self.mh.error(
                    Location(list(self.packages.values())[0]["file"]),
                    "circular inheritence")

            for pkg in work_list:
                self.rsl_files[self.packages[pkg]["file"]].parse_rsl_file()
                processed_packages.add(pkg)
                del self.packages[pkg]

    def parse_check_files(self):
        ok = True
        for parser in self.check_files.values():
            try:
                parser.parse_check_file()
            except TRLC_Error:
                ok = False
        return ok

    def parse_trlc_files(self):
        ok = True
        for parser in self.trlc_files.values():
            try:
                parser.parse_trlc_file()
            except TRLC_Error:
                ok = False
        return ok

    def resolve_record_references(self):
        ok = True
        for package in self.stab.values(ast.Package):
            for obj in package.symbols.values(ast.Record_Object):
                try:
                    obj.resolve_references(self.mh)
                except TRLC_Error:
                    ok = False

        return ok

    def perform_checks(self):
        ok = True
        for package in self.stab.values(ast.Package):
            for obj in package.symbols.values(ast.Record_Object):
                try:
                    if not obj.perform_checks(self.mh):
                        ok = False
                except TRLC_Error:
                    ok = False

        return ok

    def perform_sanity_checks(self):
        ok = True
        for package in self.stab.values(ast.Package):
            for obj in package.symbols.values(ast.Record_Type):
                try:
                    lint.verify_record(self.mh, obj)
                except TRLC_Error:
                    ok = False
        return ok

    def process(self, lint_mode=False):
        """Parse all registered files.

        :param lint_mode: don't parse instances and perform static \
        analysis on the model and checks instead
        :type lint_mode: bool

        :return: a symbol table (or None if there were any errors)
        :rtype: Symbol_Table
        """
        assert isinstance(lint_mode, bool)

        # Parse RSL files (topologically sorted, in order to deal with
        # dependencies)
        try:
            self.parse_rsl_files()
        except TRLC_Error:
            return None

        # Parse check files. At this point we cannot introduce anything
        # new in terms of packages.
        ok = True
        if not self.parse_check_files():
            ok = False

        # If we run in lint mode, then we perform the checks now and then
        # stop. We do not process the TRLC files.
        if lint_mode:
            if not ok:
                return None
            if not self.perform_sanity_checks():
                return None
            print("Verified %u model(s) and check(s), and found no issues." %
                  (len(self.rsl_files) + len(self.check_files)))
            print("Note: The lint option is a placeholder and does"
                  " not do anything yet.")
            return self.stab

        # Parse TRLC files. Almost all the semantic analysis and name
        # resolution happens here, with the notable exception of resolving
        # record references (as we can have circularity here).
        if not self.parse_trlc_files():
            return None

        # Resolve record reference names and do the missing semantic
        # analysis.
        if not self.resolve_record_references():
            return None

        if not ok:
            return None

        # Finally, apply user defined checks
        if not self.perform_checks():
            return None

        return self.stab


def main():
    ap = ArgumentParser(
        description="TRLC %s (Python reference implementation)" % TRLC_VERSION
    )
    ap.add_argument("--debug-dump",
                    default=False,
                    action="store_true",
                    help="dump symbol table")
    ap.add_argument("--lint",
                    default=False,
                    action="store_true",
                    help="sanity check models and checks")
    ap.add_argument("dir_name",
                    metavar="DIR")
    options = ap.parse_args()

    mh = Message_Handler()
    sm = Source_Manager(mh)

    if not os.path.isdir(options.dir_name):
        ap.error("%s is not a directory" % options.dir_name)

    # Process input files
    ok = True
    for path, _, files in os.walk(options.dir_name):
        for file_name in files:
            if file_name.endswith(".rsl"):
                try:
                    sm.register_rsl_file(os.path.join(path, file_name))
                except TRLC_Error:
                    ok = False
            elif file_name.endswith(".check"):
                sm.register_check_file(os.path.join(path, file_name))
            elif file_name.endswith(".trlc"):
                sm.register_trlc_file(os.path.join(path, file_name))
    if not ok:
        return 1

    if sm.process(lint_mode = options.lint) is None:
        return 1
    else:
        if options.debug_dump:
            sm.stab.dump()
        return 0


if __name__ == "__main__":
    main()