#!/usr/bin/env python3
#
# TRLC - Treat Requirements Like Code
# Copyright (C) 2026 Florian Schanda
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

import subprocess

from pyvcg import smt
from pyvcg import graph
from pyvcg import vcg
from pyvcg.driver.file_smtlib import SMTLIB_Generator
from pyvcg.driver.cvc5_smtlib import CVC5_File_Solver

try:
    from pyvcg.driver.cvc5_api import CVC5_Solver
    CVC5_API_AVAILABLE = True
except ImportError:  # pragma: no cover
    CVC5_API_AVAILABLE = False

from trlc import ast
from trlc.errors import Location, Message_Handler

CVC5_OPTIONS = {
    "tlimit-per"      : 2500,
    "seed"            : 42,
    "sat-random-seed" : 42,
}


class Unsupported(Exception):  # pragma: no cover
    # lobster-exclude: Not safety relevant
    def __init__(self, node, text):
        assert isinstance(node, ast.Node)
        assert isinstance(text, str) or text is None
        super().__init__()
        self.message  = text
        self.location = node.location


class Feedback:
    KINDS = frozenset(["evaluation-of-null",
                       "div-by-zero",
                       "array-index",
                       "always-true"])

    # lobster-exclude: Not safety relevant
    def __init__(self, loc, message, kind, expect_unsat=True):
        assert isinstance(loc, Location)
        assert isinstance(message, str)
        assert kind in Feedback.KINDS
        assert isinstance(expect_unsat, bool)
        self.loc          = loc
        self.message      = message
        self.kind         = "vcg-" + kind
        self.expect_unsat = expect_unsat


class VCG:
    # lobster-exclude: Not safety relevant
    def __init__(self, mh, n_ctyp, debug, use_api=True, cvc5_binary=None):
        assert isinstance(mh, Message_Handler)
        assert isinstance(n_ctyp, ast.Composite_Type)
        assert isinstance(debug, bool)
        assert isinstance(use_api, bool)
        assert use_api or isinstance(cvc5_binary, str)

        self.mh       = mh
        self.n_ctyp   = n_ctyp
        self.debug    = debug
        self.use_api  = use_api
        self.cvc5_bin = cvc5_binary

        self.vc_name = "trlc-%s-%s" % (n_ctyp.n_package.name,
                                       n_ctyp.name)
        self.tmp_id = 0

        self.vcg   = vcg.VCG()
        self.graph = self.vcg.graph

        self.gn_current = self.vcg.start
        # Current node, we will update this as we go along.

        self.preamble = self.vcg.start
        # We do remember the first node where we put all our
        # declarations, in case we need to add some more later.

        self.s_this = None
        # This will take a reference to the current "instance",
        # i.e. a constant of the type we analyse

        self.basic_sorts = {}
        # Direct translations for non-builtin types
        #   ast.Composite_Type   -> smt.Record
        #   ast.Enumeration_Type -> smt.Enumeration
        #   ast.Array_Type       -> smt.Sequence_Sort

        self.component_sorts = {}
        # Translations for record components (this is where the
        # optional types live)
        #   ast.Composite_Component -> smt.Optional
        #   ast.Composite_Component -> <something from basic_sorts>

        self.optional_sorts = {}
        # To make sure we don't create duplicates we cache them here
        #   smt.Sort -> smt.Optional

    @staticmethod
    def flag_unsupported(node, text=None):  # pragma: no cover
        assert isinstance(node, ast.Node)
        raise Unsupported(node, text)

    def new_temp_name(self):
        self.tmp_id += 1
        return "tmp.%u" % self.tmp_id

    def analyse(self):
        try:
            self.analyse_composite_type(self.n_ctyp)
        except Unsupported as exc:  # pragma: no cover
            self.mh.warning(exc.location,
                            "currently unsupported in VCG (%s)" % exc.message)

    def analyse_composite_type(self, n_ctyp):
        assert isinstance(n_ctyp, ast.Composite_Type)

        # Create variable(s)
        s_sort = self.tr_type(n_typ            = n_ctyp,
                              indirect_records = False)
        self.s_this = smt.Constant(sort = s_sort,
                                   name = "this")
        self.preamble.add_statement(
            smt.Constant_Declaration(symbol   = self.s_this,
                                     relevant = True))

        # Add constraints
        self.assert_type_constraints(s_expr           = self.s_this,
                                     n_typ            = n_ctyp,
                                     indirect_records = False)
        if self.debug:
            subprocess.run(["dot",
                            "-Tpdf",
                            "-o%s-types.pdf" % self.vc_name],
                           input=self.graph.debug_render_dot(),
                           check=True,
                           encoding="UTF-8")

        # Traverse checks and create graph
        self.build_graph()
        if self.debug:
            subprocess.run(["dot",
                            "-Tpdf",
                            "-o%s-graph.pdf" % self.vc_name],
                           input=self.graph.debug_render_dot(),
                           check=True,
                           encoding="UTF-8")

        # Generate VCs + Solve
        self.vcg.generate()
        for vc_id, vc in enumerate(self.vcg.vcs):
            if self.debug:  # pramga: no cover
                with open(self.vc_name + "_%04u.smt2" % vc_id, "w",
                          encoding="UTF-8") as fd:
                    fd.write(vc["script"].generate_vc(SMTLIB_Generator()))

    ######################################################################
    # Types -> SMTLIB Sorts
    ######################################################################

    def tr_type(self, n_typ, indirect_records=True):
        # Translate a Type into an SMTLIB sort
        assert isinstance(n_typ, ast.Type)
        assert isinstance(indirect_records, bool)

        if isinstance(n_typ, ast.Record_Type) and indirect_records:
            # Record references are translated differently. We treat
            # them as integers, and we will later use an uninterpreted
            # function to retrieve an instance.
            return smt.BUILTIN_INTEGER
        elif isinstance(n_typ, ast.Composite_Type):
            return self.tr_type_composite(n_typ)
        elif isinstance(n_typ, ast.Enumeration_Type):
            return self.tr_type_enumeration(n_typ)
        elif isinstance(n_typ, ast.Array_Type):
            return self.tr_type_array(n_typ)
        elif isinstance(n_typ, ast.Builtin_String):
            return smt.BUILTIN_STRING
        elif isinstance(n_typ, ast.Builtin_Integer):
            return smt.BUILTIN_INTEGER
        elif isinstance(n_typ, ast.Builtin_Decimal):
            return smt.BUILTIN_REAL
        elif isinstance(n_typ, ast.Builtin_Boolean):
            return smt.BUILTIN_BOOLEAN
        else:
            self.flag_unsupported(
                n_typ,
                "translation of %s is not supported yet" %
                n_typ.__class__.__name__)
            return None

    def tr_type_composite(self, n_typ):
        # Translate a tuple or record type
        assert isinstance(n_typ, ast.Composite_Type)
        if n_typ in self.basic_sorts:
            return self.basic_sorts[n_typ]

        s_sort = smt.Record(n_typ.name)
        for n_component in n_typ.components.values():
            s_sort.add_component(
                name = n_component.name,
                sort = self.tr_type_of_composite_component(n_component))

        self.preamble.add_statement(smt.Record_Declaration(s_sort))
        self.basic_sorts[n_typ] = s_sort
        return s_sort

    def tr_type_of_composite_component(self, n_component):
        # Translate the type of a component (optional or regular)
        assert isinstance(n_component, ast.Composite_Component)
        if n_component in self.component_sorts:
            return self.component_sorts[n_component]

        if n_component.optional:
            s_sort = self.tr_type_optional(n_component.n_typ)
        else:
            s_sort = self.tr_type(n_component.n_typ)

        self.component_sorts[n_component] = s_sort
        return s_sort

    def tr_type_optional(self, n_typ):
        # Translate a given type as its optional version
        assert isinstance(n_typ, ast.Type)

        s_base_sort = self.tr_type(n_typ)
        if s_base_sort in self.optional_sorts:
            return self.optional_sorts[s_base_sort]

        s_sort = smt.Optional(s_base_sort)
        self.preamble.add_statement(smt.Optional_Declaration(s_sort))
        self.optional_sorts[s_base_sort] = s_sort
        return s_sort

    def tr_type_enumeration(self, n_typ):
        # Translate the given enum type
        assert isinstance(n_typ, ast.Enumeration_Type)
        if n_typ in self.basic_sorts:
            return self.basic_sorts[n_typ]

        s_sort = smt.Enumeration(n_typ.name)
        for n_literal_spec in n_typ.literals.values():
            assert isinstance(n_literal_spec, ast.Enumeration_Literal_Spec)
            s_sort.add_literal(n_literal_spec.name)

        self.preamble.add_statement(smt.Enumeration_Declaration(s_sort))
        self.basic_sorts[n_typ] = s_sort
        return s_sort

    def tr_type_array(self, n_typ):
        # Translate the given array type. Note that any constraints
        # (e.g. on length) will be added later, they are not part of
        # the sort.
        assert isinstance(n_typ, ast.Array_Type)
        if n_typ in self.basic_sorts:
            return self.basic_sorts[n_typ]

        s_element_sort = self.tr_type(n_typ.element_type)
        s_sort = smt.Sequence_Sort(s_element_sort)

        # No declaration for this as it's a parametric builtin type
        self.basic_sorts[n_typ] = s_sort
        return s_sort

    ######################################################################
    # Types constraints
    ######################################################################

    def assert_type_constraints(self, s_expr, n_typ, indirect_records=True):
        # Assert on the given expression that all type constraints are
        # met.
        assert isinstance(s_expr, smt.Expression)
        assert isinstance(n_typ, ast.Type)
        assert isinstance(indirect_records, bool)
        assert self.tr_type(n_typ, indirect_records) is s_expr.sort

        s_constraints = self.build_type_constraints(s_expr,
                                                    n_typ,
                                                    indirect_records)

        if s_constraints.is_static_true():
            return

        # This is not necessary but it makes VCs a bit more readable.
        if isinstance(s_constraints, smt.Conjunction):
            for term in s_constraints.terms:
                self.gn_current.add_statement(smt.Assertion(term))
        else:
            self.gn_current.add_statement(smt.Assertion(s_constraints))

    def build_type_constraints(self, s_expr, n_typ, indirect_records=True):
        # Create a boolean expression involving the given expression
        # that captures all type constraints of the given type.
        assert isinstance(s_expr, smt.Expression)
        assert isinstance(n_typ, ast.Type)
        assert isinstance(indirect_records, bool)
        assert self.tr_type(n_typ, indirect_records) is s_expr.sort

        if isinstance(n_typ, ast.Record_Type) and indirect_records:
            # TODO. Need to apply the UF and apply constraints on the
            # result
            return smt.Boolean_Literal(True)
        elif isinstance(n_typ, ast.Composite_Type):
            return self.build_type_constraints_composite(s_expr,
                                                         n_typ)
        elif isinstance(n_typ, ast.Array_Type):
            return self.build_type_constraints_array(s_expr, n_typ)
        elif isinstance(n_typ, (ast.Enumeration_Type,
                                ast.Builtin_String,
                                ast.Builtin_Integer,
                                ast.Builtin_Decimal,
                                ast.Builtin_Boolean)):
            return smt.Boolean_Literal(True)
        else:
            self.flag_unsupported(
                n_typ,
                "type constraints for %s are not supported yet" %
                n_typ.__class__.__name__)
            return None

    def build_type_constraints_composite(self, s_expr, n_typ):
        assert isinstance(s_expr, smt.Expression)
        assert isinstance(n_typ, ast.Composite_Type)
        assert self.tr_type(n_typ, indirect_records=False) is s_expr.sort

        terms = []

        # Classic field-specific constraints
        for n_component in n_typ.components.values():
            s_field = smt.Record_Access(record    = s_expr,
                                        component = n_component.name)

            if n_component.optional:
                s_value = smt.Optional_Value(s_field)
            else:
                s_value = s_field
            s_constraint = self.build_type_constraints(
                s_expr = s_value,
                n_typ  = n_component.n_typ)

            if s_constraint.is_static_true():
                # If the constraint itself is always true, then we can
                # just skip the component since X -> true is always
                # true.
                continue

            if n_component.optional:
                s_term = smt.Implication(
                    smt.Boolean_Negation(smt.Optional_Null_Check(s_field)),
                    s_constraint)
            else:
                s_term = s_constraint

            terms.append(s_term)

        # Tuples (with optional fields) have one more property we need
        # to take care of.
        # lobster-trace: LRM.Tuple_Separator_Form
        # Specifically once we get a null field, the rest are also
        # null.
        if isinstance(n_typ, ast.Tuple_Type) and n_typ.has_separators():
            s_prev = None
            for n_component in n_typ.components.values():
                if n_component.optional:
                    s_field = smt.Record_Access(record    = s_expr,
                                                component = n_component.name)
                    if s_prev is not None:
                        s_term = smt.Implication(
                            smt.Optional_Null_Check(s_prev),
                            smt.Optional_Null_Check(s_field))
                        terms.append(s_term)
                    s_prev = s_field

        # TODO: assume successful checks for tuple types
        # TODO: assume successful pre-reference checks for records

        return self.simplify_conjunction(terms)

    def build_type_constraints_array(self, s_expr, n_typ):
        assert isinstance(s_expr, smt.Expression)
        assert isinstance(n_typ, ast.Array_Type)
        assert self.tr_type(n_typ) is s_expr.sort

        terms = []

        # Constraint for minimum size (if any)
        if n_typ.lower_bound > 0:
            terms.append(
                smt.Comparison(">=",
                               smt.Sequence_Length(s_expr),
                               smt.Integer_Literal(n_typ.lower_bound)))

        # Constraint for maximum size (if any)
        if n_typ.upper_bound is not None:
            terms.append(
                smt.Comparison("<=",
                               smt.Sequence_Length(s_expr),
                               smt.Integer_Literal(n_typ.upper_bound)))

        # Type constraints for all elements
        s_bound_var = smt.Bound_Variable(sort = smt.BUILTIN_INTEGER,
                                         name = self.new_temp_name())
        s_value = smt.Sequence_Index(sequence = s_expr,
                                     index    = s_bound_var)
        s_predicate = self.build_type_constraints(s_expr = s_value,
                                                  n_typ  = n_typ.element_type)
        if not s_predicate.is_static_true():
            s_guard = smt.Conjunction(
                smt.Comparison(">=",
                               s_bound_var,
                               smt.Integer_Literal(0)),
                smt.Comparison("<",
                               s_bound_var,
                               smt.Sequence_Length(s_expr)))
            s_body = smt.Implication(s_guard, s_predicate)
            terms.append(
                smt.Quantifier(kind      = "forall",
                               variables = [s_bound_var],
                               body      = s_body))

        return self.simplify_conjunction(terms)

    ######################################################################
    # VCG
    ######################################################################

    def build_graph(self):
        # Build graph from which we generate VCs. Some important
        # notes:
        #
        # lobster-trace: LRM.Check_Evaluation_Order
        # Inside a check block, we get the obvious order.
        #
        # lobster-trace: LRM.Check_Evaluation_Order_Across_Blocks
        # If the user has multiple check blocks they need to be
        # evaluated "in parallel", i.e. we cannot rely on fatal
        # messages from one to guarantee properties
        #
        # lobster-trace: LRM.Check_Evaluation_Order_For_Extensions
        # That said, for type extensions we can assume all parent
        # checks have been evaluated (in any order) before we get to
        # ours, so we can assume fatal checks.
        check_groups = self.build_check_groups(self.n_ctyp)

        # First we assert all fatal checks from extended types as
        # background knowledge. We can do it in any order.
        for check_group in check_groups["established"]:
            assert isinstance(check_group, list)
            for n_check_block in check_group:
                assert isinstance(n_check_block, ast.Check_Block)
                self.build_check_block(n_block     = n_check_block,
                                       with_checks = False)

        # Then we check the current type's check blocks (independent
        # of ordering).
        gn_start = self.gn_current
        for n_check_block in check_groups["new"]:
            assert isinstance(n_check_block, ast.Check_Block)
            self.gn_current = gn_start
            self.build_check_block(n_block     = n_check_block,
                                   with_checks = True)

    def build_check_groups(self, n_typ):
        # Create sets of checks that must be evaluated together
        # lobster-trace: LRM.Check_Evaluation_Order_Across_Blocks
        # lobster-trace: LRM.Check_Evaluation_Order_For_Extensions
        assert isinstance(n_typ, ast.Composite_Type)

        check_groups = {
            "established" : [],
            "new"         : n_typ.check_blocks
        }
        if isinstance(n_typ, ast.Record_Type):
            n_ptr = n_typ.parent
            while n_ptr is not None:
                if n_ptr.check_blocks:
                    check_groups["established"].insert(0, n_ptr.check_blocks)
                n_ptr = n_ptr.parent
        elif isinstance(n_typ, ast.Tuple_Type):
            pass
        else:
            self.flag_unsupported(n_typ,
                                  "unexpected composite type %s" %
                                  n_typ.__class__.__name__)

        return check_groups

    def build_check_block(self, n_block, with_checks):
        # Create checks in the graph for this block. Ensures that
        # self.gn_current will end up a single node that flows out of
        # all paths from this check block.
        assert isinstance(n_block, ast.Check_Block)
        assert isinstance(with_checks, bool)

        gn_start = self.gn_current
        for n_check in n_block.checks:
            if n_check.severity in ("warning", "error"):
                # For non-fatal checks we simply reset the current
                # node so that our path is a dead-end (since no future
                # check can rely on it). If we don't do checks we can
                # also totally ignore them, because they do not
                # terminate execution.
                if with_checks:
                    self.build_check(n_check, with_checks)
                    self.gn_current = gn_start
            elif n_check.severity == "fatal":
                # For fatal checks we adjust gn_start so subsequent
                # checks can rely on the properties asserted by the
                # check
                self.build_check(n_check, with_checks)
                gn_start = self.gn_current
            else:
                self.flag_unsupported(n_check,
                                      "unexpected severity %s" %
                                      n_check.severity)

    def build_check(self, n_check, with_checks):
        assert isinstance(n_check, ast.Check)
        assert isinstance(with_checks, bool)

        s_expr = self.build_expression(n_expr      = n_check.n_expr,
                                       with_checks = with_checks)

        gn = graph.Assumption(self.graph)
        gn.add_statement(smt.Assertion(s_expr))
        self.gn_current.add_edge_to(gn)
        self.gn_current = gn

    ######################################################################
    # Checks
    ######################################################################

    def check_not_null(self, loc, s_expr):
        assert isinstance(loc, Location)
        assert isinstance(s_expr, smt.Expression)

        s_goal = self.mk_is_not_null(s_expr)

        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            expression = s_goal,
            feedback   = Feedback(loc     = loc,
                                  message = "might be null",
                                  kind    = "evaluation-of-null"),
            comment    = "null check at %s" % loc.to_string())
        self.gn_current.add_edge_to(gn_check)

        self.gn_current = gn_check

    def check_div_by_zero(self, loc, s_expr):
        assert isinstance(loc, Location)
        assert isinstance(s_expr, smt.Expression)

        s_goal = smt.Boolean_Negation(
            smt.Comparison("=",
                           s_expr,
                           smt.Integer_Literal(0)))

        gn_check = graph.Check(self.graph)
        gn_check.add_goal(
            expression = s_goal,
            feedback   = Feedback(loc     = loc,
                                  message = "potential division by zero",
                                  kind    = "div-by-zero"),
            comment    = "division by zero check at %s" % loc.to_string())
        self.gn_current.add_edge_to(gn_check)

        self.gn_current = gn_check

    ######################################################################
    # Expressions
    ######################################################################

    def build_expression(self, n_expr, with_checks, permit_null=False):
        assert isinstance(n_expr, ast.Expression)
        assert isinstance(with_checks, bool)
        assert isinstance(permit_null, bool)

        if False:
            pass
        elif isinstance(n_expr, ast.Binary_Expression):
            s_rv = self.build_expression_binary(n_expr, with_checks)
        elif isinstance(n_expr, ast.Integer_Literal):
            s_rv = smt.Integer_Literal(n_expr.value)
        elif isinstance(n_expr, ast.Name_Reference):
            s_rv = self.build_expression_name_reference(n_expr)
        else:
            self.flag_unsupported(n_expr,
                                  "unexpected expression type %s" %
                                  n_expr.__class__.__name__)

        if with_checks and not permit_null and n_expr.can_be_null():
            self.check_not_null(n_expr.location, s_rv)

        return s_rv

    def build_expression_binary(self, n_expr, with_checks):
        # Build expression for all binary expressions
        assert isinstance(n_expr, ast.Binary_Expression)
        assert isinstance(with_checks, bool)

        smt_int_op = {ast.Binary_Operator.PLUS   : "+",
                      ast.Binary_Operator.MINUS  : "-",
                      ast.Binary_Operator.TIMES  : "*",
                      ast.Binary_Operator.DIVIDE : "floor_div"}
        smt_dec_op = {ast.Binary_Operator.PLUS   : "+",
                      ast.Binary_Operator.MINUS  : "-",
                      ast.Binary_Operator.TIMES  : "*",
                      ast.Binary_Operator.DIVIDE : "/"}

        # Equality is extra weird, so we deal with it first
        if n_expr.operator in (ast.Binary_Operator.COMP_EQ,
                               ast.Binary_Operator.COMP_NEQ):
            return self.build_expression_equality(n_expr, with_checks)

        # Secondly, some binary operators (and, or, implies) have
        # short-cut semantics. For them we need to deal with the
        # branch.
        if n_expr.operator in (ast.Binary_Operator.LOGICAL_AND,
                               ast.Binary_Operator.LOGICAL_OR,
                               ast.Binary_Operator.LOGICAL_IMPLIES):
            return self.build_expression_shortcut(n_expr, with_checks)

        # Otherwise, we have something normal, and so we need to check
        # for null.
        s_lhs = self.mk_value(self.build_expression(n_expr.n_lhs, with_checks))
        s_rhs = self.mk_value(self.build_expression(n_expr.n_rhs, with_checks))


        if n_expr.operator in (ast.Binary_Operator.COMP_EQ,
                               ast.Binary_Operator.COMP_NEQ):
            self.mh.ice_loc(n_expr, "impossible")
        elif n_expr.operator == ast.Binary_Operator.COMP_LT:
            return smt.Comparison("<", s_lhs, s_rhs)
        elif n_expr.operator == ast.Binary_Operator.COMP_GT:
            return smt.Comparison(">", s_lhs, s_rhs)
        elif n_expr.operator == ast.Binary_Operator.COMP_LEQ:
            return smt.Comparison("<=", s_lhs, s_rhs)
        elif n_expr.operator == ast.Binary_Operator.COMP_GEQ:
            return smt.Comparison(">=", s_lhs, s_rhs)
        elif n_expr.operator in (ast.Binary_Operator.PLUS,
                                 ast.Binary_Operator.MINUS,
                                 ast.Binary_Operator.TIMES,
                                 ast.Binary_Operator.DIVIDE):
            if with_checks:
                if n_expr.operator == ast.Binary_Operator.DIVIDE:
                    self.check_div_by_zero(n_expr.location, s_rhs)

            if isinstance(n_expr.typ, ast.Builtin_Integer):
                return smt.Binary_Int_Arithmetic_Op(
                    smt_int_op[n_expr.operator],
                    s_lhs,
                    s_rhs)
            elif isinstance(n_expr.typ, ast.Builtin_Decimal):
                return smt.Binary_Real_Arithmetic_Op(
                    smt_dec_op[n_expr.operator],
                    s_lhs,
                    s_rhs)
            else:
                self.flag_unsupported(n_expr,
                                      "arithmetic on %s" %
                                      n_expr.typ.name)
        else:
            self.flag_unsupported(n_expr, "operator %s" % n_expr.operator)
            return None

    def build_expression_name_reference(self, n_expr):
        assert isinstance(n_expr, ast.Name_Reference)

        if isinstance(n_expr.entity, ast.Composite_Component):
            return smt.Record_Access(record    = self.s_this,
                                     component = n_expr.entity.name)
        else:
            self.flag_unsupported(n_expr,
                                  "%s name reference" %
                                  n_expr.__class__.__name__)
            return None

    def build_expression_equality(self, n_expr, with_checks):
        # Build expression for equality and inequality
        assert isinstance(n_expr, ast.Binary_Expression)
        assert n_expr.operator in (ast.Binary_Operator.COMP_EQ,
                                   ast.Binary_Operator.COMP_NEQ)
        assert isinstance(with_checks, bool)

        # There is a special case we need to deal with, and that is
        # comparison to the null literal.
        if isinstance(n_expr.n_lhs, ast.Null_Literal) and \
           isinstance(n_expr.n_rhs, ast.Null_Literal):
            # Special case of null == null is always true
            # lobster-trace: LRM.Equality_On_Null
            # lobster-trace: LRM.Null_Equivalence
            return smt.Boolean_Literal(n_expr.operator ==
                                       ast.Binary_Operator.COMP_EQ)

        elif isinstance(n_expr.n_lhs, ast.Null_Literal) or \
             isinstance(n_expr.n_rhs, ast.Null_Literal):
            # This is an explicit null check against the literal. We
            # get a term for the not-null side and then apply a null
            # check
            if isinstance(n_expr.n_lhs, ast.Null_Literal):
                n_operand = n_expr.n_rhs
            else:
                n_operand = n_expr.n_lhs
            s_operand = self.build_expression(n_operand, with_checks, True)
            if n_expr.operator == ast.Binary_Operator.COMP_EQ:
                return self.mk_is_null(s_operand)
            else:
                return self.mk_is_not_null(s_operand)

        else:
            # Neither side is a null literal (but either side could be
            # a null *value*).
            s_lhs = self.build_expression(n_expr.n_lhs, with_checks, True)
            s_rhs = self.build_expression(n_expr.n_rhs, with_checks, True)

            s_rv = self.mk_null_aware_equality(s_lhs, s_rhs)
            if n_expr.operator == ast.Binary_Operator.COMP_NEQ:
                s_rv = smt.Boolean_Negation(s_rv)
            return s_rv

    def build_expression_shortcut(self, n_expr, with_checks):
        # Build expression for binary operators with short-cut
        # semantics
        assert isinstance(n_expr, ast.Binary_Expression)
        assert n_expr.operator in (ast.Binary_Operator.LOGICAL_AND,
                                   ast.Binary_Operator.LOGICAL_OR,
                                   ast.Binary_Operator.LOGICAL_IMPLIES)
        assert isinstance(with_checks, bool)

        s_lhs = self.build_expression(n_expr.n_lhs, with_checks)

        if with_checks:
            gn_start = self.gn_current
            gn = graph.Assumption(self.graph)
            self.gn_current.add_edge_to(gn)
            self.gn_current = gn

            if n_expr.operator == ast.Binary_Operator.LOGICAL_OR:
                gn.add_statement(smt.Assertion(smt.Boolean_Negation(s_lhs)))
            else:
                gn.add_statement(smt.Assertion(s_lhs))

        s_rhs = self.build_expression(n_expr.n_rhs, with_checks)

        if n_expr.operator == ast.Binary_Operator.LOGICAL_AND:
            return smt.Conjunction(s_lhs, s_rhs)
        elif n_expr.operator == ast.Binary_Operator.LOGICAL_OR:
            return smt.Disjunction(s_lhs, s_rhs)
        else:
            return smt.Implication(s_lhs, s_rhs)

    ######################################################################
    # Utility
    ######################################################################

    @staticmethod
    def mk_is_null(s_expr):
        # Check if something is null
        assert isinstance(s_expr, smt.Expression)
        if isinstance(s_expr.sort, smt.Optional):
            return smt.Optional_Null_Check(s_expr)
        else:
            return smt.Boolean_Literal(False)

    @staticmethod
    def mk_is_not_null(s_expr):
        # Check if something is not null
        assert isinstance(s_expr, smt.Expression)
        if isinstance(s_expr.sort, smt.Optional):
            return smt.Boolean_Negation(smt.Optional_Null_Check(s_expr))
        else:
            return smt.Boolean_Literal(True)

    @staticmethod
    def mk_value(s_expr):
        # Access the value of an expression
        assert isinstance(s_expr, smt.Expression)
        if isinstance(s_expr.sort, smt.Optional):
            return smt.Optional_Value(s_expr)
        else:
            return s_expr

    @staticmethod
    def mk_null_aware_equality(s_lhs, s_rhs):
        # Check for equality when either side could be null
        assert isinstance(s_lhs, smt.Expression)
        assert isinstance(s_rhs, smt.Expression)
        s_lhs_is_null = VCG.mk_is_null(s_lhs)
        s_rhs_is_null = VCG.mk_is_null(s_rhs)

        s_both_null = smt.Conjunction(s_lhs_is_null,
                                      s_rhs_is_null)

        return smt.Disjunction(
            s_both_null,
            smt.Conjunction(smt.Boolean_Negation(s_lhs_is_null),
                            smt.Boolean_Negation(s_rhs_is_null),
                            smt.Comparison("=",
                                           VCG.mk_value(s_lhs),
                                           VCG.mk_value(s_rhs))))

    @staticmethod
    def simplify_conjunction(terms):
        # Condense a list of anded terms. The empty list generates
        # true.
        assert isinstance(terms, list)
        assert all(isinstance(t, smt.Expression) and
                   t.sort is smt.BUILTIN_BOOLEAN
                   for t in terms)

        nontrivial_terms = []
        num_terms        = 0
        for term in terms:
            if term.is_static_true():
                pass
            elif term.is_static_false():
                return smt.Boolean_Literal(False)
            else:
                nontrivial_terms.append(term)
                num_terms += 1

        if num_terms == 0:
            return smt.Boolean_Literal(True)
        elif num_terms == 1:
            return nontrivial_terms[0]
        else:
            return smt.Conjunction(*nontrivial_terms)
