from abc import ABCMeta, abstractmethod
from collections import defaultdict
from enum import Enum
from functools import reduce

def strip_parens(expr):
    """Strip surrounding parenthesis."""
    if expr[0] == '(' and expr[-1] == ')':
        return expr[1:-1]
    return expr

# basic operations
class Expression:

    def get_variables(self):
        return set()

class Const(Expression):
    def __init__(self, value):
        self.value = str(value)

    def __str__(self):
        return self.value

class Var(Expression):
    def __init__(self, name):
        self.name = name

    def get_variables(self):
        return set([self.name])

    def __str__(self):
        return self.name

class FunctionCall(Expression):

    def __init__(self, func_name, *args):
        for arg in args:
            assert isinstance(arg, Expression)

        self.func_name = func_name
        self.args = args

    def __str__(self):
        # strip parenthesis
        params = (strip_parens(arg) for arg in self.args)
        return '{}({})'.format(self.func_name, params)

class Arithmetic(Expression): pass

class UnaryOp(Arithmetic):

    def __init__(self, rhs):
        self.rhs = rhs

    def get_variables(self):
        return self.rhs.get_variables()

class Plus(UnaryOp):
    def __str__(self):
        return "(+{})".format(self.rhs)

class Minus(UnaryOp):
    def __str__(self):
        return "(-{})".format(self.rhs)

class BinaryOp(Arithmetic):

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def get_variables(self):
        return self.lhs.get_variables() | self.rhs.get_variables()

class Add(BinaryOp):
    def __str__(self):
        return "({} + {})".format(self.lhs, self.rhs)

class Subtract(BinaryOp):
    def __str__(self):
        return "({} - {})".format(self.lhs, self.rhs)

class Multiply(BinaryOp):
    def __str__(self):
        return "({} * {})".format(self.lhs, self.rhs)

class Divide(BinaryOp):
    def __str__(self):
        return "({} / {})".format(self.lhs, self.rhs)

class CmpOperator(Enum):
    LT = '<'
    LTE = '<='
    EQ = '=='
    NEQ = '!='
    GT = '>'
    GTE = '>='

class Compare(BinaryOp):
    def __init__(self, cmp_op, lhs, rhs):
        super().__init__(lhs, rhs)
        self.cmp_op = cmp_op

    def __str__(self):
        return "({} {} {})".format(self.lhs, self.cmp_op.value, self.rhs)


class Operation:

    def defined_variables(self):
        return set()

    def used_variables(self):
        return set()

class Noop(Operation):
    def __str__(self):
        return "Noop"

NOOP = Noop()

class Assign(Operation):
    def __init__(self, var, expr):
        assert isinstance(var, Var)
        assert isinstance(expr, Expression)

        self.var = var
        self.expr = expr

    def defined_variables(self):
        return self.var.get_variables()

    def used_variables(self):
        return self.expr.get_variables()

    def __str__(self):
        return "{} = {}".format(self.var, self.expr)

class If(Operation):
    def __init__(self, condition):
        assert isinstance(condition, Compare)
        self.cond = condition

    def used_variables(self):
        return self.cond.get_variables()

    def __str__(self):
        return "IF {}".format(self.cond)


class ControlFlowGraph:
    """It is the user's duty to ensure all nodes must be reachable from entry."""

    class QuadBlock:
        """A simple block with only 1 statement."""
        def __init__(self, cfg, no, operation):
            self.cfg = cfg
            self.no = no
            self.op = operation

            # record IN and OUT for different analyses
            # the key is name of an analysis
            self.IN = {}
            self.OUT = {}

        def set_operation(self, operation):
            self.op = operation

        def is_entry(self):
            return self == self.cfg.entry

        def is_exit(self):
            return self == self.cfg.exit

        def predecessors(self):
            return self.cfg.pred[self]

        def successors(self):
            return self.cfg.succ[self]

        def defined_variables(self):
            return self.op.defined_variables()

        def used_variables(self):
            return self.op.used_variables()

        def __eq__(self, other):
            return self.cfg == other.cfg and self.no == other.no

        def __hash__(self):
            return hash(self.no)

        def __str__(self):
            return 'B{}'.format(self.no)

        def __repr__(self):
            return str(self)


    # for now, let's use QuadBlock as BasicBlock
    BasicBlock = QuadBlock


    def __init__(self):
        # bookkeeping stuff
        self.counter = 0
        self.pred = {}
        self.succ = {}
        self.meta = {}

        self.entry = self.new_block()
        self.exit = self.new_block()

    def set_meta(self, key, val):
        self.meta[key] = val

    def get_meta(self, key, defval=None):
        return self.meta.get(key, defval)

    def get_entry(self):
        return self.entry

    def get_exit(self):
        return self.exit

    def new_block(self, operation=NOOP):
        block = ControlFlowGraph.BasicBlock(self, self.counter, operation)

        # bookkeeping
        self.pred[block] = set()
        self.succ[block] = set()
        self.counter += 1

        return block

    def insert_empty_block(self, src, dst):
        """Insert an empty block along edge src -> dst."""
        assert dst in self.succ[src]
        self.succ[src].remove(dst)
        self.pred[dst].remove(src)

        # use consistent naming
        block_no = '{}-{}'.format(src.no, dst.no)
        block = ControlFlowGraph.BasicBlock(self, block_no, NOOP)
        self.pred[block] = set()
        self.succ[block] = set()

        self.add_edge(src, block)
        self.add_edge(block, dst)

        return block

    def add_edge(self, src, dst):
        assert dst not in self.succ[src]

        self.succ[src].add(dst)
        self.pred[dst].add(src)

    def remove_edge(self, src, dst):
        assert dst in self.succ[src]

        self.succ[src].remove(dst)
        self.pred[dst].remove(src)

    def blocks(self):
        """Return an iterator of all blocks."""
        return self.pred.keys()

    def edges(self):
        """Return an iterator of all edges in the form of (src, dst) tuples."""
        for src, dsts in self.succ.items():
            for dst in dsts:
                yield (src, dst)

    def iterate(self, post_order=True):
        """Iterate over blocks in post order or reverse post order."""
        # TODO: create iterator instances to enable multiple traversal
        #       at the same time
        self.visiting = set()
        self.visited = set()

        if post_order:
            return self.__post_order(self.entry)
        else:
            # I know this is bad. I know...
            return reversed(list(self.__post_order(self.entry)))

    def __post_order(self, block):
        self.visiting.add(block)

        for succ in self.succ[block]:
            if succ in self.visiting or succ in self.visited:
                continue
            yield from self.__post_order(succ)

        yield block

        self.visiting.remove(block)
        self.visited.add(block)


class FlowAnalysis:
    __metaclass__ = ABCMeta
    analyses = set()

    def __init__(self):
        # make sure the new analysis is unique
        # since we are going to use the name as key
        name = self.name()
        assert name not in FlowAnalysis.analyses
        FlowAnalysis.analyses.add(name)

    @abstractmethod
    def name(self):
        """Return a unique name of the analysis."""
        pass

    @abstractmethod
    def is_forward(self):
        """Return True if this analysis is foward."""
        pass

    @abstractmethod
    def boundary_value(self):
        """Return initial value for ENTRY or EXIT."""
        pass

    @abstractmethod
    def initial_value(self):
        """Return initial value for blocks, typically T."""
        pass

    @abstractmethod
    def meet(self, val1, val2):
        """Compute meet of two data flow objects."""
        pass

    @abstractmethod
    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        # TODO: enforce copy in solver
        pass

    def preprocess(self, cfg):
        """Do preprocessing (optional)."""
        pass

    def postprocess(self, cfg):
        """Do postprocessing (optional)."""
        pass


class Solver:
    """Solver for data analysis."""

    @staticmethod
    def run_analysis(analysis, cfg):
        if analysis.is_forward():
            return Solver.__run_forward(analysis, cfg)
        else:
            return Solver.__run_backward(analysis, cfg)

    @staticmethod
    def __run_forward(analysis, cfg):
        A = analysis.name()

        analysis.preprocess(cfg)

        # initialize OUT of each block
        for block in cfg.blocks():
            if block.is_entry():
                block.IN[A] = None
                block.OUT[A] = analysis.boundary_value()
            else:
                block.OUT[A] = analysis.initial_value()

        # iterate until convergence
        changed = True
        while changed:
            changed = False
            # traverse cfg in reverse post order
            for block in cfg.iterate(post_order=False):
                if block.is_entry(): continue

                block.IN[A] = reduce(analysis.meet, (p.OUT[A] for p in block.predecessors()))
                old_OUT = block.OUT[A]
                block.OUT[A] = analysis.transfer(block, block.IN[A])

                if old_OUT != block.OUT[A]:
                    changed = True

        analysis.postprocess(cfg)

    @staticmethod
    def __run_backward(analysis, cfg):
        A = analysis.name()

        analysis.preprocess(cfg)

        # initialize IN of each block
        for block in cfg.blocks():
            if block.is_exit():
                block.IN[A] = analysis.boundary_value()
                block.OUT[A] = None
            else:
                block.IN[A] = analysis.initial_value()

        # iterate until convergence
        changed = True
        while changed:
            changed = False
            # traverse cfg in reverse post order
            for block in cfg.iterate(post_order=True):
                if block.is_exit(): continue

                block.OUT[A] = reduce(analysis.meet, (s.IN[A] for s in block.successors()))
                old_IN = block.IN[A]
                block.IN[A] = analysis.transfer(block, block.OUT[A])

                if old_IN != block.IN[A]:
                    changed = True

        analysis.postprocess(cfg)


# example analyses
class ReachingDefinition(FlowAnalysis):

    def __init__(self):
        super().__init__()

    def name(self):
        return 'Reaching-Definition'

    def is_forward(self):
        return True

    def boundary_value(self):
        return set()

    def initial_value(self):
        return set()

    def meet(self, val1, val2):
        """Meet is union of two sets."""
        return val1 | val2

    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        result = set(val)

        defined_vars = block.defined_variables()
        # process only if this block defines some variable
        if len(defined_vars) > 0:
            for var in defined_vars:
                result -= self.defs[var]

            result.add(block)

        return result

    def preprocess(self, cfg):
        """Gather definitions for each variable."""
        defs = defaultdict(set) # var -> set[block]
        for block in cfg.blocks():
            for var in block.defined_variables():
                defs[var].add(block)

        self.defs = dict(defs)


class Liveness(FlowAnalysis):

    def __init__(self):
        super().__init__()

    def name(self):
        return 'Liveness'

    def is_forward(self):
        return False

    def boundary_value(self):
        return set()

    def initial_value(self):
        return set()

    def meet(self, val1, val2):
        """Meet is union of two sets."""
        return val1 | val2

    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        result = set(val)

        # f(x) = uses U (x - defs)
        result.difference_update(block.defined_variables())
        result.update(block.used_variables())

        return result


ALL_EXPRS = 'All-Expression-Set'

ANALYSIS_ANTICIPATED_EXPR = 'Anticipated-Expressions'
class AnticipatedExpressions(FlowAnalysis):

    def name(self):
        return ANALYSIS_ANTICIPATED_EXPR

    def is_forward(self):
        return False

    def boundary_value(self):
        return set()

    def initial_value(self):
        # see preprocess()
        return self.cfg.get_meta(ALL_EXPRS)

    def meet(self, val1, val2):
        """Meet is intersection of two sets."""
        return val1 & val2

    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        result = set(val)

        # f(x) = use U (x - kill)
        result.difference_update(block.PRE_KILL)
        result.update(block.PRE_USE)

        return result

    def preprocess(self, cfg):
        # save for use later
        self.cfg = cfg

        # find edges whose target has more than one predecessors
        # NOTE: don't insert on the fly to avoid edit-on-iteration
        critical_edges = []
        for src, dst in cfg.edges():
            if len(dst.predecessors()) > 1:
                critical_edges.append((src, dst))

        # insert empty block on such edges
        for src, dst in critical_edges:
            cfg.insert_empty_block(src, dst)

        # collect all partial expressions along with the associated variables
        # also set USE for each block by the way
        # TODO: don't inject properties (PRE_USE, PRE_KILL, etc) to blocks
        partial_exprs = set()
        var_expr_map = defaultdict(set)
        for block in cfg.blocks():
            # consider only arithmetic expression on RHS of assignment
            if not isinstance(block.op, Assign):
                block.PRE_USE = set()
                continue

            assignment = block.op
            expr = assignment.expr

            if not isinstance(expr, Arithmetic):
                block.PRE_USE = set()
                continue

            expr_str = str(expr)
            partial_exprs.add(expr_str)
            for used_var in expr.get_variables():
                var_expr_map[used_var].add(expr_str)

            block.PRE_USE = set([expr_str])

        # set universal set of partial expressions
        cfg.set_meta(ALL_EXPRS, partial_exprs)

        # set KILL for each block
        for block in cfg.blocks():
            if not isinstance(block.op, Assign):
                block.PRE_KILL = set()
                continue

            kill_set = set()
            assignment = block.op
            for var in assignment.var.get_variables():
                kill_set.update(var_expr_map[var])

            block.PRE_KILL = kill_set

    def postprocess(self, cfg):
        print('\nAfter Anticipated Expressions:')
        name = self.name()
        for block in cfg.iterate(post_order=False):
            print('B{}.IN  = {}'.format(block.no, block.IN[name]))
            print('B{}.OUT = {}'.format(block.no, block.OUT[name]))


ANALYSIS_AVAILABLE_EXPR = 'Available-Expressions'
class AvailableExpressions(FlowAnalysis):

    def name(self):
        return ANALYSIS_AVAILABLE_EXPR

    def is_forward(self):
        return True

    def boundary_value(self):
        return set()

    def initial_value(self):
        return self.cfg.get_meta(ALL_EXPRS)

    def meet(self, val1, val2):
        """Meet is intersection of two sets."""
        return val1 & val2

    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        result = set(val)

        # f(x) = (anticipated[B].in U x) - kill
        result.update(block.IN[ANALYSIS_ANTICIPATED_EXPR])
        result.difference_update(block.PRE_KILL)

        return result

    def preprocess(self, cfg):
        self.cfg = cfg

    def postprocess(self, cfg):
        print('\nAfter Available Expressions:')
        name = self.name()
        for block in cfg.iterate(post_order=False):
            print('B{}.IN  = {}'.format(block.no, block.IN[name]))
            print('B{}.OUT = {}'.format(block.no, block.OUT[name]))

        # compute earliest
        for block in cfg.iterate(post_order=False):
            # skip entry because available[ENTRY].in is not defined
            if not block.is_entry():
                anticipated_in = block.IN[ANALYSIS_ANTICIPATED_EXPR]
                available_in = block.IN[ANALYSIS_AVAILABLE_EXPR]
                block.PRE_EARLIEST = anticipated_in - available_in
                print('B{}.EARLIEST = {}'.format(block.no, block.PRE_EARLIEST))


ANALYSIS_POSTPONABLE_EXPR = 'Postponable-Expressions'
class PostponableExpressions(FlowAnalysis):

    def name(self):
        return ANALYSIS_POSTPONABLE_EXPR

    def is_forward(self):
        return True

    def boundary_value(self):
        return set()

    def initial_value(self):
        return self.cfg.get_meta(ALL_EXPRS)

    def meet(self, val1, val2):
        """Meet is intersection of two sets."""
        return val1 & val2

    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        result = set(val)

        # f(x) = (earliest[B] U x) - use
        result.update(block.PRE_EARLIEST)
        result.difference_update(block.PRE_USE)

        return result

    def preprocess(self, cfg):
        self.cfg = cfg

    def postprocess(self, cfg):
        print('\nAfter Postponable Expressions:')
        name = self.name()
        for block in cfg.iterate(post_order=False):
            print('B{}.IN  = {}'.format(block.no, block.IN[name]))
            print('B{}.OUT = {}'.format(block.no, block.OUT[name]))

        # compute latest
        def helper(block):
            """Compute rearliest or postponable."""
            earliest = block.PRE_EARLIEST
            postponable_in = block.IN[ANALYSIS_POSTPONABLE_EXPR]
            return earliest | postponable_in

        U = self.cfg.get_meta(ALL_EXPRS)
        def complement(S):
            """Compute U-S."""
            return U - S

        for block in cfg.iterate(post_order=False):
            # handle ENTRY with care since earliest is not defined
            # (it actually doesn't matter what the entry.latest is)
            if block.is_entry():
                block.PRE_LATEST = set()
                continue

            succ_vals = [helper(succ) for succ in block.successors()]
            temp = set()
            if len(succ_vals) > 0:
                temp = complement(reduce(self.meet, succ_vals))
            block.PRE_LATEST = helper(block) & (block.PRE_USE | temp)
            print('B{}.LATEST = {}'.format(block.no, block.PRE_LATEST))


ANALYSIS_USED_EXPR = 'Used-Expressions'
class UsedExpressions(FlowAnalysis):

    def name(self):
        return ANALYSIS_USED_EXPR

    def is_forward(self):
        return False

    def boundary_value(self):
        return set()

    def initial_value(self):
        return set()

    def meet(self, val1, val2):
        """Meet is union of two sets."""
        return val1 | val2

    def transfer(self, block, val):
        """Apply transfer function on block. Must NOT alter val."""
        result = set(val)

        # f(x) = (use U x) - latest[B]
        result.update(block.PRE_USE)
        result.difference_update(block.PRE_LATEST)

        return result

    def postprocess(self, cfg):
        print('\nAfter Used Expressions:')
        name = self.name()
        for block in cfg.iterate(post_order=False):
            print('B{}.IN  = {}'.format(block.no, block.IN[name]))
            print('B{}.OUT = {}'.format(block.no, block.OUT[name]))


def eliminate_partial_redundancy(cfg, *, debug=False):
    # step 0: preprocess: add necessary empty blocks and determine use and kill
    # step 1: run anticipated expressions analysis
    ant = AnticipatedExpressions()
    Solver.run_analysis(ant, cfg)

    # step 2: run available expressions analysis and compute earliest
    avail = AvailableExpressions()
    Solver.run_analysis(avail, cfg)

    # step 3: run postponable expressions analysis and compute latest
    post = PostponableExpressions()
    Solver.run_analysis(post, cfg)

    # step 4: run used expressions analysis
    used = UsedExpressions()
    Solver.run_analysis(used, cfg)

    # step 5: postprocess: replace redundant partial expressions with
    #         newly created temporary variables
    # TODO
