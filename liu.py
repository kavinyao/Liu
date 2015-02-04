from abc import ABCMeta, abstractmethod
from collections import defaultdict
from functools import reduce

class ControlFlowGraph:
    """It is the user's duty to ensure all nodes must be reachable from entry."""

    class QuadBlock:
        """A simple block with only 1 statement."""
        def __init__(self, cfg, no, operation=Noop):
            self.cfg = cfg
            self.no = no
            self.op = operation

            # record IN and OUT for different analyses
            # the key is name of an analysis
            self.IN = {}
            self.OUT = {}

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


    # for now, let's use QuadBlock as BasicBlock
    BasicBlock = QuadBlock


    def __init__(self):
        # bookkeeping stuff
        self.counter = 0
        self.pred = {}
        self.succ = {}

        self.entry = self.new_block()
        self.exit = self.new_block()

    def entry(self):
        return self.entry

    def exit(self):
        return self.exit

    def new_block(self, operation=Noop):
        block = BasicBlock(self, self.counter, operation)

        # bookkeeping
        self.pred[block] = set()
        self.succ[block] = set()
        self.counter += 1

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

    def iterate(self, post_order=True):
        """Iterate over blocks in post order or reverse post order."""
        if post_order:
            return self.__post_order(self.entry)
        else:
            # I know this is bad. I know...
            return reversed(list(self.__post_order(self.entry)))

    def __post_order(self, block):
        for succ in self.succ[block]:
            if succ is visited:
                continue
            self.__post_order(succ)

        yield block


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
            return __run_forward(analysis, cfg)
        else:
            return __run_backward(analysis, cfg)

    @staticmethod
    def __run_forward(analysis, cfg):
        A = analysis.name()

        analysis.preprocess(cfg)

        # initialize OUT of each block
        for block in cfg.blocks():
            if block.is_entry():
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

                block.IN[A] = reduce(analysis.meet, p.OUT[A] for p in block.predecessors())
                old_OUT = B.OUT[A]
                block.OUT = analysis.transfer(block, block.IN[A])

                if old_OUT != block.OUT[A]:
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
        result = val

        defined_vars = block.defined_vars()
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

        self.defs = defs

    def postprocess(self, cfg):
        """Do postprocessing (optional)."""
        pass

# example usage
if __name__ == '__main__':
    # construct CFG
    cfg = ControlFlowGraph()
    n2 = cfg.new_block(Assign(Var('i'), Subtract(Var('m'), Const('1'))))
    n3 = cfg.new_block(Assign(Var('j'), Var('n')))
    n4 = cfg.new_block(Assign(Var('a'), Var('u1')))
    n5 = cfg.new_block(Assign(Var('i'), Add(Var('i'), Const('1'))))
    n6 = cfg.new_block(Assign(Var('j'), Subtract(Var('j'), Const('1'))))
    n7 = cfg.new_block(Assign(Var('a'), Var('u2')))
    n8 = cfg.new_block(Assign(Var('u'), Var('u3')))
    cfg.add_edge(cfg.entry(), n2)
    cfg.add_edge(n2, n3)
    cfg.add_edge(n3, n4)
    cfg.add_edge(n4, n5)
    cfg.add_edge(n5, n6)
    cfg.add_edge(n6, n7)
    cfg.add_edge(n6, n8)
    cfg.add_edge(n7, n8)
    cfg.add_edge(n8, n5)
    cfg.add_edge(n8, cfg.exit())

    # solve reaching definitions
    reach_def = ReachingDefinition()
    Solver.solve(reach_def, cfg)

    RD = reach_def.name()
    for block in cfg.iterate(post_order=False):
        print('B{}.in = {}'.format(block.no, block.IN[RD]))
        print('B{}.out = {}'.format(block.no, block.OUT[RD]))
