from abc import ABCMeta, abstractmethod
from functools import reduce

class ControlFlowGraph:
    """It is the user's duty to ensure all nodes must be reachable from entry."""

    class BasicBlock:
        def __init__(self, cfg, no):
            self.cfg = cfg
            self.no = no

        def is_entry(self):
            return self == self.cfg.entry

        def is_exit(self):
            return self == self.cfg.exit

        def predecessors(self):
            return self.cfg.pred[self]

        def successors(self):
            return self.cfg.succ[self]

        def __eq__(self, other):
            return self.cfg == other.cfg and self.no == other.no

        def __hash__(self):
            return hash(self.no)


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

    def new_block(self):
        block = BasicBlock(self, self.counter)

        # bookkeeping
        self.pred[block] = set()
        self.succ[block] = set()
        self.counter += 1

        return block

    def add_edge(self, src, dst):
        self.succ[src].add(dst)
        self.pred[dst].add(src)

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
        analysis.preprocess(cfg)

        # initialize OUT
        OUT = {}
        for block in cfg.blocks():
            if block.is_entry():
                OUT[block] = analysis.boundary_value()
            else:
                OUT[block] = analysis.initial_value()

        # iterate until convergence
        changed = True
        while changed:
            changed = False
            # traverse cfg in reverse post order
            for block in cfg.iterate(post_order=False):
                if block.is_entry(): continue

                IN = reduce(analysis.meet, OUT[p] for p in block.predecessors())
                old_OUT = OUT[B]
                OUT[block] = analysis.transfer(block, IN)

                if old_OUT != OUT[block]:
                    changed = True

        analysis.postprocess(cfg)
