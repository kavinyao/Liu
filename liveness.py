from liu import *

# construct CFG
cfg = ControlFlowGraph()
n2 = cfg.new_block(Assign(Var('i'), Subtract(Var('m'), Const('1'))))
n3 = cfg.new_block(Assign(Var('j'), Var('n')))
n4 = cfg.new_block(Assign(Var('a'), Var('u1')))
n5 = cfg.new_block(Assign(Var('i'), Add(Var('i'), Const('1'))))
n6 = cfg.new_block(Assign(Var('j'), Subtract(Var('j'), Const('1'))))
n7 = cfg.new_block(Assign(Var('a'), Var('u2')))
n8 = cfg.new_block(Assign(Var('i'), Var('u3')))
cfg.add_edge(cfg.get_entry(), n2)
cfg.add_edge(n2, n3)
cfg.add_edge(n3, n4)
cfg.add_edge(n4, n5)
cfg.add_edge(n5, n6)
cfg.add_edge(n6, n7)
cfg.add_edge(n6, n8)
cfg.add_edge(n7, n8)
cfg.add_edge(n8, n5)
cfg.add_edge(n8, cfg.get_exit())

# solve reaching definitions
liveness = Liveness()
Solver.run_analysis(liveness, cfg)

LV = liveness.name()
for block in cfg.iterate(post_order=False):
    print('B{}.IN  = {}'.format(block.no, block.IN[LV]))
    print('B{}.OUT = {}'.format(block.no, block.OUT[LV]))

