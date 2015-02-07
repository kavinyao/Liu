from liu import *

# construct CFG
cfg = ControlFlowGraph()

# entry and exit are at index 0 and 1
blocks = [cfg.get_entry(), cfg.get_exit()]
for i in range(2, 12):
    blocks.append(cfg.new_block())

# set operations at certain nodes
blocks[2].set_operation(Assign(Var('r'), Const('2')))
blocks[3].set_operation(Assign(Var('p'), Add(Var('q'), Const('2'))))
blocks[5].set_operation(Assign(Var('x'), Add(Var('q'), Const('2'))))
blocks[6].set_operation(Assign(Var('z'), Add(Var('a'), Var('x'))))
blocks[7].set_operation(Assign(Var('x'), FunctionCall('input')))
blocks[8].set_operation(Assign(Var('y'), Add(Var('q'), Const('2'))))
blocks[9].set_operation(Assign(Var('m'), Add(Var('a'), Var('y'))))
blocks[10].set_operation(Assign(Var('w'), Add(Var('a'), Var('x'))))
blocks[11].set_operation(Assign(Var('r'), FunctionCall('input')))

edges = [
    (0, 2),
    (2, 3), (2, 4),
    (3, 5),
    (4, 5),
    (5, 6), (5, 7),
    (6, 8),
    (7, 9),
    (8, 9),
    (9, 10), (9, 7),
    (10, 11),
    (11, 1), (11, 2),
]

for src, dst in edges:
    cfg.add_edge(blocks[src], blocks[dst])

eliminate_partial_redundancy(cfg, debug=True)
