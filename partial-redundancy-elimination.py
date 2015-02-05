from liu import *

# construct CFG
cfg = ControlFlowGraph()

# entry and exit are at index 0 and 1
blocks = [cfg.get_entry(), cfg.get_exit()]
for i in range(2, 13):
    blocks.append(cfg.new_block())

# set operations at certain nodes
blocks[6].set_operation(Assign(Var('a'), Add(Var('x'), Var('y'))))
blocks[9].set_operation(Assign(Var('x'), FunctionCall('input')))
blocks[10].set_operation(Assign(Var('b'), Add(Var('x'), Var('y'))))
blocks[11].set_operation(Assign(Var('c'), Add(Var('x'), Var('y'))))
blocks[12].set_operation(Assign(Var('y'), FunctionCall('input')))

edges = [
    (0, 2),
    (2, 3), (2, 4),
    (3, 5),
    (4, 6), (4, 7),
    (5, 8),
    (6, 8), (6, 9),
    (7, 11),
    (8, 10),
    (9, 10), (9, 1),
    (10, 1), (10, 3),
    (11, 1), (11, 12),
    (12, 7),
]

for src, dst in edges:
    cfg.add_edge(blocks[src], blocks[dst])

eliminate_partial_redundancy(cfg, debug=True)
