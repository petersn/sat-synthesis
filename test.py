import itertools

# def vpternlog(x0, x1, x2, imm):
#     idx = 4 * x0 + 2 * x1 + x2
#     return (imm >> idx) & 1

# def ham4(x0, x1, x2, x3):
#     t0 = vpternlog(x3, x1, x2, 0x69)
#     t1 = vpternlog(x1, t0, x0, 0xe2)
#     t2 = vpternlog(x2, t1, x3, 0x80)
#     t3 = vpternlog(t2, t0, x0, 0x09)
#     t4 = vpternlog(x3, t1, x2, 0x6c)
#     return 1*t3 + 2*t4 + 4*t2

# for bits in itertools.product([0, 1], repeat=4):
#     print(ham4(*bits), bits, ham4(*bits) == sum(bits))


def f(x0, x1, x2, x3):
    t0 = not (1 and x0)
    t1 = not (t0 and x3)
    t2 = not (t0 and t1)
    t3 = not (1 and t2)
    t4 = not (x2 and t1)
    t5 = not (t3 and x1)
    t6 = not (t5 and t3)
    t7 = not (t6 and 1)
    t8 = not (t4 and t7)
    t9 = not (1 and t8)
    return t9

LUT4 = 0x0001

def lut(bits):
    index = 8 * bits[3] + 4 * bits[2] + 2 * bits[1] + bits[0]
    return (LUT4 >> index) & 1

for bits in itertools.product([0, 1], repeat=4):
    print(f(*bits), bits, f(*bits) == lut(bits))
