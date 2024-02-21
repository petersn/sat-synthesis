import itertools

def vpternlog(x0, x1, x2, imm):
    idx = 4 * x0 + 2 * x1 + x2
    return (imm >> idx) & 1

def ham4(x0, x1, x2, x3):
    t0 = vpternlog(x3, x2, x1, 0x3c)
    t1 = vpternlog(x3, x2, x1, 0x7e)
    t2 = vpternlog(x0, t0, x1, 0x96)
    t3 = vpternlog(t1, t2, x0, 0xb4)
    t4 = vpternlog(x3, t2, t1, 0x10)
    return t2 + 2 * t3 + 4 * t4

for bits in itertools.product([0, 1], repeat=4):
    print(ham4(*bits), bits, ham4(*bits) == sum(bits))
