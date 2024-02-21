import itertools

def vpternlog(x0, x1, x2, imm):
    idx = 4 * x0 + 2 * x1 + x2
    return (imm >> idx) & 1

def ham4(x0, x1, x2, x3):
    t0 = vpternlog(x3, x1, x2, 0x69)
    t1 = vpternlog(x1, t0, x0, 0xe2)
    t2 = vpternlog(x2, t1, x3, 0x80)
    t3 = vpternlog(t2, t0, x0, 0x09)
    t4 = vpternlog(x3, t1, x2, 0x6c)
    return 1*t3 + 2*t4 + 4*t2

for bits in itertools.product([0, 1], repeat=4):
    print(ham4(*bits), bits, ham4(*bits) == sum(bits))
