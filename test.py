import itertools

def vpternlog(x0, x1, x2, imm):
    #idx = x0 + 2 * x1 + 4 * x2
    idx = 4 * x2 + 2 * x1 + x0
    idx = 7 - idx
    return (imm >> idx) & 1

def ham4(x0, x1, x2, x3):
    t0 = vpternlog(x2, x0, x3, 0x69)
    t1 = vpternlog(t0, x1, x0, 0xc3)
    t2 = vpternlog(x0, x2, x3, 0x81)
    t3 = vpternlog(x3, x1, t2, 0x80)
    t4 = vpternlog(x1, t1, t2, 0x59)
    return t1, t4, t3


for bits in itertools.product([0, 1], repeat=4):
    print(ham4(*bits), bits)
