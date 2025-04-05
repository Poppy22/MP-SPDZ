from .comparison import *
from .floatingpoint import *
from .types import *
from . import comparison, program

class NonLinear:
    def mod2m(self, a, k, m, signed):
        """
        a_prime = a % 2^m

        k: bit length of a
        m: compile-time integer
        signed: True/False, describes a
        """
        if not util.is_constant(m):
            raise CompilerError('m must be a public constant')
        if m >= k:
            return a
        else:
            return self._mod2m(a, k, m, signed)

    def trunc_pr(self, a, k, m, signed=True):
        if isinstance(a, types.cint):
            return shift_two(a, m)
        prog = program.Program.prog
        if prog.use_trunc_pr:
            if not prog.options.ring:
                prog.curr_tape.require_bit_length(k + prog.security)
            if signed and prog.use_trunc_pr != -1:
                a += (1 << (k - 1))
            res = sint()
            trunc_pr(res, a, k, m)
            if signed and prog.use_trunc_pr != -1:
                res -= (1 << (k - m - 1))
            return res
        return self._trunc_pr(a, k, m, signed)

    def trunc_round_nearest(self, a, k, m, signed):
        res = sint()
        comparison.Trunc(res, a + (1 << (m - 1)), k + 1, m, signed)
        return res

    def trunc(self, a, k, m, signed):
        if m == 0:
            return a
        return self._trunc(a, k, m, signed)
    
    # R: clear-text; x: edabit in binary format
    def LTBits(self, R, x, r, BIT_SIZE):
        R_bits = cint.bit_decompose(R, BIT_SIZE)
        library.print_ln("\nLTBits: R_bits= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", R_bits[i])

        library.print_ln("\nLTBits from bits: x = ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", x[i].reveal())

        y = [x[i].bit_xor(R_bits[i]) for i in range(BIT_SIZE)]
        library.print_ln("\nLTBits: y_bits= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", y[i].reveal())

        z = floatingpoint.PreOpL(floatingpoint.or_op, y[::-1])[::-1] + [0]
        library.print_ln("\nLTBits: z= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", z[i].reveal())

        w = [z[i] - z[i + 1] for i in range(BIT_SIZE)]
        library.print_ln("\nLTBits: w= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", w[i].reveal())
        
        s = sum((R_bits[i] & w[i]) for i in range(BIT_SIZE))
        library.print_ln("\nend of LTB rabbit Sum=%s; returning 1 - sum: %s; and with types.sintbit = %s", s.reveal(), (1 - s).reveal(), (types.sintbit(1) - types.sintbit(s)).reveal())
        return types.sintbit(1) - types.sintbit(sum((R_bits[i] & w[i]) for i in range(BIT_SIZE)))
    
    def rabbitLTZField(self, x, BIT_SIZE = 64):
        """
        s = (c ?< a)

        BIT_SIZE: bit length of a
        """
        length_eda = BIT_SIZE
        M = 18446744073709551557
        R = (M - 1) // 2

        r, r_bits = sint.get_edabit(length_eda, True)
        masked_a = (x + r).reveal()
        masked_b = (x + r + M - R).reveal() # masked_a + 1
        w = [None, None, None, None]

        w[1] = self.LTBits(masked_a, r_bits, r, BIT_SIZE)
        library.print_ln("w1, comparing: masked_a=%s edabit=%s w1=%s", masked_a, r.reveal(), w[1].reveal())

        w[2] = self.LTBits(masked_b, r_bits, r, BIT_SIZE)
        library.print_ln("w2, comparing: masked_b=%s edabit=%s w2=%s", masked_b, r.reveal(), w[2].reveal())

        w[3] = cint(masked_b < 0)
        library.print_ln("w3, comparing: masked_b=%s with %s, w3=%s", masked_b, M - R, w[3].reveal())

        result = w[1] - w[2] + w[3]
        library.print_ln("end of ltz ring: result = %s and 1- result=%s", result.reveal(), (1-result).reveal())
        return sint(1 - result)

    # def rabbitLTS_fix(self, a, b):
    #     return 1 - self.rabbitLTS(b, a)
    
    # def rabbitLTS(self, a, b):
    #     res = self.rabbitLTZ(a - b)
    #     return res

    def ltz(self, a, k):
        library.print_ln("Line 87: a=%s k=%s", a.reveal(), k)
        prog = program.Program.prog
        if prog.options.comparison_rabbit:
            library.print_ln("Line 90: calling rabbitLTZ from field")
            return self.rabbitLTZField(a)
        
        # else, use truncation
        return -self.trunc(a, k, k - 1, True)

class Masking(NonLinear):
    def eqz(self, a, k):
        c, r = self._mask(a, k)
        d = [None]*k
        for i,b in enumerate(r[0].bit_decompose_clear(c, k)):
            d[i] = r[i].bit_xor(b)
        return 1 - types.sintbit.conv(self.kor(d))

class Prime(Masking):
    """ Non-linear functionality modulo a prime with statistical masking. """
    def _mod2m(self, a, k, m, signed):
        res = sint()
        if m == 1:
            Mod2(res, a, k, signed)
        else:
            Mod2mField(res, a, k, m, signed)
        return res

    def _mask(self, a, k):
        return maskField(a, k)

    def _trunc_pr(self, a, k, m, signed=None):
        return TruncPrField(a, k, m)

    def _trunc(self, a, k, m, signed=None):
        a_prime = self.mod2m(a, k, m, signed)
        tmp = cint()
        inv2m(tmp, m)
        return (a - a_prime) * tmp

    def bit_dec(self, a, k, m, maybe_mixed=False):
        if maybe_mixed:
            return BitDecFieldRaw(a, k, m)
        else:
            return BitDecField(a, k, m)

    def kor(self, d):
        return KOR(d)

class KnownPrime(NonLinear):
    """ Non-linear functionality modulo a prime known at compile time. """
    def __init__(self, prime):
        self.prime = prime

    def _mod2m(self, a, k, m, signed):
        if signed:
            a += cint(1) << (k - 1)
        return sint.bit_compose(self.bit_dec(a, k, m, True))

    def _trunc_pr(self, a, k, m, signed):
        # nearest truncation
        return self.trunc_round_nearest(a, k, m, signed)

    def _trunc(self, a, k, m, signed=None):
        return TruncZeros(a - self._mod2m(a, k, m, signed), k, m, signed)

    def trunc_round_nearest(self, a, k, m, signed):
        a += cint(1) << (m - 1)
        if signed:
            a += cint(1) << (k - 1)
            k += 1
        res = self._trunc(a, k, m, False)
        if signed:
            res -= cint(1) << (k - m - 2)
        return res

    def bit_dec(self, a, k, m, maybe_mixed=False):
        assert k < self.prime.bit_length()
        bits = BitDecFull(a, m, maybe_mixed=maybe_mixed)
        assert len(bits) == m
        return bits

    def eqz(self, a, k):
        # always signed
        a += two_power(k)
        return 1 - types.sintbit.conv(KORL(self.bit_dec(a, k, k, True)))

    def ltz(self, a, k):
        prog = program.Program.prog
        if prog.options.comparison_rabbit:
            return -20
        
        if k + 1 < self.prime.bit_length():
            # https://dl.acm.org/doi/10.1145/3474123.3486757
            # "negative" values wrap around when doubling, thus becoming odd
            return self.mod2m(2 * a, k + 1, 1, False)
        else:
            return super(KnownPrime, self).ltz(a, k)

class Ring(Masking):
    """ Non-linear functionality modulo a power of two known at compile time.
    """
    def __init__(self, ring_size):
        self.ring_size = ring_size

    def _mod2m(self, a, k, m, signed):
        res = sint()
        Mod2mRing(res, a, k, m, signed)
        return res

    def _mask(self, a, k):
        return maskRing(a, k)

    def _trunc_pr(self, a, k, m, signed):
        return TruncPrRing(a, k, m, signed=signed)

    def _trunc(self, a, k, m, signed=None):
        return comparison.TruncRing(None, a, k, m, signed=signed)

    def bit_dec(self, a, k, m, maybe_mixed=False):
        if maybe_mixed:
            return BitDecRingRaw(a, k, m)
        else:
            return BitDecRing(a, k, m)

    def kor(self, d):
        return KORL(d)

    def trunc_round_nearest(self, a, k, m, signed):
        if k == self.ring_size:
            # cannot work with bit length k+1
            tmp = TruncRing(None, a, k, m - 1, signed)
            return TruncRing(None, tmp + 1, k - m + 1, 1, signed)
        else:
            return super(Ring, self).trunc_round_nearest(a, k, m, signed)

    # R: clear-text; x: edabit in binary format
    def LTBits(self, R, x, r, BIT_SIZE):
        R_bits = cint.bit_decompose(R, BIT_SIZE)
        library.print_ln("\nLTBits: R_bits= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", R_bits[i])

        library.print_ln("\nLTBits from bits: x = ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", x[i].reveal())

        y = [x[i].bit_xor(R_bits[i]) for i in range(BIT_SIZE)]
        library.print_ln("\nLTBits: y_bits= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", y[i].reveal())

        z = floatingpoint.PreOpL(floatingpoint.or_op, y[::-1])[::-1] + [0]
        library.print_ln("\nLTBits: z= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", z[i].reveal())

        w = [z[i] - z[i + 1] for i in range(BIT_SIZE)]
        library.print_ln("\nLTBits: w= ")
        for i in range(BIT_SIZE):
            library.print_without_ln("%s", w[i].reveal())
        
        s = sum((R_bits[i] & w[i]) for i in range(BIT_SIZE))
        library.print_ln("\nend of LTB rabbit Sum=%s; returning 1 - sum: %s; and with types.sintbit = %s", s.reveal(), (1 - s).reveal(), (types.sintbit(1) - types.sintbit(s)).reveal())
        return types.sintbit(1) - types.sintbit(sum((R_bits[i] & w[i]) for i in range(BIT_SIZE)))
    
    def rabbitLTZRing(self, x, BIT_SIZE = 64):
        """
        s = (c ?< a)

        BIT_SIZE: bit length of a
        """
        length_eda = BIT_SIZE
        M = P_VALUES[64]
        R = 0 # for ring

        r, r_bits = sint.get_edabit(length_eda, True)
        masked_a = (x + r).reveal()
        masked_b = (x + r + M - R).reveal() # masked_a + 1
        w = [None, None, None, None]

        w[1] = self.LTBits(masked_a, r_bits, r, BIT_SIZE)
        library.print_ln("w1, comparing: masked_a=%s edabit=%s w1=%s", masked_a, r.reveal(), w[1].reveal())

        w[2] = self.LTBits(masked_b, r_bits, r, BIT_SIZE)
        library.print_ln("w2, comparing: masked_b=%s edabit=%s w2=%s", masked_b, r.reveal(), w[2].reveal())

        w[3] = cint(masked_b < 0)
        library.print_ln("w3, comparing: masked_b=%s with %s, w3=%s", masked_b, M - R, w[3].reveal())

        result = w[1] - w[2] + w[3]
        library.print_ln("end of ltz ring: result = %s and 1- result=%s", result.reveal(), (1-result).reveal())
        return sint(1 - result)
    
    def ltz(self, a, k):
        library.print_ln("Line 223: a=%s k=%s", a.reveal(), k)
        prog = program.Program.prog
        if prog.options.comparison_rabbit:
            library.print_ln("Line 226: calling rabbitLTZ from ring")
            return self.rabbitLTZRing(a)
        else:
            return LtzRing(a, k)
