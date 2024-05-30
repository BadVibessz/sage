# sage.doctest: needs sage.combinat
r"""
<McEliece cryptosystem based on Goppa codes>

<Paragraph description>

EXAMPLES::

<Lots and lots of examples>

AUTHORS:

- Danila Tsymbal (2024-05-09): initial version // TODO:

- person (date in ISO year-month-day format): short desc

"""

# ****************************************************************************
#       Copyright (C) 2024 Danila Tsymbal <danila.tsymbal@mail.ru>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.crypto.cryptosystem import PublicKeyCryptosystem
from sage.coding.all import codes

# todo: bad?
from sage.rings.finite_rings.all import *
from sage.matrix.all import (matrix, random_matrix)
from sage.combinat.permutation import Permutations
from sage.modules.free_module_element import vector
from sage.arith.misc import xgcd
from sage.misc.functional import sqrt # todo: import these inside concrete func?
from sage.functions.other import floor
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

import random

# TODO: doc!!

def _random_binary_unimodular_matrix(rows, cols):
    r"""
    Generate random binary non-singular matrix.
    """
    return random_matrix(GF(2), rows, cols, algorithm='unimodular')


def _random_permutation_matrix(n):
    return matrix(GF(2), Permutations(n).random_element().to_matrix())


def _random_binary_err_vector(length, weight_bound):
    list = [0] * length

    weight = 0
    for i in range(length):
        if weight == weight_bound:
            break

        rand_elem = random.randint(0, 1)

        list[i] = rand_elem
        weight = weight + rand_elem

    return vector(GF(2), list)


def _split(p):
    # split polynomial p over F into even part po
    # and odd part p1 such that p(z) = p2 (z) + z p2 (z)
    Phi = p.parent()
    p0 = Phi([sqrt(c) for c in p.list()[0::2]])
    p1 = Phi([sqrt(c) for c in p.list()[1::2]])
    return (p0,p1)

def _partial_xgcd(a, b, R, bound):  # todo: understand stop crit!!!
    s = R.one()
    prev_s = R.zero()

    r = a
    prev_r = b

    while not (prev_r.degree() > floor(bound) / 2 and r.degree() == floor(bound / 2)):
        q = prev_r.quo_rem(r)[0]

        (prev_r, r) = (r, prev_r - q * r)
        (prev_s, s) = (s, prev_s - q * s)

    return (r, s)

def _get_errors(R, L, s, g):
    r"""
    Get error vector by received message using Patterson algorithm
    // todo
    """
    x = g.parent().gen()
    n = len(L)

    h = _inverse_by_mod(s, g)

    if h == x:
        return vector(GF(2), [0] * n)

    # take the necessary square root

    # d = ((h + x)^(2^(m*g.degree() - 1))).mod(g)

    (g0, g1) = _split(g)
    sqrt_X = g0 * _inverse_by_mod(g1, g)

    (T0, T1) = _split(h + x)
    d = (T0 + sqrt_X * T1).mod(g)

    (a, b) = _partial_xgcd(R(d.list()), R(g.list()), R, g.degree())

    # error-locating polynomial
    sigma = a * a + x * b * b

    # find locations in which errors occurred
    err_locations = []

    for i in range(n):
        if sigma(L[i]) == 0:
            err_locations.append(i)

    err_invert = [0] * n
    for err_pos in err_locations:
        err_invert[err_pos] = 1

    return vector(GF(2), err_invert)


def _inverse_by_mod(poly, mod):
    r"""
    Inverse polynomial by modulus using extended Euclidean algorithm

    INPUT:

    - ``poly`` -- polynomial to inverse
    - ``mod`` -- polynomial that is modulus

    OUTPUT:

    - polynomial `f` that satisfies poly(x) * f(x) == 1 mod(mod(x))

    EXAMPLES::

    sage: from sage.crypto.public_key.mceliece import _inverse_by_mod

    sage: F = GF(2^4, 'a');
    sage: R.<x> = F[]
    sage: RR.<a> = F

    sage: f = x^5 + (a^3 + a^2)*x^4 + (a^2 + a + 1)*x^3 + (a^3 + a^2 + 1)*x^2 + (a^3 + a^2 + a)*x + a^3 + a^2 + 1
    sage: g = x^2 + (a^3 + a^2)*x + a^3
    sage: _inverse_by_mod(f, g)
    (a^3 + a^2)*x + a^3 + 1
    """
    return xgcd(poly, mod)[1]

def _random_irreducible_polynomial(R, d):
    r"""
    Generate random irreducible polynomial over R

    INPUT:

    - ``R`` -- ring of polynomial
    - ``d`` -- degree that polynomial should have

    OUTPUT:

    - irreducible polynomial over R

    EXPAMPLES::

    sage: from sage.crypto.public_key.mceliece import _random_irreducible_polynomial

    sage: F = GF(2^4, 'a');
    sage: R.<x> = F[]
    sage: RR.<a> = F

    sage: f = _random_irreducible_polynomial(R, 5); f
    x^5 + (a^3 + a^2)*x^4 + (a^2 + a + 1)*x^3 + (a^3 + a^2 + 1)*x^2 + (a^3 + a^2 + a)*x + a^3 + a^2 + 1

    f.is_irreducible()
    True
    """
    var = R.gen()

    c = 0
    while True: # TODO,  benchmark this! how fast we get irreducible poly
        res = 1*var**d + R.random_element(degree=d-1)
        c = c + 1

        if res.is_irreducible() == True:
            return res

class McEliece(PublicKeyCryptosystem):
    r"""
    // todo:
    """

    def __init__(self, n, k, t):
        """
       Construct the McEliece cryptosystem.

       INPUT:

        - ``n`` -- length of Goppa code.
        - ``k`` -- dimension of Goppa code.
        - ``t`` -- degree of Goppa polynomial.

       OUTPUT:

       - A ``McEliece`` object representing the McEliece cryptosystem.

       See the class docstring of ``McEliece`` for detailed
       documentation.

       EXAMPLES::
       // TODO: ??
       """

        # we know that k >= n - mt > 0, thus (n - k) / t <= m < n / t
        # also m must satisfy n - mt >= k, as our Goppa code will have k' = n - mt dimension
        # and this k' must be greater or equals provided `k` parameter 
        # TODO: some validation for n, k, t

        if n <= 0 or k <= 0 or t <= 0:
            raise Exception("Parameters should be positive.")

        if k >= n:
            raise Exception("K should be less than n.")

        m = floor((n - k) / t)
        q = 2**m

        # make sure that field contains at least `n` elements
        while q < n:
            m = m + 1
            q = 2**m

        if n - m*t <= 0 or n - m*t < k:
            raise Exception("Invalid parameters") # TODO: read about exceptions in sage dev guide


        # public parameters
        self.n = n
        self.k = k
        self.t = t

        F = GF(q)

        self.R = PolynomialRing(F, 'x')

        self.g = _random_irreducible_polynomial(self.R, t)
        self.L = [a for a in random.sample(F.list(), n) if self.g(a) != 0]

        self.C = codes.GoppaCode(self.g, self.L)

        # remove (dim - k) last rows of C.generator_matrix() to accept messages of length `k`
        dim = self.C.dimension()
        
        if k == dim:
            self.G = self.C.generator_matrix()
        else: 
            self.G = self.C.generator_matrix().delete_rows([i for i in range(k, dim)])
        
        r = len(self.G.rows())
        c = len(self.G.columns())

        self.S = _random_binary_unimodular_matrix(r, r)
        self.P = _random_permutation_matrix(c)

        self.GG = self.S * self.G * self.P

        # public key: (S * G * P, t)
        # private key: (g, G, S, P)

    def __eq__(self, other):
        """
        Compare this ``McEliece`` object with ``other``.

        INPUT:

        - ``other`` -- a  object.

        OUTPUT:

        - ``True`` if both ``self`` and ``other`` are ``McEliece``
          objects are equal. ``False`` otherwise.

        Two ``McEliece`` objects are equal if their string
        representations are the same.

        EXAMPLES::

        sage: from sage.crypto.public_key.mceliece import McEliece
        sage: mc1 = McEliece(16, 8, 2)
        sage: mc2 = McEliece(32, 12, 4)
        sage: mc1 == mc2
       
        False


        sage: from sage.crypto.public_key.mceliece import McEliece
        sage: mc = McEliece(16, 8, 2)
        sage: mc == mc
       
        True
        """
        return repr(self) == repr(other)

    def __repr__(self):
        """
        A string representation of McEliece cryptosystem object.

        OUTPUT:

        - A string representation of this McEliece cryptosystem object.

        EXAMPLES::

        sage: from sage.crypto.public_key.mceliece import McEliece
        sage: mc = McEliece(16, 8, 2); mc

        McEliece cryptosystem with parameters (16, 8, 2)
        over [16, 8] Goppa code over GF(2)
        over Univariate Polynomial Ring in x over Finite Field in z4 of size 2^4
        with code locators:
        z4 + 1
        z4^3 + z4^2 + 1
        z4
        1
        z4^2
        z4^3 + z4^2 + z4 + 1
        0
        z4^3 + z4^2
        z4^2 + z4 + 1
        z4^2 + z4
        z4^2 + 1
        z4^3 + z4^2 + z4
        z4^3 + z4
        z4^3 + 1
        z4^3
        z4^3 + z4 + 1
        and Goppa polynomial x^2 + (z4 + 1)*x + z4^3 + z4^2
        """

        code_locators = ""
        for l in self.L:
            code_locators = code_locators + f"{l}\n"

        return (
        f"McEliece cryptosystem with parameters {self.parameters()}\n"
        f"over {self.C}\n"
        f"over {self.R}\n"
        f"with code locators:\n{code_locators}"
        f"and Goppa polynomial {self.g}"
        )
        
    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::
        // TODO
        """

        # TODO
        return ""

    def parameters(self):
        r"""
        Return public parameters of McEliece cryptosystem object

        OUTPUT:

        - The McEliece public parameters as tuple (``n``, ``k``, ``t``)

        EXAMPLES::

        sage: from sage.crypto.public_key.mceliece import McEliece
        sage: mc = McEliece(16, 8, 2)
        sage: mc.parameters()
        (16, 8, 2)


        sage: from sage.crypto.public_key.mceliece import McEliece
        sage: mc = McEliece(16, 8, 2)
        sage: mc.parameters()
        (32, 17, 3)
        """
        return (self.n, self.k, self.t)


    def public_key(self):
        r"""
        Return public key of McEliece cryptosystem object

        OUTPUT:

        - The McEliece public key as tuple (``S * G * P``, ``t``)

        // todo:

        EXAMPLES::

        sage: mc = McEliece(8, 4, 1)
        sage: mc.public_key()
        
        ([1 0 0 1 1 1 1]   
         [0 1 0 1 1 1 0]   
         [1 0 1 1 1 0 0], 1)
        """
        return (self.GG, self.t)


    def private_key(self):
        r"""
        Return private key of McEliece cryptosystem object

        OUTPUT:

        - The McEliece private key as tuple (``g``, ``G``, ``S``, ``P``)


        EXAMPLES::

        (
                                                            [0 1 0 0 0 0 0]
                                                            [1 0 0 0 0 0 0]
                                                            [0 0 0 0 0 1 0]
                                                            [0 0 1 0 0 0 0]
                                  [1 0 0 0 1 1 0]  [1 0 0]  [0 0 0 1 0 0 0]
                                  [0 1 0 1 1 0 1]  [1 0 1]  [0 0 0 0 1 0 0]
        x + z4^3 + z4^2 + z4 + 1, [0 0 1 0 1 0 1], [0 1 0], [0 0 0 0 0 0 1]
        )
        // todo:
        """
        return (self.g, self.G, self.S, self.P)


    def __call__(self, m):
        r"""
        Apply the McEliece scheme to encrypt plaintext message

        INPUT:

        - ``m`` -- binary vector of length ``k`` where ``k`` is public parameter of cryptosystem

        OUTPUT:

        - ciphertext ``m * S * G * P`` + ``e`` where ``e`` - is a random error vector of length ``n`` and hamming weight <= ``t``


        EXAMPLES::
        sage: mc = McEliece(16, 8, 2)
        sage: m = vector(GF(2), [0,1,0,0,1,1,0,1])
        sage: mc(m)

        (1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1)
        // todo:
        """
        #TODO: if k < n - mt -> message m should have (n - mt) - k trailing zeros?
        # or maybe just cut off (n - mt) - k trailing rows of C.gen_matrix?
        return m * self.GG + _random_binary_err_vector(self.n, self.t)

    @classmethod
    def encrypt(cls, m, k, n):
        r"""
        Apply the McEliece scheme to encrypt plaintext message

        INPUT:

        - ``m`` -- binary vector of length ``k`` where ``k`` is public parameter of cryptosystem
        - ``k`` -- public key of the McEliece cryptosystem object
        - ``n`` -- public parameters `n` of the McEliece cryptosystem object

        OUTPUT:

        - ciphertext ``m * S * G * P`` + ``e`` where ``e`` - is a random error vector of length ``n`` and hamming weight <= ``t``

        // todo:

        EXAMPLES::

        sage: mc = McEliece(20, 10, 2)
        sage: m = vector(GF(2), [1,1,1,0,1,1,0,0,0,1])
        sage: McEliece.encrypt(m, mc.public_key(), n)

        (1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0)
        """
        (GG, t) = k        

        return m * GG + _random_binary_err_vector(n, t)

    def _calculate_syndrome(self, c):  # TODO: use check matrix?
        r"""
        Calculate syndrome polynomial of ciphertext

        INPUT:

        - ``c`` -- ciphertext, binary vector of length ``n`` where ``n`` is public parameter of cryptosystem

        OUTPUT:

        - synrome polynomial of form: sum_{i=0}_{n-1} (c_{i} / (x - L_{i})) mod g(x)

        EXAMPLES:

        sage: mc = McEliece(16, 8, 2)
        sage: m = vector(GF(2), [1,1,0,1,1,0,0,0])
        sage: c = mc(m)
        sage: print(c)

        (1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1)

        sage: mc._calculate_syndrome(c)

        (z4^3 + z4^2)*x + z4^3 + z4^2 + z4 + 1
        """
        if self.n != len(c):
            raise Exception("len(L) != len(c)")

        var = self.R.gen()
        syndrome = self.R.zero()
        for i in range(len(c)):
            frac = 0
            if c[i] != 0:
                frac = (var - self.L[i]) / c[i]

            syndrome += _inverse_by_mod(frac, self.g)

        return syndrome.mod(self.g)


    def decrypt(self, c):
        r"""
        Apply the McEliece scheme to decrypt ciphertext

        INPUT:

        - ``c`` -- binary vector of length ``n`` where ``n`` is public parameter of cryptosystem

        OUTPUT:

        - plaintext ``m`` where ``m`` calculates as folows:
        c * P^(-1) = m * S * G + e * P^(-1) = m * S * G + e'
        then using Patterson error correction algorithm we find e' = e * P^(-1)
        then find c' - e' = m * S * G
        solving matrix equation c' - e' = m * s * G we find m * S
        result of m * S * S^(-1) is the plaintext
        // todo:

        EXAMPLES::

        sage: mc = McEliece(16, 8, 2)
        sage: m = vector(GF(2), [1,0,1,1,0,0,0,1])
        sage: mc.decrypt(mc(m))
        
        (1, 0, 1, 1, 0, 0, 0, 1)
        """
        c = c * self.P.inverse()
        c = c + _get_errors(self.R, self.L, self._calculate_syndrome(c), self.g)

        return self.G.solve_left(c) * self.S.inverse()