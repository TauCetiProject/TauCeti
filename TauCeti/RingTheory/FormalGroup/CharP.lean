/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import TauCeti.RingTheory.MvPowerSeries.CharP

/-!
# Formal groups with a subgroup cut out by `X ^ (p ^ n)`

Let `F(X, Y)` be a one-dimensional formal group law over a commutative ring `R`, and let `q` be a
natural number. The closed subscheme `X ^ q = 0` of the formal group is closed under the group law
when `F(X, Y) ^ q` lies in the ideal `(X ^ q, Y ^ q)` of `R⟦X, Y⟧`. If `p = 0` in `R`, then
`X ^ (p ^ n) = 0` is the kernel of the `n`-th power of Frobenius, so this holds for `q = p ^ n`.
The first conclusion of Katz–Mazur, Lemma 5.3.4, is a converse, proved here: if it holds for
`q = p ^ n` with `p` prime and `n ≥ 1`, then `p = 0` in `R`. (Katz and Mazur also identify the
subgroup with the kernel of the `n`-th power of Frobenius; that identification is not part of this
file.) This is the formal-group input to the rigidity statement that if the zero section of a
smooth commutative one-dimensional group scheme is a point of exact order `p ^ n` in the sense of
Drinfeld, then `p = 0` on the base.

The argument only uses the linear part `X + Y` of `F`; the coefficient computation is
`MvPowerSeries.natCast_eq_zero_of_pow_mem_span` in `TauCeti.RingTheory.MvPowerSeries.CharP`.

## Main results

* `FormalGroup.natCast_eq_zero_of_pow_mem_span`: if `F(X, Y) ^ (p ^ n) ∈ (X ^ (p ^ n), Y ^ (p ^ n))`
  for a prime `p` and `n ≠ 0`, then `p = 0` in `R`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Lemma 5.3.4.
-/

public section

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- **Katz–Mazur, Lemma 5.3.4.** If the closed subscheme `X ^ (p ^ n) = 0` of a one-dimensional
formal group law `F` over `R` is a subgroup scheme, that is, if `F(X, Y) ^ (p ^ n)` lies in the
ideal `(X ^ (p ^ n), Y ^ (p ^ n))` of `R⟦X, Y⟧`, for a prime `p` and some `n ≠ 0`, then `p = 0`
in `R`. -/
theorem natCast_eq_zero_of_pow_mem_span (F : FormalGroup R) {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : F.toPowerSeries ^ p ^ n ∈
      Ideal.span {MvPowerSeries.X 0 ^ p ^ n, MvPowerSeries.X 1 ^ p ^ n}) :
    (p : R) = 0 :=
  MvPowerSeries.natCast_eq_zero_of_pow_mem_span F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
    hp hn h

end FormalGroup
