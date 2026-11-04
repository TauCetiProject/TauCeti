/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Hilbert series of a symmetric algebra

The degree-`n` part of the symmetric algebra of a finite free module of rank `r` has
rank `r.multichoose n`. Its Hilbert series is therefore `(1 - t)⁻ʳ`, expressed using
Mathlib's unit `PowerSeries.invOneSubPow` and by the denominator-cleared identity
`Hilb(Sym M, t) * (1 - t)^r = 1`.

The base is any commutative semiring satisfying the strong rank condition. The series
coefficients can lie in any commutative ring, independently of the base. In particular,
integer coefficients retain the dimensions over a field of positive characteristic.
Rank zero is included: its series is `1`, with zero coefficients in positive degrees.

For polynomial functions on a vector space `V`, apply the results to `M = V*`.
The denominator-cleared form combines with homogeneous regular-sequence quotient
formulas to compute coinvariant Hilbert series.

The coefficient calculation uses `Module.Basis.symmetricAlgebraHomogeneous` and
Mathlib's `Sym.card_sym_eq_multichoose`; the series calculation uses the existing
binomial expansion of `PowerSeries.invOneSubPow`.

## References

* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), §§2–3.
-/

public section

namespace TauCeti.SymmetricAlgebra

variable (R M : Type*) [CommSemiring R] [StrongRankCondition R]
  [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The Hilbert series of the symmetric algebra of a finite free module of rank `r`
is the inverse of `(1 - X)^r`. The coefficients may be taken independently of the base,
so taking them in `ℤ` retains ranks without reduction modulo the characteristic. -/
theorem mk_finrank_eq_invOneSubPow (S : Type*) [CommRing S] :
    PowerSeries.mk (fun n ↦ (Module.finrank R (homogeneousSubmodule R M n) : S)) =
      (PowerSeries.invOneSubPow S (Module.finrank R M) : PowerSeries S) := by
  simp_rw [finrank_homogeneousSubmodule]
  cases hr : Module.finrank R M with
  | zero =>
    ext n
    cases n <;> simp [PowerSeries.invOneSubPow_zero]
  | succ r =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp only [PowerSeries.coeff_mk, Nat.multichoose_eq]
    congr 1
    rw [Nat.succ_add_sub_one, Nat.choose_symm_add]

/-- The denominator-cleared Hilbert-series formula for a symmetric algebra. It is valid
over an arbitrary commutative coefficient ring, including integer coefficients when
the underlying module is over a field of positive characteristic. -/
theorem mk_finrank_mul_one_sub_X_pow (S : Type*) [CommRing S] :
    PowerSeries.mk (fun n ↦ (Module.finrank R (homogeneousSubmodule R M n) : S)) *
      (1 - PowerSeries.X) ^ Module.finrank R M = 1 := by
  rw [mk_finrank_eq_invOneSubPow,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  exact (PowerSeries.invOneSubPow S (Module.finrank R M)).val_inv

end TauCeti.SymmetricAlgebra
