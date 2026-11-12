/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted

/-!
# Holomorphic division values of the Weierstrass derivative

For a natural number `N` and an integer pair `b`, the value
`℘'((b₀ z + b₁) / N; ℤ z + ℤ)` is a weight-three single-residue Eisenstein series,
multiplied by `-2 N³`. Consequently it is holomorphic as the modulus `z` varies in `ℍ`.
After division by two, these are the second coordinates in the Weierstrass parametrization
of torsion points on the family of elliptic curves with lattice `ℤ z + ℤ`.

The formula includes pairs divisible by `N`: Mathlib assigns value zero to `℘'` at
lattice points, and the associated odd-weight zero-residue series also vanishes.
For a point on the elliptic curve, those pairs represent the identity rather than an
affine point with second coordinate zero.

## References

* J. S. Milne, *Modular Functions and Modular Forms*, Proposition 3.10, for holomorphic
  variation of lattice sums, and Proposition 3.12, for Weierstrass uniformization.
-/

public section

open PeriodPair UpperHalfPlane
open scoped Manifold

namespace TauCeti.EisensteinSeries

variable {N : ℕ}

/-- A division value of the Weierstrass derivative is a weight-three Eisenstein series
in the corresponding residue class, with the normalization `-2 N³`. -/
theorem derivWeierstrassP_periodPair_div_eq_weightedEisensteinSeries
    (b : Fin 2 → ℤ) (z : ℍ) :
    ℘'[z.periodPair] (((b 0 : ℂ) * z + b 1) / N) =
      (-2 * (N : ℂ) ^ 3) * weightedEisensteinSeries
        (Pi.single (((↑) : ℤ → ZMod N) ∘ b) 1) 3 z := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [derivWeierstrassP_zero]
  have : NeZero N := ⟨hN⟩
  rw [weightedEisensteinSeries_single_eq_tsum, ← (Equiv.neg (Fin 2 → ℤ)).tsum_eq,
    ← tsum_mul_left]
  refine (hasSum_derivWeierstrassP_periodPair z _).tsum_eq.symm.trans (tsum_congr fun y ↦ ?_)
  rw [Equiv.neg_apply, smul_neg, ← sub_eq_add_neg, EisensteinSeries.eisSummand,
    TauCeti.UpperHalfPlane.intCast_sub_nsmul_mul_add_intCast]
  simp only [zpow_neg, zpow_ofNat, mul_pow]
  field_simp

/-- The Weierstrass derivative at a division point varies holomorphically with the modulus. -/
theorem mdifferentiable_derivWeierstrassP_periodPair_div (b : Fin 2 → ℤ) :
    MDiff (fun z : ℍ ↦ ℘'[z.periodPair] (((b 0 : ℂ) * z + b 1) / N)) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simpa [derivWeierstrassP_zero] using mdifferentiable_const
  have : NeZero N := ⟨hN⟩
  simp_rw [derivWeierstrassP_periodPair_div_eq_weightedEisensteinSeries]
  apply mdifferentiable_const.mul
  simpa only [coe_weightedEisensteinSeriesSIF] using
    weightedEisensteinSeries_mdifferentiable
      (Pi.single (((↑) : ℤ → ZMod N) ∘ b) 1) (by norm_num : (3 : ℤ) ≤ 3)

end TauCeti.EisensteinSeries
