/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum
import Mathlib.Data.Nat.Choose.Cast
import TauCeti.LinearAlgebra.BilinearForm.Hermite

/-!
# Hermite's inequality for the minimum of a positive definite lattice

Let `L` be a positive definite integral lattice of rank `n`. Hermite's inequality bounds its
minimum `min L`, the least norm `B(x, x)` of a nonzero lattice vector, by its determinant:

```text
min L ≤ (4 / 3) ^ ((n - 1) / 2) · (det L) ^ (1 / n).
```

It is the specialization to the integral form of `L` of
`LinearMap.BilinForm.exists_ne_zero_three_pow_mul_pow_le_four_pow_mul_det`, and it is stated twice:
once as the inequality of integers `3 ^ (n choose 2) · (min L)ⁿ ≤ 4 ^ (n choose 2) · det L`, and
once in the root form displayed above. Neither needs a rank hypothesis: in rank zero the minimum is
`0`, the determinant is `1`, and both statements hold trivially.

The constant is sharp in rank `2`: the root lattice `A₂` has minimum `2` and determinant `3`, and
`2 = (4 / 3) ^ (1 / 2) · 3 ^ (1 / 2)`; this is recorded in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Hermite`.

## Main results

* `TauCeti.IntegralLattice.IsPosDef.three_pow_mul_minimum_pow_le`:
  `3 ^ (n choose 2) · (min L)ⁿ ≤ 4 ^ (n choose 2) · det L`.
* `TauCeti.IntegralLattice.IsPosDef.minimum_le_rpow_mul_determinant_rpow`:
  `min L ≤ (4 / 3) ^ ((n - 1) / 2) · (det L) ^ (1 / n)`.

## References

* C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. 40 (1850), 261–315.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.5.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **Hermite's inequality for the minimum, without roots.** A positive definite integral lattice
of rank `n` satisfies `3 ^ (n choose 2) · (min L)ⁿ ≤ 4 ^ (n choose 2) · det L`. -/
theorem IsPosDef.three_pow_mul_minimum_pow_le (hL : L.IsPosDef) :
    3 ^ (finrank ℤ L).choose 2 * (L.minimum : ℤ) ^ finrank ℤ L ≤
      4 ^ (finrank ℤ L).choose 2 * L.determinant := by
  classical
  let b := Module.finBasis ℤ L
  rw [L.determinant_eq_gramDet b, gramDet_def, gramMatrix_eq_toMatrix]
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · have hn : finrank ℤ L = 0 := finrank_zero_of_subsingleton
    have : IsEmpty (Fin (finrank ℤ L)) := by rw [hn]; infer_instance
    simp [hn]
  obtain ⟨x, hx, hle⟩ := L.integralForm.exists_ne_zero_three_pow_mul_pow_le_four_pow_mul_det
    L.isSymm_integralForm
    (fun x hx ↦ by simpa [integralNorm_apply] using hL.posDef_integralNorm x hx) b
  rw [Fintype.card_fin] at hle
  refine le_trans ?_ hle
  gcongr
  rw [← integralNorm_apply]
  exact hL.isPosSemidef.minimum_le_integralNorm hx

/-- **Hermite's inequality for the minimum.** A positive definite integral lattice of rank `n`
satisfies `min L ≤ (4 / 3) ^ ((n - 1) / 2) · (det L) ^ (1 / n)`. -/
theorem IsPosDef.minimum_le_rpow_mul_determinant_rpow (hL : L.IsPosDef) :
    (L.minimum : ℝ) ≤ (4 / 3 : ℝ) ^ (((finrank ℤ L : ℝ) - 1) / 2) *
      (L.determinant : ℝ) ^ (1 / (finrank ℤ L : ℝ)) := by
  set n := finrank ℤ L
  have h := hL.three_pow_mul_minimum_pow_le
  have hdet : (0 : ℝ) ≤ L.determinant := by
    have : (0 : ℤ) ≤ 4 ^ n.choose 2 * L.determinant := le_trans (by positivity) h
    exact_mod_cast nonneg_of_mul_nonneg_right this (by positivity)
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · rw [minimum_eq_zero_of_subsingleton, Nat.cast_zero]
    positivity
  have hn : n ≠ 0 := finrank_pos.ne'
  refine le_of_pow_le_pow_left₀ hn (by positivity) ?_
  have hexp : ((n : ℝ) - 1) / 2 * n = (n.choose 2 : ℕ) := by
    rw [Nat.cast_choose_two]
    ring
  rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_mul_natCast hdet, hexp,
    one_div_mul_cancel (Nat.cast_ne_zero.mpr hn), Real.rpow_one, Real.rpow_natCast, div_pow,
    div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  exact_mod_cast h

end TauCeti.IntegralLattice
