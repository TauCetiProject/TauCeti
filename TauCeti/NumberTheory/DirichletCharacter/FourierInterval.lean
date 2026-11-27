/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.IntervalSum
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Data.ZMod.Ico
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.GaussSum

/-!
# Gauss-sum expansion of Dirichlet character interval sums

* `DirichletCharacter.sum_range_add_eq_inv_gaussSum_mul_sum` gives the expansion in nonzero
  additive frequencies using Mathlib's `gaussSum_mulShift_of_isPrimitive`.
* `DirichletCharacter.norm_sum_range_add_le_sum_norm_stdAddChar` bounds a character sum by
  the sum of the norms of its additive interval sums, using
  `DirichletCharacter.IsPrimitive.norm_gaussSum`.
* `DirichletCharacter.norm_intervalSum_le_sum_min_inv_sin` gives the finite cosecant bound for
  `DirichletCharacter.intervalSum`, using
  `ZMod.norm_sum_range_stdAddChar_mul_add_le_min_inv_sin` and
  `ZMod.sum_val_erase_zero_eq_sum_Ico`.

## References

* C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, Integers 11 (2011),
  equations (4) and (7).
-/

public section

open Finset ZMod
open scoped Real

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The Gauss-sum expansion of an interval sum of a primitive nonprincipal character, with the
inverse character in the coefficients and the Gauss-sum denominator. For an interval
`(M, M + H]`, take the starting residue `a = (M : ZMod q) + 1`. See Pomerance,
*Remarks on the Pólya–Vinogradov inequality*, (7). -/
theorem sum_range_add_eq_inv_gaussSum_mul_sum (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1) (a : ZMod q) (H : ℕ) :
    ∑ j ∈ range H, χ (a + (j : ZMod q)) =
      (gaussSum χ⁻¹ stdAddChar)⁻¹ * ∑ k ∈ univ.erase (0 : ZMod q),
        χ⁻¹ k * ∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod q))) := by
  have hτ := gaussSum_inv_ne_zero_of_isPrimitive hχ (isPrimitive_stdAddChar q)
  have hexpand (x : ZMod q) : χ x = (gaussSum χ⁻¹ stdAddChar)⁻¹ *
      ∑ k ∈ univ.erase (0 : ZMod q), χ⁻¹ k * stdAddChar (k * x) := by
    have hzero := χ⁻¹.map_zero' (mt hχ.eq_one_iff.mpr hχ₀)
    rw [eq_inv_mul_iff_mul_eq₀ hτ]
    calc
      gaussSum χ⁻¹ stdAddChar * χ x = gaussSum χ⁻¹ (stdAddChar.mulShift x) := by
        simpa only [inv_inv, mul_comm (χ x)] using
          (gaussSum_mulShift_of_isPrimitive stdAddChar hχ.inv x).symm
      _ = _ := by
        rw [gaussSum, ← sum_erase_add _ _ (mem_univ (0 : ZMod q))]
        simp only [hzero, zero_mul, add_zero, AddChar.mulShift_apply, mul_comm x]
  simp_rw [hexpand, ← mul_sum]
  rw [sum_comm]
  simp_rw [← mul_sum]

/-- The triangle-inequality bound from the Gauss-sum expansion of a primitive nonprincipal
character. The reciprocal square root is the norm of the inverse Gauss sum. -/
theorem norm_sum_range_add_le_sum_norm_stdAddChar (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1) (a : ZMod q) (H : ℕ) :
    ‖∑ j ∈ range H, χ (a + (j : ZMod q))‖ ≤
      (Real.sqrt q)⁻¹ * ∑ k ∈ univ.erase (0 : ZMod q),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod q)))‖ := by
  rw [χ.sum_range_add_eq_inv_gaussSum_mul_sum hχ hχ₀, norm_mul, norm_inv,
    hχ.inv.norm_gaussSum (isPrimitive_stdAddChar q)]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ ?_))
    (by positivity)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ⁻¹.norm_le_one k)

/-- The norm of an interval sum of a primitive nonprincipal character is bounded by the
sum of the reciprocal sines, capped termwise by the interval length and divided by `√q`.
See Pomerance, *Remarks on the Pólya–Vinogradov inequality*, (4) and (7). -/
theorem norm_intervalSum_le_sum_min_inv_sin (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1) (M : ℤ) (H : ℕ) :
    ‖χ.intervalSum M H‖ ≤
      (Real.sqrt q)⁻¹ * ∑ k ∈ Ico 1 q, min (H : ℝ) (Real.sin (π * k / q))⁻¹ := by
  rw [χ.intervalSum_eq_sum_range, ← sum_val_erase_zero_eq_sum_Ico
    (fun k ↦ min (H : ℝ) (Real.sin (π * k / q))⁻¹)]
  refine (χ.norm_sum_range_add_le_sum_norm_stdAddChar hχ hχ₀ _ H).trans ?_
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk ↦ ?_) (by positivity)
  exact norm_sum_range_stdAddChar_mul_add_le_min_inv_sin _ k H (mem_erase.mp hk).1

end DirichletCharacter
