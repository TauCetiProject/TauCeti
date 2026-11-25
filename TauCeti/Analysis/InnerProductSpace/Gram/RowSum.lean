/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Gram row sums and Selberg's inequality

For a finite family `y : ι → E` in an inner product space over `𝕜` (`ℝ` or `ℂ`), write
`rᵢ = ∑ⱼ ‖⟪yᵢ, yⱼ⟫‖` for the sum of the absolute values of the `i`-th row of the Gram matrix
`Matrix.gram 𝕜 y`. These row sums control the family as if it were orthogonal: a linear
combination satisfies `‖∑ᵢ cᵢ yᵢ‖² ≤ ∑ᵢ |cᵢ|² rᵢ`, and Selberg's inequality
`∑ᵢ |⟪x, yᵢ⟫|² / rᵢ ≤ ‖x‖²` generalizes Bessel's inequality to arbitrary finite families. The
family may be empty, have repetitions or zero vectors, and be linearly dependent; a zero row
contributes zero because real division by zero is zero. No completeness or finite dimensionality
is assumed, and except for the characterization of vanishing row sums the space may be
seminormed.

Bounding every row sum by a common constant gives the unweighted inequality
`∑ᵢ |⟪x, yᵢ⟫|² ≤ C ‖x‖²`. In the large sieve the vectors are exponential or character vectors,
and the off-diagonal Gram entries are the exponential or character sums to be estimated.

## Main results

* `TauCeti.sum_norm_inner_eq_zero_iff`, `TauCeti.sum_norm_inner_pos_iff`: a Gram row sum
  vanishes exactly at a zero vector (at a vector of zero norm in a seminormed space:
  `TauCeti.sum_norm_inner_eq_zero_iff_norm_eq_zero`).
* `TauCeti.norm_sum_smul_sq_le_sum_norm_sq_mul_sum_norm_inner`: the Gram-row bound
  `‖∑ᵢ cᵢ yᵢ‖² ≤ ∑ᵢ |cᵢ|² rᵢ`.
* `TauCeti.norm_sub_sum_smul_sq_le`: Selberg's projection defect bound
  `‖x - ∑ᵢ (⟪yᵢ, x⟫ / rᵢ) yᵢ‖² ≤ ‖x‖² - ∑ᵢ |⟪x, yᵢ⟫|² / rᵢ`.
* `TauCeti.sum_norm_inner_sq_div_le_norm_sq`: Selberg's inequality.
* `TauCeti.sum_norm_inner_sq_le_of_row_le`: the uniform row-sum inequality, with its
  specializations `TauCeti.sum_norm_inner_sq_le_iSup_mul_norm_sq` (the largest row sum) and
  `TauCeti.sum_norm_inner_sq_le_of_norm_sq_le_of_sum_erase_le` (diagonal plus off-diagonal bounds).

## References

* E. Bombieri, *A note on the large sieve*, Acta Arith. 18 (1971), 401–404, Proposition 1 and its
  proof, attributed there to A. Selberg. The coefficient displayed after equation (4) divides by
  the square of the row sum; the argument needs the row sum `rᵢ` itself, which is used here.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, Theorem 7 (the maximal-row form).
-/

public section

open Finset RCLike
open scoped InnerProductSpace ComplexConjugate

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The diagonal Gram entry `‖⟪v, v⟫‖` is the squared norm of `v`. -/
theorem norm_inner_self_eq_norm_sq (v : E) : ‖⟪v, v⟫_𝕜‖ = ‖v‖ ^ 2 := by
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]

/-- The squared norm of a vector of a family is at most its Gram row sum. -/
theorem norm_sq_le_sum_norm_inner (y : ι → E) (i : ι) :
    ‖y i‖ ^ 2 ≤ ∑ j, ‖⟪y i, y j⟫_𝕜‖ :=
  (norm_inner_self_eq_norm_sq (y i)).symm.trans_le <|
    single_le_sum (f := fun j ↦ ‖⟪y i, y j⟫_𝕜‖) (fun _ _ ↦ norm_nonneg _) (mem_univ i)

/-- A Gram row sum `∑ j, ‖⟪y i, y j⟫‖` vanishes exactly when `y i` has zero norm. In a normed
space this is `sum_norm_inner_eq_zero_iff`. -/
theorem sum_norm_inner_eq_zero_iff_norm_eq_zero (y : ι → E) (i : ι) :
    ∑ j, ‖⟪y i, y j⟫_𝕜‖ = 0 ↔ ‖y i‖ = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ sum_eq_zero fun j _ ↦ by simp [inner_eq_zero_of_left _ h]⟩
  have := norm_sq_le_sum_norm_inner (𝕜 := 𝕜) y i
  rw [h] at this
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _))

/-- **The Gram-row bound.** The squared norm of a finite linear combination is at most the
sum of the squared coefficients weighted by the Gram row sums `∑ j, ‖⟪y i, y j⟫‖`. No
orthogonality is assumed; equality holds for repeated unit vectors with all coefficients `1`. -/
theorem norm_sum_smul_sq_le_sum_norm_sq_mul_sum_norm_inner (y : ι → E) (c : ι → 𝕜) :
    ‖∑ i, c i • y i‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2 * ∑ j, ‖⟪y i, y j⟫_𝕜‖ := by
  set g : ι → ι → ℝ := fun i j ↦ ‖⟪y i, y j⟫_𝕜‖
  have hg : ∀ i j, g i j = g j i := fun i j ↦ norm_inner_symm _ _
  -- Expand the squared norm into the double sum of `conj (c i) * c j * ⟪y i, y j⟫`.
  have hexp : ‖∑ i, c i • y i‖ ^ 2 ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * g i j := by
    calc ‖∑ i, c i • y i‖ ^ 2 = re ⟪∑ i, c i • y i, ∑ j, c j • y j⟫_𝕜 :=
          (inner_self_eq_norm_sq _).symm
      _ ≤ ‖⟪∑ i, c i • y i, ∑ j, c j • y j⟫_𝕜‖ := re_le_norm _
      _ = ‖∑ i, ∑ j, conj (c i) * c j * ⟪y i, y j⟫_𝕜‖ := by
          simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
      _ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * g i j := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans ?_)
          simp [g]
  -- Use `2 |cᵢ| |cⱼ| ≤ |cᵢ|² + |cⱼ|²` and the symmetry of `g` to collect the two halves.
  have hamgm : ∀ i j, ‖c i‖ * ‖c j‖ * g i j ≤ (‖c i‖ ^ 2 * g i j + ‖c j‖ ^ 2 * g j i) / 2 := by
    intro i j
    rw [← hg i j]
    nlinarith [sq_nonneg (‖c i‖ - ‖c j‖), norm_nonneg ⟪y i, y j⟫_𝕜]
  have hswap : ∑ i, ∑ j, ‖c j‖ ^ 2 * g j i = ∑ i, ∑ j, ‖c i‖ ^ 2 * g i j := sum_comm
  calc ‖∑ i, c i • y i‖ ^ 2 ≤ ∑ i, ∑ j, (‖c i‖ ^ 2 * g i j + ‖c j‖ ^ 2 * g j i) / 2 :=
        hexp.trans (sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hamgm i j)
    _ = ∑ i, ‖c i‖ ^ 2 * ∑ j, g i j := by
        simp_rw [← sum_div, sum_add_distrib, hswap, mul_sum]
        ring

/-- **Selberg's projection defect bound.** Projecting `x` onto the family with the coefficients
`⟪y i, x⟫ / rᵢ`, where `rᵢ = ∑ j, ‖⟪y i, y j⟫‖` is the Gram row sum, leaves a defect of squared
norm at most `‖x‖² - ∑ i, ‖⟪x, y i⟫‖² / rᵢ`. -/
theorem norm_sub_sum_smul_sq_le (y : ι → E) (x : E) :
    ‖x - ∑ i, (⟪y i, x⟫_𝕜 / ((∑ j, ‖⟪y i, y j⟫_𝕜‖ : ℝ) : 𝕜)) • y i‖ ^ 2 ≤
      ‖x‖ ^ 2 - ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j, ‖⟪y i, y j⟫_𝕜‖ := by
  set r : ι → ℝ := fun i ↦ ∑ j, ‖⟪y i, y j⟫_𝕜‖
  set S := ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i
  -- The cross term equals `S`, since `⟪y i, x⟫ * ⟪x, y i⟫ = ‖⟪x, y i⟫‖ ^ 2`.
  have hcross : re ⟪x, ∑ i, (⟪y i, x⟫_𝕜 / (r i : 𝕜)) • y i⟫_𝕜 = S := by
    rw [inner_sum, map_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    -- Write the `i`-th term as `conj ⟪x, y i⟫ * ⟪x, y i⟫ / rᵢ`, then take real parts.
    rw [inner_smul_right, div_mul_eq_mul_div, ← inner_conj_symm (y i) x, RCLike.conj_mul]
    norm_cast
  -- The coefficients make each term of the Gram-row bound equal to the corresponding term of `S`:
  -- both sides vanish for a zero row, and otherwise `‖⟪x, y i⟫‖² / rᵢ² * rᵢ = ‖⟪x, y i⟫‖² / rᵢ`.
  have hcoef : ∀ i, ‖⟪y i, x⟫_𝕜 / (r i : 𝕜)‖ ^ 2 * r i = ‖⟪x, y i⟫_𝕜‖ ^ 2 / r i := by
    intro i
    have hr : 0 ≤ r i := sum_nonneg fun _ _ ↦ norm_nonneg _
    rcases hr.eq_or_lt with h | h
    · simp [← h]
    · simp [norm_inner_symm, abs_of_pos h]
      field_simp
  have hsq : ‖∑ i, (⟪y i, x⟫_𝕜 / (r i : 𝕜)) • y i‖ ^ 2 ≤ S :=
    (norm_sum_smul_sq_le_sum_norm_sq_mul_sum_norm_inner y _).trans_eq
      (sum_congr rfl fun i _ ↦ hcoef i)
  rw [norm_sub_sq (𝕜 := 𝕜), hcross]
  linarith

/-- **Selberg's inequality.** For every finite family `y` and every vector `x`,
`∑ i, ‖⟪x, y i⟫‖² / rᵢ ≤ ‖x‖²`, where `rᵢ = ∑ j, ‖⟪y i, y j⟫‖` is the Gram row sum. Zero rows
contribute zero. For an orthonormal family every row sum is one, and this is Bessel's
inequality. -/
theorem sum_norm_inner_sq_div_le_norm_sq (y : ι → E) (x : E) :
    ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j, ‖⟪y i, y j⟫_𝕜‖ ≤ ‖x‖ ^ 2 := by
  linarith [norm_sub_sum_smul_sq_le (𝕜 := 𝕜) y x,
    sq_nonneg ‖x - ∑ i, (⟪y i, x⟫_𝕜 / ((∑ j, ‖⟪y i, y j⟫_𝕜‖ : ℝ) : 𝕜)) • y i‖]

/-- **The uniform Gram-row inequality.** If every Gram row sum `∑ j, ‖⟪y i, y j⟫‖` is at most a
nonnegative constant `C`, then `∑ i, ‖⟪x, y i⟫‖² ≤ C ‖x‖²`. -/
theorem sum_norm_inner_sq_le_of_row_le (y : ι → E) (x : E) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖⟪y i, y j⟫_𝕜‖ ≤ C) :
    ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  calc ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ ∑ i, C * (‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j, ‖⟪y i, y j⟫_𝕜‖) := by
        refine sum_le_sum fun i _ ↦ ?_
        rcases (sum_nonneg fun j _ ↦ norm_nonneg ⟪y i, y j⟫_𝕜).eq_or_lt with h | h
        · -- A zero row sum forces `‖y i‖ = 0`, hence `⟪x, y i⟫ = 0`.
          have hy := (sum_norm_inner_eq_zero_iff_norm_eq_zero y i).mp h.symm
          simp [inner_eq_zero_of_right x hy]
        · rw [mul_div_assoc', le_div_iff₀ h]
          rw [mul_comm C]
          exact mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    _ = C * ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 / ∑ j, ‖⟪y i, y j⟫_𝕜‖ := (mul_sum ..).symm
    _ ≤ C * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_norm_inner_sq_div_le_norm_sq y x) hC

/-- **The maximal-row Gram inequality.** `∑ i, ‖⟪x, y i⟫‖² ≤ (⨆ i, rᵢ) ‖x‖²`, where
`rᵢ = ∑ j, ‖⟪y i, y j⟫‖` is the Gram row sum. For an empty family both sides are zero. -/
theorem sum_norm_inner_sq_le_iSup_mul_norm_sq (y : ι → E) (x : E) :
    ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ (⨆ i, ∑ j, ‖⟪y i, y j⟫_𝕜‖) * ‖x‖ ^ 2 :=
  sum_norm_inner_sq_le_of_row_le y x
    (Real.iSup_nonneg fun i ↦ sum_nonneg fun j _ ↦ norm_nonneg ⟪y i, y j⟫_𝕜)
    fun i ↦ le_ciSup (f := fun i ↦ ∑ j, ‖⟪y i, y j⟫_𝕜‖) (Set.finite_range _).bddAbove i

/-- **The diagonal/off-diagonal Gram inequality.** If `‖y i‖² ≤ D` and the off-diagonal row sum
`∑_{j ≠ i} ‖⟪y i, y j⟫‖` is at most `O` for every `i`, and `0 ≤ D + O`, then
`∑ i, ‖⟪x, y i⟫‖² ≤ (D + O) ‖x‖²`. -/
theorem sum_norm_inner_sq_le_of_norm_sq_le_of_sum_erase_le [DecidableEq ι] (y : ι → E) (x : E)
    {D O : ℝ} (hDO : 0 ≤ D + O) (hD : ∀ i, ‖y i‖ ^ 2 ≤ D)
    (hO : ∀ i, ∑ j ∈ univ.erase i, ‖⟪y i, y j⟫_𝕜‖ ≤ O) :
    ∑ i, ‖⟪x, y i⟫_𝕜‖ ^ 2 ≤ (D + O) * ‖x‖ ^ 2 := by
  refine sum_norm_inner_sq_le_of_row_le y x hDO fun i ↦ ?_
  rw [← add_sum_erase _ _ (mem_univ i), norm_inner_self_eq_norm_sq]
  exact add_le_add (hD i) (hO i)

end Seminormed

section Normed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A Gram row sum `∑ j, ‖⟪y i, y j⟫‖` vanishes exactly when `y i = 0`. -/
@[simp]
theorem sum_norm_inner_eq_zero_iff (y : ι → E) (i : ι) :
    ∑ j, ‖⟪y i, y j⟫_𝕜‖ = 0 ↔ y i = 0 := by
  rw [sum_norm_inner_eq_zero_iff_norm_eq_zero, norm_eq_zero]

/-- A Gram row sum `∑ j, ‖⟪y i, y j⟫‖` is positive exactly when `y i ≠ 0`, even for a linearly
dependent family. -/
theorem sum_norm_inner_pos_iff (y : ι → E) (i : ι) :
    0 < ∑ j, ‖⟪y i, y j⟫_𝕜‖ ↔ y i ≠ 0 := by
  rw [(sum_nonneg fun j _ ↦ norm_nonneg ⟪y i, y j⟫_𝕜).lt_iff_ne', Ne,
    sum_norm_inner_eq_zero_iff]

end Normed

end TauCeti
