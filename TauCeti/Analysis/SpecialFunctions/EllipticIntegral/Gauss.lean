/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.AGM
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Trigonometric

/-!
# Gauss's AGM formula for the complete elliptic integral of the first kind

Writing `1 - k² sin² θ = cos² θ + k'² sin² θ` with the complementary modulus `k' = √(1 - k²)`
identifies `legendreK k` with the trigonometric AGM integral of the axes `1` and `k'`. The
evaluation of that integral by the arithmetic-geometric mean then gives **Gauss's theorem**

`legendreK k = π / (2 * agm 1 √(1 - k²))`  for `k ^ 2 < 1`.

Since the AGM is unchanged by replacing its arguments with their geometric and arithmetic means,
the same identification gives **Landen's transformation** of `K` (DLMF 19.8.12):

* `legendreK_two_mul_sqrt_div_one_add`, the ascending form: for `0 ≤ k < 1`,
  `legendreK (2 √k / (1 + k)) = (1 + k) * legendreK k`;
* `legendreK_eq_one_add_mul_legendreK`, the descending form: for `k ^ 2 < 1`, with
  `k' = √(1 - k²)` and `k₁ = (1 - k') / (1 + k')`, `legendreK k = (1 + k₁) * legendreK k₁`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.8, <https://dlmf.nist.gov/19.8>.
* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, Chapter 1.
-/

public section

open NNReal (agm)
open scoped Real

namespace TauCeti.Real

open _root_.Real

/-- For `k ^ 2 < 1`, the complete elliptic integral of the first kind is the AGM integral of
the axes `1` and the complementary modulus `√(1 - k²)`. -/
theorem legendreK_eq_agmIntegral {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = agmIntegral 1 √(1 - k ^ 2) := by
  have h : 0 < 1 - k ^ 2 := by linarith
  rw [agmIntegral_def, ← integral_rpow_cos_sq_add_sin_sq_eq_integral_Ioi one_ne_zero
    (sqrt_pos.2 h).ne', legendreK_def, legendreF_def]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [one_pow, one_mul, sq_sqrt h.le]
  congr 1
  linear_combination -sin_sq_add_cos_sq θ

/-- **Gauss's theorem**: for `k ^ 2 < 1`, the complete elliptic integral of the first kind is
`K(k) = π / (2 M(1, k'))`, where `M` is the arithmetic-geometric mean and `k' = √(1 - k²)` is
the complementary modulus. -/
theorem legendreK_eq_pi_div_two_mul_agm {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = π / (2 * agm 1 (√(1 - k ^ 2)).toNNReal) := by
  rw [legendreK_eq_agmIntegral hk, ← div_div]
  simpa [coe_toNNReal _ (sqrt_nonneg _)] using
    agmIntegral_eq_pi_div_two_div_agm (a := 1) (b := (√(1 - k ^ 2)).toNNReal)

/-- **Landen's transformation** of the complete integral of the first kind, ascending form
(DLMF 19.8.12): for `0 ≤ k < 1`, `K(2√k / (1 + k)) = (1 + k) K(k)`. -/
theorem legendreK_two_mul_sqrt_div_one_add {k : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) :
    legendreK (2 * √k / (1 + k)) = (1 + k) * legendreK k := by
  have hp : 0 < 1 + k := by linarith
  have hm : 0 < 1 - k := by linarith
  -- The complementary modulus of `2√k / (1 + k)` is `(1 - k) / (1 + k)`.
  have hsq : 1 - (2 * √k / (1 + k)) ^ 2 = ((1 - k) / (1 + k)) ^ 2 := by
    field_simp
    rw [sq_sqrt hk₀]
    ring
  have hlt : (2 * √k / (1 + k)) ^ 2 < 1 := by
    nlinarith [sq_pos_of_pos (div_pos hm hp)]
  have hk : k ^ 2 < 1 := by nlinarith
  rw [legendreK_eq_agmIntegral hlt, legendreK_eq_agmIntegral hk, hsq,
    sqrt_sq (div_pos hm hp).le]
  -- Scale both axes by `1 + k`, then take one AGM step from `(1 + k, 1 - k)`.
  have hscale := agmIntegral_mul_left (1 + k)⁻¹ (1 + k) (1 - k)
  rw [inv_mul_cancel₀ hp.ne', ← div_eq_inv_mul, abs_inv, abs_of_pos hp, div_inv_eq_mul] at hscale
  rw [hscale, agmIntegral_eq_agmIntegral_gm_am hp.le hm.le, mul_comm, agmIntegral_comm]
  congr 2
  · ring
  · congr 1
    ring

/-- **Landen's transformation** of the complete integral of the first kind, descending form
(DLMF 19.8.12): for `k ^ 2 < 1`, with `k' = √(1 - k²)` and `k₁ = (1 - k') / (1 + k')`, we have
`K(k) = (1 + k₁) K(k₁)`. -/
theorem legendreK_eq_one_add_mul_legendreK {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = (1 + (1 - √(1 - k ^ 2)) / (1 + √(1 - k ^ 2))) *
      legendreK ((1 - √(1 - k ^ 2)) / (1 + √(1 - k ^ 2))) := by
  set k' := √(1 - k ^ 2)
  have hk'0 : 0 < k' := sqrt_pos.2 (by linarith)
  have hk'1 : k' ≤ 1 := sqrt_le_one.2 (by nlinarith)
  have hk'sq : k' ^ 2 = 1 - k ^ 2 := sq_sqrt (by linarith)
  have h₀ : 0 ≤ (1 - k') / (1 + k') := div_nonneg (by linarith) (by linarith)
  have h₁ : (1 - k') / (1 + k') < 1 := (div_lt_one (by linarith)).2 (by linarith)
  rw [← legendreK_two_mul_sqrt_div_one_add h₀ h₁]
  -- The ascending transformation of `k₁` returns the modulus `|k|`, and `K` is even.
  have habs : 2 * √((1 - k') / (1 + k')) / (1 + (1 - k') / (1 + k')) = |k| := by
    have hnn : 0 ≤ 2 * √((1 - k') / (1 + k')) / (1 + (1 - k') / (1 + k')) := by
      have : 0 ≤ 1 + (1 - k') / (1 + k') := by linarith
      positivity
    rw [← sqrt_sq_eq_abs, ← sqrt_sq hnn]
    congr 1
    rw [div_pow, mul_pow, sq_sqrt h₀]
    field_simp
    linear_combination (-4 : ℝ) * hk'sq
  rw [habs]
  rcases abs_choice k with h | h <;> simp [h]

end TauCeti.Real
