/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.ModulusDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Landen's transformation of the complete integral of the second kind

The ascending transformation sends `k` to `2√k / (1 + k)` and expresses the second-kind
integral at the new modulus in terms of `E(k)` and `K(k)`. The descending transformation
uses `k₁ = (1 - k') / (1 + k')`, where `k' = √(1 - k²)`, and reads
`E(k) = (1 + k') E(k₁) - k' K(k)`.

Together with the first-kind transformations in `Gauss`, these identities allow simultaneous
evaluation of the two complete elliptic integrals by arithmetic-geometric mean iteration.
We obtain the second-kind transformation by differentiating the first-kind one in the modulus.

## References

* NIST *Digital Library of Mathematical Functions*, §19.8(ii), <https://dlmf.nist.gov/19.8>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, §9.5.

The corresponding Carlson-form transformation is `Carlson.carlsonRE_sq_eq` in Bastiaan J
Braams' `lean-codes`, `Carlson/Elliptic/LandenExercises.lean` (commit `2b8cba1`, Apache-2.0).
The proof here uses the real Legendre modulus derivatives instead of Carlson's general
quadratic transformation.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter Set
open scoped Topology

/-- **Landen's transformation** of the complete integral of the second kind, ascending form:
for `0 ≤ k < 1`, `E(2√k / (1 + k)) = (2 E(k) - (1 - k²) K(k)) / (1 + k)`. -/
theorem legendreEc_two_mul_sqrt_div_one_add {k : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) :
    legendreEc (2 * √k / (1 + k)) =
      (2 * legendreEc k - (1 - k ^ 2) * legendreK k) / (1 + k) := by
  rcases hk₀.eq_or_lt with rfl | hk₀
  · simp only [sqrt_zero, mul_zero, zero_div, add_zero, legendreEc_zero, legendreK_zero]
    ring
  have hp : 0 < 1 + k := by linarith
  have hk : k ^ 2 < 1 := by nlinarith
  have hs : 0 < √k := sqrt_pos.2 hk₀
  have ht : 0 < 2 * √k / (1 + k) := by positivity
  have hsq := one_sub_sq_two_mul_sqrt_div_one_add hk₀.le
  have hlt := sq_two_mul_sqrt_div_one_add_lt_one hk₀.le hk₁.ne
  have hd : HasDerivAt (fun x : ℝ ↦ 2 * √x / (1 + x))
      ((1 - k) / (√k * (1 + k) ^ 2)) k := by
    apply HasDerivAt.congr_deriv (((hasDerivAt_sqrt hk₀.ne').const_mul 2).div
      ((hasDerivAt_id k).const_add 1) hp.ne')
    simp only [id_eq]
    field_simp
    nlinarith [sq_sqrt hk₀.le]
  have hleft := (hasDerivAt_legendreK ht.ne' hlt).comp k hd
  have hright := ((hasDerivAt_id k).const_add 1).mul (hasDerivAt_legendreK hk₀.ne' hk)
  have heq : (fun x : ℝ ↦ legendreK (2 * √x / (1 + x))) =ᶠ[𝓝 k]
      (fun x ↦ (1 + x) * legendreK x) := by
    filter_upwards [Ioo_mem_nhds hk₀ hk₁] with x hx
    exact legendreK_two_mul_sqrt_div_one_add hx.1.le hx.2
  have hderiv := hleft.unique (hright.congr_of_eventuallyEq heq)
  rw [legendreK_two_mul_sqrt_div_one_add hk₀.le hk₁, hsq] at hderiv
  have hnonzero : 1 - k ^ 2 ≠ 0 := by linarith
  simp only [id_eq] at hderiv
  field_simp at hderiv ⊢
  -- Clearing the modulus derivative denominators multiplies the desired identity by
  -- k * (1 - k ^ 2), which is nonzero on the current domain 0 < k < 1.
  apply mul_left_cancel₀ (mul_ne_zero hk₀.ne' hnonzero)
  linear_combination hderiv +
    (2 * (1 - k ^ 2) * (legendreEc k - (1 - k) * legendreK k)) * (sq_sqrt hk₀.le)

/-- **Landen's transformation** of the complete integral of the second kind, descending form:
for `k² < 1`, with `k' = √(1 - k²)` and `k₁ = (1 - k') / (1 + k')`,
`E(k) = (1 + k') E(k₁) - k' K(k)`. -/
theorem legendreEc_eq_one_add_mul_legendreEc {k : ℝ} (hk : k ^ 2 < 1) :
    legendreEc k = (1 + √(1 - k ^ 2)) *
      legendreEc ((1 - √(1 - k ^ 2)) / (1 + √(1 - k ^ 2))) -
        √(1 - k ^ 2) * legendreK k := by
  set c := √(1 - k ^ 2)
  have hc : 0 < c := sqrt_pos.2 (by linarith)
  have hc₁ : c ≤ 1 := sqrt_le_one.2 (by nlinarith)
  have hp : 0 < 1 + c := by linarith
  have hq₀ : 0 ≤ (1 - c) / (1 + c) := div_nonneg (by linarith) hp.le
  have hq₁ : (1 - c) / (1 + c) < 1 := (div_lt_one hp).2 (by linarith)
  have hE := legendreEc_two_mul_sqrt_div_one_add hq₀ hq₁
  have hK : legendreK k = (1 + (1 - c) / (1 + c)) *
      legendreK ((1 - c) / (1 + c)) := by
    simpa only [c] using legendreK_eq_one_add_mul_legendreK hk
  have harg : legendreEc (2 * √((1 - c) / (1 + c)) /
      (1 + (1 - c) / (1 + c))) = legendreEc k := by
    rw [two_mul_sqrt_div_one_add_eq_abs hk.le, legendreEc_abs]
  rw [harg] at hE
  field_simp at hE hK ⊢
  -- The ascending identities at (1 - c) / (1 + c) have denominator 1 + c.
  -- Multiply the target by this positive factor to combine the cleared identities.
  apply mul_left_cancel₀ hp.ne'
  linear_combination hE / 2 + c * hK

end TauCeti.Real
