/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.ModulusDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Legendre's relation

The complete elliptic integrals at complementary moduli satisfy
`E(k) K(k′) + E(k′) K(k) - K(k) K(k′) = π / 2`, where `k′ = √(1 - k²)`.
This identity relates the first and second kinds and determines the second kind at the
self-complementary modulus `1 / √2`.

The left side has derivative zero on `(0, 1)`. Its constant is evaluated at `k → 0⁺`:
the derivatives of `E` and `K` at zero give `E(k) - K(k) = o(k)`, while the elementary
bound on `K` gives `k K(k′) ≤ π / 2`. Thus no logarithmic expansion at modulus one is needed.

## References

* NIST *Digital Library of Mathematical Functions*, §19.7(i), equation 19.7.1,
  <https://dlmf.nist.gov/19.7.E1>.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter Set
open scoped Topology

private theorem hasDerivAt_legendre_relation {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    HasDerivAt (fun k : ℝ ↦
      legendreEc k * legendreK √(1 - k ^ 2) + legendreEc √(1 - k ^ 2) * legendreK k -
        legendreK k * legendreK √(1 - k ^ 2)) 0 k := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hs₀ : 0 < √(1 - k ^ 2) := sqrt_pos.2 (sub_pos.2 hk)
  have hs : (√(1 - k ^ 2)) ^ 2 = 1 - k ^ 2 := sq_sqrt (sub_pos.2 hk).le
  have hs₁ : (√(1 - k ^ 2)) ^ 2 < 1 := by rw [hs]; nlinarith
  have hd := (((hasDerivAt_id' k).pow 2).const_sub 1).sqrt (sub_pos.2 hk).ne'
  have hK := hasDerivAt_legendreK hk₀.ne' hk
  have hE := hasDerivAt_legendreEc hk₀.ne' hk
  have hKc := (hasDerivAt_legendreK hs₀.ne' hs₁).comp k hd
  have hEc := (hasDerivAt_legendreEc hs₀.ne' hs₁).comp k hd
  refine (((hE.mul hKc).add (hEc.mul hK)).sub (hK.mul hKc)).congr_deriv ?_
  simp only [Function.comp_apply, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one,
    mul_one, hs, sub_sub_cancel]
  field_simp
  rw [hs]
  ring

private theorem tendsto_legendreEc_sub_legendreK_mul_complement :
    Tendsto (fun k : ℝ ↦ (legendreEc k - legendreK k) * legendreK √(1 - k ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  have hquot : Tendsto (fun k : ℝ ↦ (legendreEc k - legendreK k) / k)
      (𝓝[>] 0) (𝓝 0) := by
    simpa [legendreEc_zero, legendreK_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (hasDerivAt_legendreEc_zero.sub hasDerivAt_legendreK_zero).tendsto_slope_zero_right
  have hbound : Tendsto (fun k : ℝ ↦ ‖(legendreEc k - legendreK k) / k‖ * (π / 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hquot.norm.mul_const (π / 2)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk' : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hs : (√(1 - k ^ 2)) ^ 2 = 1 - k ^ 2 := sq_sqrt (sub_pos.2 hk').le
  have hs₁ : (√(1 - k ^ 2)) ^ 2 < 1 := by rw [hs]; nlinarith [hk.1]
  have hK : k * legendreK √(1 - k ^ 2) ≤ π / 2 := by
    have h := legendreK_le_pi_div_two_div_sqrt hs₁
    rw [hs, sub_sub_cancel, sqrt_sq hk.1.le] at h
    simpa [mul_comm] using (le_div_iff₀ hk.1).mp h
  calc
    ‖(legendreEc k - legendreK k) * legendreK √(1 - k ^ 2)‖ =
        ‖(legendreEc k - legendreK k) / k‖ * (k * legendreK √(1 - k ^ 2)) := by
      rw [norm_mul, norm_div, Real.norm_of_nonneg hk.1.le,
        Real.norm_of_nonneg (legendreK_pos hs₁).le]
      field_simp [hk.1.ne']
    _ ≤ ‖(legendreEc k - legendreK k) / k‖ * (π / 2) :=
      mul_le_mul_of_nonneg_left hK (norm_nonneg _)

/-- **Legendre's relation** between the complete first and second elliptic integrals at
complementary moduli (DLMF 19.7.1). -/
theorem legendre_relation {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    legendreEc k * legendreK √(1 - k ^ 2) + legendreEc √(1 - k ^ 2) * legendreK k -
      legendreK k * legendreK √(1 - k ^ 2) = π / 2 := by
  let L := fun k : ℝ ↦
    legendreEc k * legendreK √(1 - k ^ 2) + legendreEc √(1 - k ^ 2) * legendreK k -
      legendreK k * legendreK √(1 - k ^ 2)
  have hconst : ∀ x ∈ Ioo (0 : ℝ) 1, L x = L k := by
    intro x hx
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
    · intro x hx
      exact (hasDerivAt_legendre_relation hx.1 hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hasDerivAt_legendre_relation hx.1 hx.2).deriv
    · exact hx
    · exact ⟨hk₀, hk₁⟩
  have hc : Tendsto (fun k : ℝ ↦ √(1 - k ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (by fun_prop : Continuous fun k : ℝ ↦ √(1 - k ^ 2)).tendsto 0
      |>.mono_left nhdsWithin_le_nhds
  have hE : Tendsto (fun k : ℝ ↦ legendreEc √(1 - k ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa [legendreEc_one, Function.comp_def] using (continuous_legendreEc.tendsto 1).comp hc
  have hK : Tendsto legendreK (𝓝[>] 0) (𝓝 (π / 2)) := by
    simpa [legendreK_zero] using
      hasDerivAt_legendreK_zero.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto L (𝓝[>] 0) (𝓝 (π / 2)) := by
    convert (hE.mul hK).add tendsto_legendreEc_sub_legendreK_mul_complement using 1
    · ext x
      dsimp [L]
      ring
    · simp
  apply tendsto_nhds_unique _ hlim
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact (hconst x hx).symm

/-- The complete second kind at the self-complementary modulus, expressed in terms of the
complete first kind. -/
theorem legendreEc_one_div_sqrt_two :
    legendreEc (1 / √2) = legendreK (1 / √2) / 2 + π / (4 * legendreK (1 / √2)) := by
  have hk₀ : (0 : ℝ) < 1 / √2 := by positivity
  have hsq : (1 / √2 : ℝ) ^ 2 = 1 / 2 := by simp
  have hk₁ : (1 / √2 : ℝ) < 1 := by nlinarith
  have hc : √(1 - (1 / √2 : ℝ) ^ 2) = 1 / √2 := by
    rw [hsq, show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, sqrt_inv]
    simp
  have h := legendre_relation hk₀ hk₁
  rw [hc] at h
  have hK := legendreK_pos (k := 1 / √2) (by rw [hsq]; norm_num)
  field_simp [hK.ne']
  linear_combination 4 * h

end TauCeti.Real
