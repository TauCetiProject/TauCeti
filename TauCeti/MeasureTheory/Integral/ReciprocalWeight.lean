/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Perspective
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A reciprocal-weighted convex integral comparison

For a finite measure `ν` and an almost everywhere positive function `g`, Jensen's inequality
with weight `1 / g` compares `∫ Φ(g) / g` with
`m * Φ (ν.real univ / m)`, where `m = ∫ 1 / g`. Monotonicity of `Φ` and of its perspective
then allow a lower bound on `ν.real univ` and an upper bound on `m` to be substituted.
The resulting inequality applies to a level surface with `g` the gradient norm. Empty
measures and zero denominators are included using the real division convention.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen,
  *The Pólya–Szegő inequality for smoothing rearrangements*, Theorem 5.8.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace ConvexOn

/-- A reciprocal-weighted Jensen comparison. A lower bound `P` on the measure of a level
surface and an upper bound `M` on its reciprocal-gradient integral yield a lower bound on
the convex gradient integral. Positivity of the reciprocal integral is derived when the
measure is nonzero, so the statement also includes empty levels and `M = 0`. -/
theorem mul_map_div_le_integral_div {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) {g : α → ℝ}
    (hg : ∀ᵐ x ∂ν, 0 < g x) (hi : Integrable (fun x ↦ (g x)⁻¹) ν)
    (hΦi : Integrable (fun x ↦ Φ (g x) / g x) ν) {P M : ℝ}
    (hP : 0 ≤ P) (hPν : P ≤ ν.real univ) (hM : (∫ x, (g x)⁻¹ ∂ν) ≤ M) :
    M * Φ (P / M) ≤ ∫ x, Φ (g x) / g x ∂ν := by
  by_cases hν : ν = 0
  · have hP0 : P = 0 := le_antisymm (by simpa [hν] using hPν) hP
    simp [hν, hP0, hΦ0]
  have : NeZero ν := ⟨hν⟩
  have hgn : ∀ᵐ x ∂ν, 0 ≤ (g x)⁻¹ := hg.mono fun x hx ↦ (inv_pos.mpr hx).le
  let m := ∫ x, (g x)⁻¹ ∂ν
  have hm : 0 < m := by
    refine lt_of_le_of_ne (integral_nonneg_of_ae hgn) ?_
    intro hm0
    have hz := (integral_eq_zero_iff_of_nonneg_ae hgn hi).mp hm0.symm
    obtain ⟨x, hx, hx0⟩ := (hg.and hz).exists
    exact (inv_pos.mpr hx).ne' hx0
  let μ := ν.withDensity (fun x ↦ ENNReal.ofReal (g x)⁻¹)
  have hd : AEMeasurable (fun x ↦ ENNReal.ofReal (g x)⁻¹) ν :=
    hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hgn).mpr hi)
  have hμm : μ.real univ = m := by
    rw [withDensity_real_apply', setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi hgn, ENNReal.toReal_ofReal hm.le]
  have : NeZero μ := ⟨fun h ↦ by simpa [h] using hμm.trans_ne hm.ne'⟩
  have hweight : (fun x ↦ (ENNReal.ofReal (g x)⁻¹).toReal * g x) =ᵐ[ν] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hg] with x hx
    simp [ENNReal.toReal_ofReal (inv_pos.mpr hx).le, hx.ne']
  have hμg : Integrable g μ := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (by simp)).mpr
    simpa only [smul_eq_mul] using (integrable_const (1 : ℝ)).congr hweight.symm
  have hμΦ : Integrable (fun x ↦ Φ (g x)) μ := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (by simp)).mpr
    refine hΦi.congr ?_
    filter_upwards [hg] with x hx
    simp [ENNReal.toReal_ofReal (inv_pos.mpr hx).le, div_eq_mul_inv, mul_comm]
  have hμint : ∫ x, g x ∂μ = ν.real univ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hd (by simp)]
    simpa only [smul_eq_mul, integral_const, smul_eq_mul, mul_one] using integral_congr_ae hweight
  have hμΦint : ∫ x, Φ (g x) ∂μ = ∫ x, Φ (g x) / g x ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hd (by simp)]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    simp [ENNReal.toReal_ofReal (inv_pos.mpr hx).le, smul_eq_mul, div_eq_mul_inv, mul_comm]
  -- Extending constantly to the left gives Jensen a continuous convex function on a closed set.
  have himage : (fun t : ℝ ↦ max t 0) '' univ = Ici 0 :=
    ext fun s ↦ ⟨fun ⟨_, _, h⟩ ↦ h ▸ le_max_right _ _, fun h ↦ ⟨s, trivial, max_eq_left h⟩⟩
  have hmax : ConvexOn ℝ univ (fun t : ℝ ↦ max t 0) :=
    (convexOn_id convex_univ).sup (convexOn_const 0 convex_univ)
  have hΦmax := ConvexOn.comp (himage ▸ hΦ) hmax (himage ▸ hΦm)
  have hc : ContinuousOn (fun t : ℝ ↦ Φ (max t 0)) univ := by
    simpa [Function.comp_def] using hΦmax.continuousOn_interior
  have hgμ : ∀ᵐ x ∂μ, 0 ≤ g x :=
    (withDensity_absolutelyContinuous ν _).ae_le (hg.mono fun _ hx ↦ hx.le)
  have hJ := hΦmax.map_average_le hc isClosed_univ (ae_of_all _ fun _ ↦ mem_univ _) hμg
    (hμΦ.congr (hgμ.mono fun x hx ↦ by simp [Function.comp_def, max_eq_left hx]))
  rw [average_eq, average_eq, hμm, hμint] at hJ
  have hJ' : m * Φ (ν.real univ / m) ≤ ∫ x, Φ (g x) / g x ∂ν := by
    have hnonneg : 0 ≤ m⁻¹ * ν.real univ := mul_nonneg (inv_nonneg.mpr hm.le) (measureReal_nonneg)
    simp only [smul_eq_mul, Function.comp_apply, max_eq_left hnonneg] at hJ
    have hright : (∫ x, Φ (max (g x) 0) ∂μ) = ∫ x, Φ (g x) ∂μ :=
      integral_congr_ae (hgμ.mono fun x hx ↦ by simp only [max_eq_left hx])
    rw [hright, hμΦint] at hJ
    rw [mul_comm m, div_eq_inv_mul]
    exact (le_div_iff₀ hm).mp (by simpa only [div_eq_inv_mul] using hJ)
  calc
    M * Φ (P / M) ≤ m * Φ (P / m) := hΦ.antitoneOn_mul_map_div hΦ0 hP hm
      (hm.trans_le hM) hM
    _ ≤ m * Φ (ν.real univ / m) := mul_le_mul_of_nonneg_left
      (hΦm (div_nonneg hP hm.le) (div_nonneg measureReal_nonneg hm.le)
        (div_le_div_of_nonneg_right hPν hm.le)) hm.le
    _ ≤ ∫ x, Φ (g x) / g x ∂ν := hJ'

end ConvexOn
