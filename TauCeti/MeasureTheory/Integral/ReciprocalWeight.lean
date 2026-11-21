/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Perspective
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import TauCeti.Analysis.Convex.Continuous
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.Probability.Density

/-!
# A reciprocal-weighted convex integral comparison

For a finite measure `ν` and an almost everywhere positive function `g`, Jensen's inequality
with weight `1 / g` compares `∫ Φ(g) / g` with
`m * Φ (ν.real univ / m)`, where `m = ∫ 1 / g`. Monotonicity of `Φ` and of its perspective
then allow a lower bound on `ν.real univ` and an upper bound on `m` to be substituted.
The resulting inequality applies to a level surface with `g` the gradient norm. Empty
measures and zero denominators are included using the real division convention.

`ConvexOn.lintegral_ofReal_div_le_of_ae_eq_const` packages the `lintegral` two-measure
comparison when the first weight is almost everywhere constant.

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
  have hiae : AEMeasurable (fun x ↦ (g x)⁻¹) ν := hi.aestronglyMeasurable.aemeasurable
  let μ := ν.withDensity (fun x ↦ ENNReal.ofReal (g x)⁻¹)
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hgn).mpr hi)
  have hμm : μ.real univ = m := by
    simpa using TauCeti.Probability.integral_withDensity_ofReal hiae hgn (fun _ ↦ (1 : ℝ))
  have : NeZero μ := ⟨fun h ↦ by simpa [h] using hμm.trans_ne hm.ne'⟩
  have hweight : (fun x ↦ g x / g x) =ᵐ[ν] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hg] with x hx using div_self hx.ne'
  have hdiv (f : α → ℝ) : (fun x ↦ (g x)⁻¹ • f x) = fun x ↦ f x / g x := by
    ext x
    rw [smul_eq_mul, inv_mul_eq_div]
  have hμg : Integrable g μ := by
    rw [TauCeti.Probability.integrable_withDensity_ofReal_iff hiae hgn, hdiv]
    exact (integrable_const (1 : ℝ)).congr hweight.symm
  have hμΦ : Integrable (fun x ↦ Φ (g x)) μ := by
    rw [TauCeti.Probability.integrable_withDensity_ofReal_iff hiae hgn, hdiv]
    exact hΦi
  have hμint : ∫ x, g x ∂μ = ν.real univ := by
    rw [TauCeti.Probability.integral_withDensity_ofReal hiae hgn, hdiv]
    simpa only [integral_const, smul_eq_mul, mul_one] using integral_congr_ae hweight
  have hμΦint : ∫ x, Φ (g x) ∂μ = ∫ x, Φ (g x) / g x ∂ν := by
    rw [TauCeti.Probability.integral_withDensity_ofReal hiae hgn, hdiv]
  have hgμ : ∀ᵐ x ∂μ, 0 ≤ g x :=
    (withDensity_absolutelyContinuous ν _).ae_le (hg.mono fun _ hx ↦ hx.le)
  have hJ := hΦ.map_average_le_of_monotoneOn_Ici hΦm hgμ hμg hμΦ
  rw [average_eq, average_eq, hμm, hμint, hμΦint] at hJ
  have hJ' : m * Φ (ν.real univ / m) ≤ ∫ x, Φ (g x) / g x ∂ν := by
    rw [mul_comm m, div_eq_inv_mul]
    exact (le_div_iff₀ hm).mp (by simpa only [smul_eq_mul, div_eq_inv_mul] using hJ)
  calc
    M * Φ (P / M) ≤ m * Φ (P / m) := hΦ.antitoneOn_mul_map_div hΦ0 hP hm
      (hm.trans_le hM) hM
    _ ≤ m * Φ (ν.real univ / m) := mul_le_mul_of_nonneg_left
      (hΦm (div_nonneg hP hm.le) (div_nonneg measureReal_nonneg hm.le)
        (div_le_div_of_nonneg_right hPν hm.le)) hm.le
    _ ≤ ∫ x, Φ (g x) / g x ∂ν := hJ'

/-- A `lintegral` reciprocal-weighted comparison between two measures `μ` and `ν` (`ν` finite),
when `g₁` is `μ`-almost everywhere constant and positive, `g₂` is `ν`-almost everywhere measurable
and positive, `μ univ ≤ ν univ`, and
`∫⁻ y, ENNReal.ofReal (g₂ y)⁻¹ ∂ν ≤ ∫⁻ x, ENNReal.ofReal (g₁ x)⁻¹ ∂μ < ∞`. -/
theorem lintegral_ofReal_div_le_of_ae_eq_const {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν]
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {g₁ : α → ℝ} {g₂ : β → ℝ} (hg₁_pos : ∀ᵐ x ∂μ, 0 < g₁ x)
    (hg₁_const : ∃ γ : ℝ, ∀ᵐ x ∂μ, g₁ x = γ)
    (hg₂_m : AEMeasurable g₂ ν) (hg₂_pos : ∀ᵐ y ∂ν, 0 < g₂ y)
    (hμν : μ univ ≤ ν univ)
    (hinv : (∫⁻ y, ENNReal.ofReal (g₂ y)⁻¹ ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (g₁ x)⁻¹ ∂μ)
    (hinv_fin : (∫⁻ x, ENNReal.ofReal (g₁ x)⁻¹ ∂μ) < ∞) :
    (∫⁻ x, ENNReal.ofReal (Φ (g₁ x) / g₁ x) ∂μ) ≤
      ∫⁻ y, ENNReal.ofReal (Φ (g₂ y) / g₂ y) ∂ν := by
  by_cases hΦ_top : (∫⁻ y, ENNReal.ofReal (Φ (g₂ y) / g₂ y) ∂ν) = ∞
  · exact hΦ_top ▸ le_top
  have hΦ_fin : (∫⁻ y, ENNReal.ofReal (Φ (g₂ y) / g₂ y) ∂ν) < ∞ := lt_top_iff_ne_top.2 hΦ_top
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  have : NeZero μ := ⟨hμ0⟩
  have hμ_fin : μ univ < ∞ := hμν.trans_lt (measure_lt_top ν univ)
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  obtain ⟨γ, hγ_ae⟩ := hg₁_const
  obtain ⟨x₀, hx₀_pos, hx₀_eq⟩ := (hg₁_pos.and hγ_ae).exists
  have hγ : 0 < γ := hx₀_eq ▸ hx₀_pos
  set P := (μ univ).toReal
  set M := (∫⁻ x, ENNReal.ofReal (g₁ x)⁻¹ ∂μ).toReal
  have hP_pos : 0 < P := ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hμ0) hμ_fin.ne
  have hM_eq : M = P / γ := by
    have hm : (∫⁻ x, ENNReal.ofReal (g₁ x)⁻¹ ∂μ) = ENNReal.ofReal γ⁻¹ * μ univ :=
      (lintegral_congr_ae (hγ_ae.mono fun _ hx ↦ by rw [hx])).trans
        (by rw [lintegral_const, mul_comm])
    simp [M, P, hm, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le), inv_mul_eq_div]
  have hlhs_eq : (∫⁻ x, ENNReal.ofReal (Φ (g₁ x) / g₁ x) ∂μ) = ENNReal.ofReal (M * Φ (P / M)) := by
    have hc : (∫⁻ x, ENNReal.ofReal (Φ (g₁ x) / g₁ x) ∂μ) = ENNReal.ofReal (Φ γ / γ) * μ univ :=
      (lintegral_congr_ae (hγ_ae.mono fun _ hx ↦ by rw [hx])).trans
        (by rw [lintegral_const, mul_comm])
    have hPM : P / M = γ := by rw [hM_eq, div_div_cancel₀ hP_pos.ne']
    rw [hc, hPM, hM_eq, ← ENNReal.ofReal_toReal hμ_fin.ne,
      ← ENNReal.ofReal_mul (div_nonneg (hΦ_nn γ hγ.le) hγ.le)]
    congr 1; ring
  have hg₂_inv_nn : ∀ᵐ y ∂ν, 0 ≤ (g₂ y)⁻¹ := hg₂_pos.mono fun _ hy ↦ (inv_pos.mpr hy).le
  have hinv_int : Integrable (fun y ↦ (g₂ y)⁻¹) ν :=
    ⟨hg₂_m.inv.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hg₂_inv_nn).2 (hinv.trans_lt hinv_fin)⟩
  have hΦ_cont : Continuous fun s : ℝ ↦ Φ (max s 0) :=
    (hΦ.continuousOn_Ici_of_monotoneOn hΦm).comp_continuous
      (continuous_id.max continuous_const) fun _ ↦ le_max_right _ _
  have hΦg_ae : AEMeasurable (fun y ↦ Φ (g₂ y)) ν :=
    (hΦ_cont.measurable.comp_aemeasurable hg₂_m).congr
      (hg₂_pos.mono fun _ hy ↦ by simp only [Function.comp_apply, max_eq_left hy.le])
  have hΦ_nn_ae : ∀ᵐ y ∂ν, 0 ≤ Φ (g₂ y) / g₂ y :=
    hg₂_pos.mono fun _ hy ↦ div_nonneg (hΦ_nn _ hy.le) hy.le
  have hΦ_int : Integrable (fun y ↦ Φ (g₂ y) / g₂ y) ν :=
    ⟨(hΦg_ae.div hg₂_m).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hΦ_nn_ae).2 hΦ_fin⟩
  have hM_bound : (∫ y, (g₂ y)⁻¹ ∂ν) ≤ M := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hinv_fin.ne,
      ofReal_integral_eq_lintegral_ofReal hinv_int hg₂_inv_nn]
    exact hinv
  have hPν : P ≤ ν.real univ := by
    rw [measureReal_def]; exact ENNReal.toReal_mono (measure_ne_top ν univ) hμν
  rw [hlhs_eq, ← ofReal_integral_eq_lintegral_ofReal hΦ_int hΦ_nn_ae]
  exact ENNReal.ofReal_le_ofReal
    (hΦ.mul_map_div_le_integral_div hΦm hΦ0 hg₂_pos hinv_int hΦ_int hP_pos.le hPν hM_bound)

end ConvexOn
