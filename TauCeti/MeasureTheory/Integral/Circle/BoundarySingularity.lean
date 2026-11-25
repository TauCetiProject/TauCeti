/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Concentric circles approaching integrable singularities on an outer circle

Let `f` be continuous on the closed annulus `ρ ≤ |z - c| ≤ r` (`0 < ρ`) except at finitely many
points `w` of the outer circle, near each of which `f(z) = O(|z - w| ^ (σ - 1))` inside the disc,
for some `σ > 0`. Then the restrictions `θ ↦ f(c + s e^{iθ})` of `f` to the circles of radius
`s ∈ [ρ, r)` about `c` have a common integrable bound on `[0, 2π]`
(`TauCeti.exists_intervalIntegrable_bound_norm_circleMap`). Away from the exceptional points `f` is
bounded on the annulus. Near an exceptional point `w`, the distance from `c + s e^{iθ}` to `w` is at
least `ρ |sin ((θ - arg (w - c)) / 2)|` (`TauCeti.norm_circleMap_sub_rpow_le`), and
`|sin| ^ (σ - 1)` is integrable for `σ > 0` (`TauCeti.intervalIntegrable_abs_sin_rpow`).

By dominated convergence, the Fourier coefficients on `[0, 2π]` of these restrictions tend to those
of the restriction of `f` to the outer circle as `s → r⁻`
(`TauCeti.tendsto_fourierCoeffOn_circleMap`), although `f` need not be continuous, nor even
bounded, there. This is how Laurent coefficients are extracted on a circle that carries integrable
singularities, in Darboux's method (`TauCeti.Analysis.Complex.Laurent.Darboux`).
-/

public section

open Complex Set Metric Filter Asymptotics MeasureTheory
open scoped Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The restrictions of `f` to the circles of radius `s ∈ [ρ, r)` about `c` admit a common
integrable bound, when `f` is continuous on the closed annulus `ρ ≤ |z - c| ≤ r` except at finitely
many points `w` of the outer circle, near each of which `f = O(‖z - w‖ ^ (σ - 1))` inside the disc
for some `σ > 0`. -/
theorem exists_intervalIntegrable_bound_norm_circleMap {f : ℂ → E} {c : ℂ} {ρ r : ℝ}
    (hρ : 0 < ρ) {S : Set ℂ} (hSfin : S.Finite) (hS : S ⊆ sphere c r)
    (hc : ContinuousOn f ((closedBall c r \ ball c ρ) \ S))
    (hO : ∀ w ∈ S, ∃ σ > (0 : ℝ), f =O[𝓝[ball c r] w] fun z ↦ ‖z - w‖ ^ (σ - 1)) :
    ∃ bound : ℝ → ℝ, IntervalIntegrable bound volume 0 (2 * π) ∧
      ∀ s ∈ Ico ρ r, ∀ᵐ θ : ℝ, ‖f (circleMap c s θ)‖ ≤ bound θ := by
  -- Near each exceptional point, lower the exponent to some `q ∈ (-1, 0]`.
  have hloc : ∀ w ∈ S, ∃ C δ q : ℝ, 0 ≤ C ∧ 0 < δ ∧ -1 < q ∧ q ≤ 0 ∧
      ∀ z ∈ ball c r, ‖z - w‖ < δ → ‖f z‖ ≤ C * ‖z - w‖ ^ q := fun w hw ↦ by
    obtain ⟨σ, hσ, hσO⟩ := hO w hw
    obtain ⟨C, hC, hCO⟩ := (hσO.nhdsWithin_norm_sub_rpow_of_le
      (fun h ↦ (mem_ball.1 h).ne (mem_sphere.1 (hS hw))) (min_le_left _ 0)).exists_pos
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.1 hCO.bound
    refine ⟨C, δ, min (σ - 1) 0, hC.le, hδ, lt_min (by linarith) (by norm_num), min_le_right _ _,
      fun z hz hzw ↦ ?_⟩
    simpa only [mem_ofPred_eq, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
      hδb ⟨mem_ball_iff_norm.2 hzw, hz⟩
  choose! C δ q hC hδ hq1 hq0 hb using hloc
  -- Away from the singular points, `f` is bounded by some `M` on the closed annulus.
  obtain ⟨M, hM⟩ := (((isCompact_closedBall c r).diff isOpen_ball).diff
    (isOpen_biUnion fun w _ ↦ isOpen_ball (x := w) (ε := δ w))).exists_bound_of_continuousOn
    (hc.mono fun z hz ↦ ⟨hz.1, fun hzS ↦ hz.2 (mem_biUnion hzS (mem_ball_self (hδ z hzS)))⟩)
  set φ : ℂ → ℝ → ℝ := fun w θ ↦ C w * ρ ^ q w * |Real.sin ((θ - arg (w - c)) / 2)| ^ q w
  have hφ : ∀ w ∈ hSfin.toFinset, ∀ θ, 0 ≤ φ w θ := fun w hw θ ↦ by
    have := hC w (hSfin.mem_toFinset.1 hw)
    positivity
  refine ⟨fun θ ↦ max M 0 + ∑ w ∈ hSfin.toFinset, φ w θ, intervalIntegrable_const.add ?_,
    fun s hs ↦ ?_⟩
  · rw [← Finset.sum_fn]
    refine IntervalIntegrable.sum _ fun w hw ↦ IntervalIntegrable.const_mul ?_ _
    -- Rescale `x ↦ |sin x| ^ q` to `θ ↦ |sin ((θ - arg (w - c)) / 2)| ^ q`.
    have h := ((intervalIntegrable_abs_sin_rpow (hq1 w (hSfin.mem_toFinset.1 hw))
      ((0 - arg (w - c)) / 2) ((2 * π - arg (w - c)) / 2)).comp_mul_left
      (c := 1 / 2)).comp_sub_right (arg (w - c))
    convert h using 2 <;> ring_nf
  -- Off the null set of angles `θ` where one of the sines vanishes, the bound holds pointwise.
  have hsin : ∀ᵐ θ : ℝ, ∀ w ∈ S, Real.sin ((θ - arg (w - c)) / 2) ≠ 0 := by
    refine (eventually_all_finite hSfin).2 fun w _ ↦ measure_mono_null
      (t := range fun k : ℤ ↦ 2 * k * π + arg (w - c)) (fun θ hθ ↦ ?_)
      ((countable_range _).measure_zero _)
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 (not_not.1 hθ)
    exact ⟨k, by linarith⟩
  filter_upwards [hsin] with θ hθ
  have hd := norm_circleMap_sub_center c (hρ.le.trans hs.1) θ
  by_cases hz : ∃ w ∈ S, circleMap c s θ ∈ ball w (δ w)
  · obtain ⟨w, hw, hzw⟩ := hz
    refine le_add_of_nonneg_of_le (le_max_right _ _) (le_trans ?_
      (Finset.single_le_sum (f := (φ · θ)) (fun w hw ↦ hφ w hw θ) (hSfin.mem_toFinset.2 hw)))
    refine (hb w hw _ (mem_ball_iff_norm.2 (hd.trans_lt hs.2)) (mem_ball_iff_norm.1 hzw)).trans ?_
    simp only [φ, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_circleMap_sub_rpow_le hρ hs.1 (hq0 w hw) (hθ w hw))
      (hC w hw)
  · refine le_add_of_le_of_nonneg ((hM _ ⟨circleMap_mem_closedBall_diff_ball hρ.le
      (Ico_subset_Icc_self hs) θ, fun h ↦ hz ?_⟩).trans
      (le_max_left _ _)) (Finset.sum_nonneg fun w hw ↦ hφ w hw θ)
    simpa only [mem_iUnion₂, exists_prop] using h

/-- Under the hypotheses of `exists_intervalIntegrable_bound_norm_circleMap`, with `ρ < r`, the
Fourier coefficients on `[0, 2π]` of the restrictions of `f` to the circles of radius `s` about `c`
tend to those of its restriction to the outer circle as `s → r⁻`. -/
theorem tendsto_fourierCoeffOn_circleMap [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) {S : Set ℂ} (hSfin : S.Finite) (hS : S ⊆ sphere c r)
    (hc : ContinuousOn f ((closedBall c r \ ball c ρ) \ S))
    (hO : ∀ w ∈ S, ∃ σ > (0 : ℝ), f =O[𝓝[ball c r] w] fun z ↦ ‖z - w‖ ^ (σ - 1)) (n : ℤ) :
    Tendsto (fun s ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ f (circleMap c s θ)) n) (𝓝[<] r)
      (𝓝 (fourierCoeffOn Real.two_pi_pos (fun θ ↦ f (circleMap c r θ)) n)) := by
  obtain ⟨bound, hbound_int, hbound⟩ :=
    exists_intervalIntegrable_bound_norm_circleMap hρ hSfin hS hc hO
  have hmem (s θ : ℝ) (hs : s ∈ Icc ρ r) (hsr : s < r ∨ circleMap c s θ ∉ S) :
      circleMap c s θ ∈ (closedBall c r \ ball c ρ) \ S := by
    refine ⟨circleMap_mem_closedBall_diff_ball hρ.le hs θ, hsr.elim (fun hsr h ↦ ?_) id⟩
    exact ((norm_circleMap_sub_center c (hρ.le.trans hs.1) θ).symm.trans
      (mem_sphere_iff_norm.1 (hS h))).not_lt hsr
  simp only [fourierCoeffOn_eq_integral _ _ Real.two_pi_pos]
  -- Dominated convergence, with the common bound and the continuity of `f` off `S`.
  refine Tendsto.const_smul (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    bound ?_ ?_ hbound_int ?_) _
  · filter_upwards [Ioo_mem_nhdsLT hρr] with s hs
    exact (((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).smul
      (hc.comp_continuous (continuous_circleMap c s) fun θ ↦
        hmem s θ (Ioo_subset_Icc_self hs) (Or.inl hs.2))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT hρr] with s hs
    filter_upwards [hbound s (Ioo_subset_Ico_self hs)] with θ hθ _
    rwa [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1
      ((hSfin.countable.preimage_circleMap c (hρ.trans hρr).ne').measure_zero _)] with θ hθ _
    refine Tendsto.const_smul (((hc _ (hmem r θ ⟨hρr.le, le_rfl⟩ (Or.inr hθ))).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩))) _
    · exact ((continuous_circleMap_uncurry c).comp
        (Continuous.prodMk_left θ)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hρr] with s hs
      exact hmem s θ (Ioo_subset_Icc_self hs) (Or.inl hs.2)

end TauCeti
