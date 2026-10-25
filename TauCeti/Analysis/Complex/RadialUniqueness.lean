/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import TauCeti.Analysis.Analytic.IsolatedZeros

/-!
# Radial limits determine a holomorphic function: the F. and M. Riesz uniqueness theorem

A bounded holomorphic function on a disc whose radial limits equal `a` on a set of angles of
positive measure is the constant `a`. More generally it suffices that the circle averages of
`log⁺ ‖f‖` stay bounded on circles whose radii accumulate at the radius of the disc, as they do
for the functions of bounded characteristic (the Nevanlinna class); for a nonzero such function
the set of angles at which its radial limit is `0` is null. Radial limits are taken along
`r ↦ circleMap c r θ` as `r` increases to the radius `R`, and the set of angles is an arbitrary
subset of `ℝ` of positive outer measure.

This is not a consequence of the identity principle: the boundary values say nothing about an
accumulation point of zeros inside the open disc. In the boundary theory of conformal maps it is
the uniqueness input showing that the preimage under a conformal map of a curve ending at a
boundary point ends at a single point of the circle, since otherwise the map would tend to that
boundary point along almost every radius ending in an arc of the circle.

## Main results

* `AnalyticOnNhd.le_circleAverage_log_norm` — Jensen's inequality from below: the circle average
  of `log ‖f‖` is at least `k * log r + log ‖τ‖`, where `k` is the order of `f` at the centre and
  `τ` its trailing coefficient there.
* `TauCeti.eqOn_zero_ball_of_tendsto_circleMap_of_frequently_circleAverage_posLog_le` — a function
  whose circle averages of `log⁺ ‖f‖` are bounded on circles with radii accumulating at `R`, and
  whose radial limit is `0` on a set of angles of positive measure, vanishes on the disc.
* `TauCeti.eqOn_const_ball_of_tendsto_circleMap` — a bounded holomorphic function with radial limit
  `a` on a set of angles of positive measure is the constant `a`.

## Implementation notes

Suppose `f` does not vanish identically. Jensen's formula bounds the circle averages of `log ‖f‖`
from below on circles near the boundary, and `log⁺ ‖f‖⁻¹ = log⁺ ‖f‖ - log ‖f‖`, so the averages of
`log⁺ ‖f‖⁻¹` stay bounded along a sequence of radii tending to `R`. On the angles with radial limit
`0`, which up to the countably many zeros of `f` on those circles form a set of positive measure in
one period, `log⁺ ‖f‖⁻¹` tends to `∞`, and Fatou's lemma makes the averages unbounded.

## References

* F. Riesz and M. Riesz, *Über die Randwerte einer analytischen Funktion*, Quatrième Congrès des
  Mathématiciens Scandinaves, Stockholm (1916), 27–44.
* P. L. Duren, *Theory of Hᵖ Spaces*, Chapter 2.
-/

public section

open Filter Metric MeasureTheory Set Topology
open Real
open scoped ENNReal

variable {f : ℂ → ℂ} {c : ℂ} {r R : ℝ}

/-- **Jensen's inequality from below.** If `f` is analytic on the closed disc of radius `|r|`
about `c`, with `r ≠ 0`, the circle average of `log ‖f‖` is at least `k * log r + log ‖τ‖`, where
`k` is the order of `f` at `c` and `τ` its trailing coefficient there.

This is Jensen's formula `MeromorphicOn.circleAverage_log_norm` with the contributions of the zeros
other than `c` dropped, each of which is nonnegative. -/
theorem AnalyticOnNhd.le_circleAverage_log_norm (hf : AnalyticOnNhd ℂ f (closedBall c |r|))
    (hr : r ≠ 0) :
    analyticOrderNatAt f c * Real.log r + Real.log ‖meromorphicTrailingCoeffAt f c‖ ≤
      circleAverage (fun z ↦ Real.log ‖f z‖) c r := by
  rw [hf.meromorphicOn.circleAverage_log_norm hr,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hf (by simp)]
  have hsum : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall c |r|) u : ℝ) *
      Real.log (r * ‖c - u‖⁻¹) := by
    refine finsum_nonneg fun u ↦ ?_
    by_cases hu : u ∈ closedBall c |r|
    · refine mul_nonneg (mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u) ?_
      rcases eq_or_ne u c with rfl | huc
      · simp
      · rw [mem_closedBall, dist_comm, dist_eq_norm] at hu
        have hpos : 0 < ‖c - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huc.symm)
        rw [← Real.log_abs, abs_mul, abs_inv, abs_norm, ← div_eq_mul_inv]
        exact Real.log_nonneg ((one_le_div hpos).2 hu)
    · simp [hu]
  have hord : ((((analyticOrderAt f c).map (Nat.cast : ℕ → ℤ)).untop₀ : ℤ) : ℝ) =
      analyticOrderNatAt f c := by
    unfold analyticOrderNatAt
    induction analyticOrderAt f c using ENat.recTopCoe <;> simp
  rw [hord]
  linarith

namespace TauCeti

/-- The angles at which `f` has a given radial limit form a `2π`-periodic set, so if they have
positive measure then so do those in one period `(0, 2π]`. -/
private lemma volume_setOf_tendsto_circleMap_inter_Ioc_ne_zero {l : Filter ℝ} {a : ℂ} {E : Set ℝ}
    (hE : volume E ≠ 0) (hlim : ∀ θ ∈ E, Tendsto (fun r ↦ f (circleMap c r θ)) l (𝓝 a)) :
    volume ({θ | Tendsto (fun r ↦ f (circleMap c r θ)) l (𝓝 a)} ∩ Ioc 0 (2 * π)) ≠ 0 := by
  intro h0
  refine hE (measure_mono_null (t := {θ | Tendsto (fun r ↦ f (circleMap c r θ)) l (𝓝 a)})
    (fun θ hθ ↦ hlim θ hθ) ?_)
  refine (isAddFundamentalDomain_Ioc two_pi_pos 0).measure_zero_of_invariant _
    (fun g ↦ ?_) (by simpa using h0)
  obtain ⟨g, k, rfl⟩ := g
  ext θ
  have hθ : ∀ r, circleMap c r (-(k * (2 * π)) + θ) = circleMap c r θ := fun r ↦ by
    rw [neg_add_eq_sub, ← zsmul_eq_mul]
    exact (periodic_circleMap c r).zsmul k |>.sub_eq θ
  simp [Set.mem_vadd_set_iff_neg_vadd_mem, AddSubgroup.vadd_def, hθ]

/-- On a circle where `f` is meromorphic, the integral of `log⁺ ‖f‖⁻¹` over one period is `2π`
times the difference of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`. -/
private lemma lintegral_ofReal_posLog_inv_norm_circleMap
    (hf : MeromorphicOn f (sphere c |r|)) :
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (log⁺ ‖f (circleMap c r θ)‖⁻¹) =
      ENNReal.ofReal (2 * π * (circleAverage (fun z ↦ log⁺ ‖f z‖) c r -
        circleAverage (fun z ↦ Real.log ‖f z‖) c r)) := by
  have hinv : (fun z ↦ log⁺ ‖f z‖⁻¹) = (fun z ↦ log⁺ ‖f z‖) - fun z ↦ Real.log ‖f z‖ := by
    funext z
    simp only [Pi.sub_apply]
    linarith [posLog_sub_posLog_inv (x := ‖f z‖)]
  have hint : CircleIntegrable (fun z ↦ log⁺ ‖f z‖⁻¹) c r := by
    rw [hinv]
    exact hf.circleIntegrable_posLog_norm.sub hf.circleIntegrable_log_norm
  rw [← circleAverage_sub hf.circleIntegrable_posLog_norm hf.circleIntegrable_log_norm, ← hinv,
    circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hint)
      (Eventually.of_forall fun θ ↦ posLog_nonneg)]

/-- **F. and M. Riesz uniqueness theorem.** Let `f` be holomorphic on the disc `ball c R`, with
circle averages of `log⁺ ‖f‖` at most `C` on circles about `c` whose radii accumulate at `R` from
below. If the radial limit of `f` is `0` at every angle of a set `E` of positive measure, then `f`
vanishes on the disc.

The bound holds for every function of bounded characteristic, in particular for every bounded
function (`TauCeti.eqOn_const_ball_of_tendsto_circleMap`). The radial limit at the angle `θ` is
taken along `r ↦ circleMap c r θ` as `r` increases to `R`. -/
theorem eqOn_zero_ball_of_tendsto_circleMap_of_frequently_circleAverage_posLog_le
    {C : ℝ} {E : Set ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hC : ∃ᶠ r in 𝓝[<] R, circleAverage (fun z ↦ log⁺ ‖f z‖) c r ≤ C)
    (hE : volume E ≠ 0)
    (hlim : ∀ θ ∈ E, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 0)) :
    EqOn f 0 (ball c R) := by
  by_contra hne
  obtain ⟨w, hw, hfw⟩ : ∃ w ∈ ball c R, f w ≠ 0 := by
    simpa [EqOn] using hne
  have hR : 0 < R := pos_of_mem_ball hw
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  -- By Jensen's inequality the averages of `log ‖f‖` are at least `L` on circles near the boundary.
  set L := analyticOrderNatAt f c * Real.log (R / 2) + Real.log ‖meromorphicTrailingCoeffAt f c‖
  have hlow : ∀ r ∈ Ioo (R / 2) R, L ≤ circleAverage (fun z ↦ Real.log ‖f z‖) c r := by
    intro r hr
    have hr0 : 0 < r := by linarith [hr.1]
    refine le_trans ?_ ((han.mono ?_).le_circleAverage_log_norm hr0.ne')
    · dsimp only [L]
      gcongr
      exact hr.1.le
    · rw [abs_of_pos hr0]
      exact closedBall_subset_ball hr.2
  -- Radii `ρ n` tending to `R` along which the averages of `log⁺ ‖f‖` are bounded by `C`.
  obtain ⟨ρ, hρlim, hρ⟩ := exists_seq_forall_of_frequently
    (hC.and_eventually (Ioo_mem_nhdsLT (half_lt_self hR)))
  have hsphere : ∀ n, sphere c |ρ n| ⊆ ball c R := fun n ↦ by
    rw [abs_of_pos (by linarith [(hρ n).2.1])]
    exact sphere_subset_ball (hρ n).2.2
  -- The angles in one period with radial limit `0`, minus the null set `N` of angles at which `f`
  -- vanishes on one of the circles, form a set `A` of positive measure.
  set N := ⋃ n, {θ : ℝ | f (circleMap c (ρ n) θ) = 0}
  have hN : volume N = 0 := by
    refine (countable_iUnion fun n ↦ ?_).measure_zero _
    refine ((finite_setOf_mem_and_eq_zero_of_isCompact han (convex_ball c R).isPreconnected hw
      hfw (isCompact_sphere c |ρ n|) (hsphere n)).countable.preimage_circleMap c (R := ρ n)
      (by linarith [(hρ n).2.1])).mono ?_
    exact fun θ hθ ↦ ⟨circleMap_mem_sphere' c (ρ n) θ, hθ⟩
  set A := ({θ | Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 0)} ∩ Ioc 0 (2 * π)) \ N
  have hA : volume A ≠ 0 := by
    rw [measure_sdiff_null hN]
    exact volume_setOf_tendsto_circleMap_inter_Ioc_ne_zero hE hlim
  -- On `A` the integrands `G n = log⁺ ‖f‖⁻¹` on the circles of radius `ρ n` tend to `⊤`.
  set G : ℕ → ℝ → ℝ≥0∞ := fun n θ ↦ ENNReal.ofReal (log⁺ ‖f (circleMap c (ρ n) θ)‖⁻¹)
  have hGmeas : ∀ n, Measurable (G n) := fun n ↦
    ENNReal.measurable_ofReal.comp (continuous_posLog.measurable.comp
      (((han.continuousOn.mono (hsphere n)).comp_continuous (continuous_circleMap c (ρ n))
        (circleMap_mem_sphere' c (ρ n))).norm.measurable.inv))
  have hGlim : ∀ θ ∈ A, liminf (fun n ↦ G n θ) atTop = ⊤ := by
    rintro θ ⟨⟨hθS, -⟩, hθN⟩
    have h0 : Tendsto (fun n ↦ ‖f (circleMap c (ρ n) θ)‖) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (hθS.comp hρlim).norm)
        (Eventually.of_forall fun n ↦ norm_pos_iff.2 fun h ↦ hθN (mem_iUnion.2 ⟨n, h⟩))
    exact (ENNReal.tendsto_ofReal_atTop.comp (tendsto_atTop_mono (fun x ↦ le_max_right _ _)
      (tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h0)))).liminf_eq
  -- Fatou's lemma then makes the integrals of `G n` unbounded, against the bound `2π (C - L)`.
  have hbound : ∀ n, ∫⁻ θ in A, G n θ ≤ ENNReal.ofReal (2 * π * (C - L)) := fun n ↦
    (lintegral_mono_set (sdiff_subset.trans inter_subset_right)).trans <| by
      rw [lintegral_ofReal_posLog_inv_norm_circleMap (han.mono (hsphere n)).meromorphicOn]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ two_pi_pos.le)
      linarith [(hρ n).1, hlow (ρ n) (hρ n).2]
  have htop : ∫⁻ θ in A, liminf (fun n ↦ G n θ) atTop = ⊤ := by
    refine lintegral_eq_top_of_measure_eq_top_ne_zero (Measurable.liminf hGmeas).aemeasurable ?_
    rwa [Measure.restrict_apply (measurableSet_eq_fun (Measurable.liminf hGmeas) measurable_const),
      inter_eq_right.2 fun θ hθ ↦ hGlim θ hθ]
  refine ENNReal.ofReal_ne_top (r := 2 * π * (C - L)) (top_le_iff.1 ?_)
  calc ⊤ = ∫⁻ θ in A, liminf (fun n ↦ G n θ) atTop := htop.symm
    _ ≤ liminf (fun n ↦ ∫⁻ θ in A, G n θ) atTop := lintegral_liminf_le hGmeas
    _ ≤ ENNReal.ofReal (2 * π * (C - L)) :=
      liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- **F. and M. Riesz uniqueness theorem, bounded form.** A bounded holomorphic function on the
disc `ball c R` whose radial limit is `a` at every angle of a set of positive measure is the
constant `a`. The radial limit at the angle `θ` is taken along `r ↦ circleMap c r θ` as `r`
increases to `R`. -/
theorem eqOn_const_ball_of_tendsto_circleMap {a : ℂ} {M : ℝ} {E : Set ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M)
    (hE : volume E ≠ 0)
    (hlim : ∀ θ ∈ E, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 a)) :
    EqOn f (fun _ ↦ a) (ball c R) := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.2 hR]
  have hg : DifferentiableOn ℂ (fun z ↦ f z - a) (ball c R) := hf.sub_const a
  -- On every circle inside the disc, `log⁺ ‖f - a‖` is at most `log⁺ (M + ‖a‖)`.
  have hC : ∃ᶠ r in 𝓝[<] R, circleAverage (fun z ↦ log⁺ ‖f z - a‖) c r ≤ log⁺ (M + ‖a‖) := by
    refine Eventually.frequently ?_
    filter_upwards [Ioo_mem_nhdsLT hR] with r hr
    have hsphere : sphere c |r| ⊆ ball c R := by
      rw [abs_of_pos hr.1]
      exact sphere_subset_ball hr.2
    refine circleAverage_mono_on_of_le_circle
      ((hg.analyticOnNhd isOpen_ball).mono hsphere).meromorphicOn.circleIntegrable_posLog_norm
      fun z hz ↦ posLog_le_posLog (by linarith [norm_nonneg (f z - a)]) ?_
    exact (norm_sub_le _ _).trans (by linarith [hM z (hsphere hz)])
  intro z hz
  exact sub_eq_zero.1 <| eqOn_zero_ball_of_tendsto_circleMap_of_frequently_circleAverage_posLog_le
    hg hC hE (fun θ hθ ↦ by simpa using (hlim θ hθ).sub_const a) hz

end TauCeti
