/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Holomorphy and differential recursion of polylogarithms on the cut plane

Every principal polylogarithm `TauCeti.Polylog.polylog n` (`n : ℤ`) is complex analytic on the
cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)` and satisfies the Euler differential
recursion `z * deriv (polylog (n + 1)) z = polylog n z` together with the recursive radial-integral
identity `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`.

These results provide the principal single-valued branch of the polylogarithm tower off `[1, ∞)`
and the differential equation `(d/dz) Li_{n+1}(z) = Li_n(z) / z` (`z ≠ 0`) governing coherent
analytic continuation, monodromy, and functional equations of higher polylogarithms.

## Main declarations

* `TauCeti.Polylog.analyticOnNhd_polylog` and `TauCeti.Polylog.analyticAt_polylog`: `polylog n` is
  complex analytic on `{z : ℂ | 1 - z ∈ Complex.slitPlane}` for every `n : ℤ`.
* `TauCeti.Polylog.differentiableOn_polylog`, `TauCeti.Polylog.differentiableAt_polylog`,
  `TauCeti.Polylog.continuousOn_polylog`, and `TauCeti.Polylog.continuousAt_polylog`: complex
  differentiability and continuity on the cut plane.
* `TauCeti.Polylog.hasDerivAt_polylog_one`, `TauCeti.Polylog.deriv_polylog_one`,
  `TauCeti.Polylog.hasDerivAt_polylog_nat_add_two`, and
  `TauCeti.Polylog.deriv_polylog_nat_add_two`: derivatives of weights `1` and `k + 2` on the cut
  plane.
* `TauCeti.Polylog.mul_deriv_polylog_add_one`: the Euler differential recursion
  `z * deriv (polylog (n + 1)) z = polylog n z` for all `n : ℤ` and `1 - z ∈ Complex.slitPlane`,
  including `z = 0`.
* `TauCeti.Polylog.hasDerivAt_polylog_add_one` and `TauCeti.Polylog.deriv_polylog_add_one`: the
  quotient derivative `polylog n z / z` at nonzero points of the cut plane.
* `TauCeti.Polylog.intervalIntegrable_polylog_mul_div` and
  `TauCeti.Polylog.polylog_add_one_eq_integral`: the recursive radial-integral identity
  `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t` on the cut plane.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (2)–(3), p. 50.
* Alexander B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology*,
  Advances in Mathematics 114 (1995), §1.0, (1.1), p. 201.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.Polylog

/-- On the cut plane, `polylog 1` has complex derivative `(1 - z)⁻¹`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) (1 - z)⁻¹ z := by
  have hd := (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).clog hz).neg
  exact (hd.congr_of_eventuallyEq (Eventually.of_forall polylog_one)).congr_deriv
    (by simp [div_eq_mul_inv])

/-- On the cut plane, `deriv (polylog 1) z = (1 - z)⁻¹`. -/
theorem deriv_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog 1) z = (1 - z)⁻¹ :=
  (hasDerivAt_polylog_one hz).deriv

/-- For every `k : ℕ` and `z` in the cut plane, `t ↦ (-log t) ^ k / (1 - t z)` is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_neg_log_pow_div_one_sub_mul (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 := by
  obtain ⟨δ, hδ, hδz⟩ := exists_le_norm_one_sub_ofReal_mul isCompact_singleton
    (singleton_subset_iff.mpr hz)
  refine ((TauCeti.intervalIntegrable_log_pow k).norm.const_mul δ⁻¹).mono_fun'
    (by fun_prop : Measurable _).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht ↦ ?_)
  rw [uIoc_of_le zero_le_one] at ht
  dsimp only
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs, abs_pow,
    div_eq_inv_mul]
  gcongr
  exact hδz z (mem_singleton z) t (Ioc_subset_Icc_self ht)

/-- Integral representation for the complex derivative of `polylog (k + 2)` on the cut plane. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  have hopen : IsOpen {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  obtain ⟨r, hr, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hz)
  obtain ⟨δ, hδ, hδball⟩ :=
    exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z r) hball
  set F : ℂ → ℝ → ℂ := fun x t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * x)) / (t : ℂ)
  set F' : ℂ → ℝ → ℂ := fun x t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * x)
  have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := closedBall z r) (bound := fun t : ℝ ↦ δ⁻¹ * ‖Real.log t ^ k‖)
    (closedBall_mem_nhds z hr)
    (Eventually.of_forall fun x ↦ (by fun_prop : Measurable (F x)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z)
    (by fun_prop : Measurable (F' z)).aestronglyMeasurable
    ?_ ((TauCeti.intervalIntegrable_log_pow k).norm.const_mul δ⁻¹) ?_
  · have hd := hparam.2.const_mul (Nat.factorial k : ℂ)⁻¹
    have hfn : (fun x : ℂ ↦ (Nat.factorial k : ℂ)⁻¹ * ∫ t : ℝ in 0..1, F x t) =
        polylog (k + 2 : ℕ) :=
      funext fun x ↦ (polylog_nat_add_two k x).symm
    rwa [hfn] at hd
  · refine ae_of_all _ fun t ht x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    dsimp only [F']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs, abs_pow,
      div_eq_inv_mul]
    gcongr
    exact hδball x hx t (Ioc_subset_Icc_self ht)
  · refine ae_of_all _ fun t ht x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have htx : 1 - (t : ℂ) * x ∈ Complex.slitPlane := by
      simpa [mul_comm] using
        Complex.one_sub_mul_ofReal_mem_slitPlane (hball hx) (Ioc_subset_Icc_self ht)
    have hlog : HasDerivAt (fun w : ℂ ↦ -Complex.log (1 - (t : ℂ) * w))
        ((t : ℂ) / (1 - (t : ℂ) * x)) x := by
      have hd := (((hasDerivAt_const x (1 : ℂ)).sub
        ((hasDerivAt_id x).const_mul (t : ℂ))).clog htx).neg
      exact hd.congr_deriv (by simp [div_eq_mul_inv])
    have hmul := (hlog.const_mul (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)
    refine hmul.congr_deriv ?_
    dsimp only [F']
    field_simp [ht0]

/-- Integral formula for `deriv (polylog (k + 2)) z` on the cut plane. -/
theorem deriv_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog (k + 2 : ℕ)) z =
      (Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z) :=
  (hasDerivAt_polylog_nat_add_two k hz).deriv

/-- Every integer-weight polylogarithm is complex analytic on the cut plane
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  have hopen : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  have hnot1 : {z : ℂ | 1 - z ∈ Complex.slitPlane} ⊆ {z : ℂ | z ≠ 1} := by
    rintro z hz rfl
    simp at hz
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (analyticOnNhd_polylog_neg_nat 0).mono hnot1
    · refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hopen
      exact (hasDerivAt_polylog_one hz).differentiableAt.differentiableWithinAt
    · refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hopen
      exact (hasDerivAt_polylog_nat_add_two k hz).differentiableAt.differentiableWithinAt
  | negSucc r =>
    simpa [Int.negSucc_eq] using (analyticOnNhd_polylog_neg_nat (r + 1)).mono hnot1

/-- `polylog n` is complex analytic at every point of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- `polylog n` is complex differentiable at every point of
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z :=
  (analyticAt_polylog n hz).differentiableAt

/-- `polylog n` is complex differentiable on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ (differentiableAt_polylog n hz).differentiableWithinAt

/-- `polylog n` is continuous at every point of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem continuousAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousAt (polylog n) z :=
  (analyticAt_polylog n hz).continuousAt

/-- `polylog n` is continuous on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem continuousOn_polylog (n : ℤ) :
    ContinuousOn (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (analyticOnNhd_polylog n).continuousOn

/-- The Euler differential recursion `z * deriv (polylog (n + 1)) z = polylog n z` holds for every
integer weight `n` on the entire cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, including at
`z = 0`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  have han₁ : AnalyticOnNhd ℂ (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w)
      {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    fun w hw ↦ analyticAt_id.mul (analyticAt_polylog (n + 1) hw).deriv
  have han₂ : AnalyticOnNhd ℂ (polylog n) {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    analyticOnNhd_polylog n
  have h0 : (0 : ℂ) ∈ {w : ℂ | 1 - w ∈ Complex.slitPlane} := by
    simp [Complex.one_mem_slitPlane]
  have hstar : StarConvex ℝ (0 : ℂ) {w : ℂ | 1 - w ∈ Complex.slitPlane} := by
    intro w hw a b _ hb hab
    simpa [Complex.real_smul, mul_comm] using
      Complex.one_sub_mul_ofReal_mem_slitPlane hw ⟨hb, by linarith⟩
  have hconn : IsPreconnected {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    (hstar.isPathConnected h0).isConnected.isPreconnected
  have hev : (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w) =ᶠ[𝓝 (0 : ℂ)] polylog n := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    rw [mem_ball_zero_iff] at hw
    rw [deriv_polylog_add_one_tsum n hw, ← tsum_mul_left, polylog_eq_tsum n hw]
    refine tsum_congr fun k ↦ ?_
    rw [pow_succ', mul_div_assoc']
  exact han₁.eqOn_of_preconnected_of_eventuallyEq han₂ hconn h0 hev hz

/-- At any nonzero point of the cut plane, `deriv (polylog (n + 1)) z = polylog n z / z`. -/
theorem deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z := by
  rw [← mul_deriv_polylog_add_one n hz, mul_div_cancel_left₀ _ hz0]

/-- At any nonzero point of the cut plane, `polylog (n + 1)` has complex derivative
`polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hz0 : z ≠ 0) :
    HasDerivAt (polylog (n + 1)) (polylog n z / z) z := by
  rw [← deriv_polylog_add_one n hz hz0]
  exact (differentiableAt_polylog (n + 1) hz).hasDerivAt

private lemma continuousOn_mul_deriv_polylog_add_one (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z)) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  refine continuousOn_const.mul ?_
  refine (analyticOnNhd_polylog (n + 1)).deriv.continuousOn.comp
    (Complex.continuous_ofReal.continuousOn.mul continuousOn_const) fun t ht ↦ ?_
  simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz ht

private lemma eqOn_polylog_mul_div_uIoc (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    EqOn (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z))
      (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) (uIoc 0 1) := by
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
    simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioc_subset_Icc_self ht)
  dsimp only
  rw [← mul_deriv_polylog_add_one n htz]
  field_simp [ht0]

/-- For every integer weight `n` and `z` in the cut plane, the radial quotient
`t ↦ polylog n (t * z) / t` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_mul_div (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 :=
  (continuousOn_mul_deriv_polylog_add_one n hz).intervalIntegrable.congr
    (eqOn_polylog_mul_div_uIoc n hz)

/-- Recursive radial-integral identity: for every integer weight `n` and every `z` in the cut
plane, `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ polylog (n + 1) ((s : ℂ) * z))
        (z * deriv (polylog (n + 1)) ((t : ℂ) * z)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
      simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
    have hinner : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    simpa only [Function.comp_def, smul_eq_mul] using
      HasDerivAt.scomp t (differentiableAt_polylog (n + 1) htz).hasDerivAt hinner
  rw [← intervalIntegral.integral_congr_ae
      (ae_of_all _ fun t ht ↦ eqOn_polylog_mul_div_uIoc n hz ht),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (continuousOn_mul_deriv_polylog_add_one n hz).intervalIntegrable]
  simp

end TauCeti.Polylog
