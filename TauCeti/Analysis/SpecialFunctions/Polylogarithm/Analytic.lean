/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Nonpositive
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Holomorphy, differential recursion, and conjugation of principal polylogarithms

Every integer-weight polylogarithm `TauCeti.Polylog.polylog n` is complex analytic on the
principal cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}` and satisfies the Euler differential
recursion `z * deriv (polylog (n + 1)) z = polylog n z` throughout that domain, including at the
origin where both sides vanish. Away from zero this gives
`deriv (polylog (n + 1)) z = polylog n z / z`, and integrating along radial segments recovers the
recursive integral representation `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t` in
every integer weight.

On the real ray `[1, ∞)` omitted from the principal domain, `polylog 1` is discontinuous at every
point, characterising `{z : ℂ | 1 - z ∈ Complex.slitPlane}` as the exact domain of continuity,
differentiability, and analyticity of weight one. Complex conjugation commutes with `polylog n` on
`{z : ℂ | 1 - z ∈ Complex.slitPlane}` in every weight, and on all of `ℂ` in nonpositive weight
where the functions are real-coefficient rational functions; in particular `polylog n x` is real
for every real `x ≤ 1`.

## Main declarations

* `TauCeti.Polylog.analyticOnNhd_polylog`: `polylog n` is complex analytic on
  `{z : ℂ | 1 - z ∈ Complex.slitPlane}` for every `n : ℤ`.
* `TauCeti.Polylog.mul_deriv_polylog_add_one`: the Euler differential recursion
  `z * deriv (polylog (n + 1)) z = polylog n z` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.hasDerivAt_polylog_add_one_of_ne_zero`: complex derivative `polylog n z / z`
  at nonzero points of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.polylog_add_one_eq_integral`: the recursive radial integral
  `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t` on
  `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.not_continuousAt_polylog_one_of_one_le`,
  `TauCeti.Polylog.continuousAt_polylog_one_iff`: `polylog 1` is continuous (equivalently
  differentiable or analytic) at `z` if and only if `1 - z ∈ Complex.slitPlane`.
* `TauCeti.Polylog.polylog_conj`, `TauCeti.Polylog.polylog_conj_of_nonpos`: compatibility with
  complex conjugation on `{z : ℂ | 1 - z ∈ Complex.slitPlane}` and in nonpositive weight on `ℂ`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.1, (2)–(3), p. 50, and §§1.1–1.3, pp. 50–51.
* Alexander B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology*,
  Advances in Mathematics 114 (1995), §1.0, (1.1), p. 201.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti.Polylog

/-- Differentiation under the radial integral sign in weights `k + 2` on the principal domain. -/
private lemma hasDerivAt_polylog_nat_add_two_aux (k : ℕ) {z₀ : ℂ}
    (hz₀ : 1 - z₀ ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀))
        volume 0 1 ∧
      HasDerivAt (polylog (k + 2 : ℕ))
        ((Nat.factorial k : ℂ)⁻¹ *
          ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀)) z₀ := by
  have hopen : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  have hKΩ : Metric.closedBall z₀ (r / 2) ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨δ, hδ, hδK⟩ := exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z₀ (r / 2)) hKΩ
  let F : ℂ → ℝ → ℂ := fun z t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun z t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)
  have hmeasF : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (uIoc 0 1)) := by
    rw [uIoc_of_le zero_le_one]
    exact .of_forall fun z ↦ (intervalIntegrable_radialIntegrand k z).1.aestronglyMeasurable
  have hbound_int : IntervalIntegrable (fun t : ℝ ↦ δ⁻¹ * |Real.log t| ^ k) volume 0 1 := by
    convert ((TauCeti.intervalIntegrable_log_pow (a := 0) (b := 1) k).norm).const_mul δ⁻¹
      using 2 with t
    rw [Real.norm_eq_abs, abs_pow]
  have hbound : ∀ᵐ t ∂volume, t ∈ uIoc 0 1 →
      ∀ z ∈ Metric.closedBall z₀ (r / 2), ‖F' z t‖ ≤ δ⁻¹ * |Real.log t| ^ k := by
    refine .of_forall fun t ht z hz ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    dsimp only [F']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (by positivity) hδ (hδK z hz t (Ioc_subset_Icc_self ht))
  have hdiff : ∀ᵐ t ∂volume, t ∈ uIoc 0 1 →
      ∀ z ∈ Metric.closedBall z₀ (r / 2), HasDerivAt (fun w ↦ F w t) (F' z t) z := by
    refine .of_forall fun t ht z hz ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
      simpa [mul_comm] using
        Complex.one_sub_mul_ofReal_mem_slitPlane (hKΩ hz) (Ioc_subset_Icc_self ht)
    have hlin : HasDerivAt (fun w : ℂ ↦ 1 - (t : ℂ) * w) (-(t : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (t : ℂ)).const_sub (1 : ℂ)
    have hlog : HasDerivAt (fun w : ℂ ↦ -Complex.log (1 - (t : ℂ) * w))
        ((t : ℂ) / (1 - (t : ℂ) * z)) z := by
      convert (hlin.clog hslit).neg using 1; ring
    convert (hlog.const_mul (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ) using 1
    dsimp only [F']; field_simp
  obtain ⟨hint, hd⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.closedBall_mem_nhds z₀ (half_pos hr)) hmeasF (intervalIntegrable_radialIntegrand k z₀)
    (by fun_prop : Measurable (F' z₀)).aestronglyMeasurable hbound hbound_int hdiff
  exact ⟨hint, (hd.const_mul (Nat.factorial k : ℂ)⁻¹).congr_of_eventuallyEq
    (.of_forall (polylog_nat_add_two k))⟩

/-- The boundary product `(-log t) ^ (m + 1) * (-Log (1 - t z))` vanishes as `t → 0⁺`. -/
private lemma tendsto_log_pow_mul_clog_nhdsGT_zero (m : ℕ) (z : ℂ) :
    Tendsto (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ (m + 1) * (-Complex.log (1 - (t : ℂ) * z)))
      (𝓝[>] 0) (𝓝 0) := by
  have hlim0 : Tendsto (fun t : ℝ ↦ 3 / 2 * ‖z‖ * (|Real.log t| ^ (m + 1 : ℝ) / t ^ (-1 : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using
      ((isLittleO_abs_log_rpow_rpow_nhdsGT_zero (m + 1 : ℝ)
        (s := -1) neg_one_lt_zero).tendsto_div_nhds_zero).const_mul (3 / 2 * ‖z‖)
  have hlim : Tendsto (fun t : ℝ ↦ 3 / 2 * ‖z‖ * (|Real.log t| ^ (m + 1) * t))
      (𝓝[>] 0) (𝓝 0) := by
    refine hlim0.congr fun t ↦ ?_
    have hcast : (m + 1 : ℝ) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Real.rpow_natCast, Real.rpow_neg_one, div_inv_eq_mul]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (2 * (‖z‖ + 1)))] with t ht
  have htz : t * ‖z‖ ≤ 1 / 2 := by
    refine (mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg z)).trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have hnorm : ‖-((t : ℂ) * z)‖ = t * ‖z‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
  have hlog : ‖Complex.log (1 - (t : ℂ) * z)‖ ≤ 3 / 2 * (t * ‖z‖) := by
    have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) (by rwa [hnorm])
    rwa [hnorm, ← sub_eq_add_neg] at h
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  calc |Real.log t| ^ (m + 1) * ‖Complex.log (1 - (t : ℂ) * z)‖
      ≤ |Real.log t| ^ (m + 1) * (3 / 2 * (t * ‖z‖)) := by gcongr
    _ = 3 / 2 * ‖z‖ * (|Real.log t| ^ (m + 1) * t) := by ring

/-- Integration by parts identifies `z * ∫ (-log t) ^ (m + 1) / (1 - t z)` with `(m + 1)` times
the radial integral of weight `m + 2`. -/
private lemma integral_log_pow_succ_mul_div_one_sub (m : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ (m + 1) * (z / (1 - (t : ℂ) * z)) =
      (m + 1 : ℂ) * ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ m * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ) := by
  let g : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ (m + 1) * (-Complex.log (1 - (t : ℂ) * z))
  let u₁ : ℝ → ℂ := fun t ↦
    -((m + 1 : ℂ) * (((-Real.log t : ℝ) : ℂ) ^ m * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)))
  let u₂ : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ (m + 1) * (z / (1 - (t : ℂ) * z))
  have hu₁_int : IntervalIntegrable u₁ volume 0 1 :=
    ((intervalIntegrable_radialIntegrand m z).const_mul (m + 1 : ℂ)).neg
  have hu₂_int : IntervalIntegrable u₂ volume 0 1 := by
    convert (hasDerivAt_polylog_nat_add_two_aux (m + 1) hz).1.const_mul z using 2 with t; ring
  have hg_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (u₁ t + u₂ t) t := fun t ht ↦ by
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
      simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioo_subset_Icc_self ht)
    have hd1 : HasDerivAt (fun s : ℝ ↦ ((-Real.log s : ℝ) : ℂ) ^ (m + 1))
        ((m + 1 : ℂ) * ((-Real.log t : ℝ) : ℂ) ^ m * (-(t : ℂ)⁻¹)) t := by
      convert ((Real.hasDerivAt_log ht.1.ne').neg.pow (m + 1)).ofReal_comp using 1
      · ext s; simp
      · simp only [Pi.neg_apply, Nat.add_sub_cancel]; push_cast; ring
    have hd2 : HasDerivAt (fun s : ℝ ↦ -Complex.log (1 - (s : ℂ) * z))
        (z / (1 - (t : ℂ) * z)) t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ 1 - (s : ℂ) * z) (-z) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).const_sub (1 : ℂ)
      convert (hlin.clog_real hslit).neg using 1; ring
    convert hd1.mul hd2 using 1; dsimp only [u₁, u₂]; field_simp
  have hg1 : Tendsto g (𝓝[<] 1) (𝓝 0) := by
    have hlin1 : HasDerivAt (fun s : ℝ ↦ 1 - (s : ℂ) * z) (-z) 1 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (1 : ℝ))).mul_const z).const_sub (1 : ℂ)
    have hc1 : ContinuousAt g 1 :=
      (((Complex.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_log one_ne_zero).neg).pow (m + 1)).mul
        (hlin1.clog_real (by simpa using hz)).neg.continuousAt)
    exact (by simp [g] : g 1 = 0) ▸ hc1.tendsto.mono_left nhdsWithin_le_nhds
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hg_deriv
    (hu₁_int.add hu₂_int) (tendsto_log_pow_mul_clog_nhdsGT_zero m z) hg1
  rw [sub_zero, intervalIntegral.integral_add hu₁_int hu₂_int] at hftc
  simp only [u₁, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hftc
  exact (neg_add_eq_zero.mp hftc).symm

/-- Weight one has complex derivative `(1 - z)⁻¹` on the principal domain, including at `0`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) ((1 - z)⁻¹) z := by
  have hlin : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hlog : HasDerivAt (fun w : ℂ ↦ -Complex.log (1 - w)) ((1 - z)⁻¹) z := by
    convert (hlin.clog hz).neg using 1
    ring
  exact hlog.congr_of_eventuallyEq (.of_forall polylog_one)

/-- Every integer-weight polylogarithm is complex differentiable at every point of
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (hasDerivAt_polylog_zero_weight
        (sub_ne_zero.mp (Complex.slitPlane_ne_zero hz)).symm).differentiableAt
    · exact (hasDerivAt_polylog_one hz).differentiableAt
    · exact (hasDerivAt_polylog_nat_add_two_aux k hz).2.differentiableAt
  | negSucc r =>
    have hne : z ≠ 1 := (sub_ne_zero.mp (Complex.slitPlane_ne_zero hz)).symm
    exact (analyticAt_polylog_neg_nat (r + 1) hne).differentiableAt

/-- Every integer-weight polylogarithm is complex differentiable on
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ (differentiableAt_polylog n hz).differentiableWithinAt

/-- Every integer-weight polylogarithm is complex analytic on the principal domain
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).analyticOnNhd (Complex.isOpen_slitPlane.preimage (by fun_prop))

/-- Every integer-weight polylogarithm is complex analytic at every point of
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- **Euler differential recursion.** On `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, the Euler
operator `z * d/dz` lowers the polylogarithm weight by one in every integer weight, including at
`z = 0`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  cases n with
  | negSucc r =>
    have heq : Int.negSucc r + 1 = -(r : ℤ) := by omega
    have hneg : Int.negSucc r = -((r + 1 : ℕ) : ℤ) := rfl
    rw [heq, hneg, polylog_neg_nat_succ]
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast]
    rcases m with _ | k
    · simp only [Nat.cast_zero, zero_add]
      rw [(hasDerivAt_polylog_one hz).deriv, polylog_zero_weight, div_eq_mul_inv]
    · obtain ⟨hint, hd⟩ := hasDerivAt_polylog_nat_add_two_aux k hz
      have hcast : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, hd.deriv]
      have hmul : z * ((Nat.factorial k : ℂ)⁻¹ *
          ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) =
          (Nat.factorial k : ℂ)⁻¹ *
            ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (z / (1 - (t : ℂ) * z)) := by
        rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
        congr 1
        exact intervalIntegral.integral_congr fun _ _ ↦ by ring
      rw [hmul]
      rcases k with _ | m
      · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero]
        have hg : ∀ t ∈ uIcc (0 : ℝ) 1,
            HasDerivAt (fun s : ℝ ↦ -Complex.log (1 - (s : ℂ) * z))
              (z / (1 - (t : ℂ) * z)) t := by
          intro t ht
          rw [uIcc_of_le zero_le_one] at ht
          have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
            simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
          have hlin : HasDerivAt (fun s : ℝ ↦ 1 - (s : ℂ) * z) (-z) t := by
            simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).const_sub (1 : ℂ)
          convert (hlin.clog_real hslit).neg using 1
          ring
        have hint0 : IntervalIntegrable (fun t : ℝ ↦ z / (1 - (t : ℂ) * z)) volume 0 1 := by
          simpa [div_eq_mul_inv] using hint.const_mul z
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint0]
        simp
      · have hcast2 : ((m + 1 + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) := rfl
        rw [integral_log_pow_succ_mul_div_one_sub m hz, hcast2, polylog_nat_add_two,
          Nat.factorial_succ, Nat.cast_mul]
        have hm1 : (m + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero m
        push_cast
        field_simp [hm1]
        congr 1
        exact intervalIntegral.integral_congr fun t _ ↦ by rw [mul_comm (t : ℂ) z]

/-- At a nonzero point of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, `polylog (n + 1)` has complex
derivative `polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one_of_ne_zero (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    HasDerivAt (polylog (n + 1)) (polylog n z / z) z := by
  have hd := (differentiableAt_polylog (n + 1) hz).hasDerivAt
  have heq : deriv (polylog (n + 1)) z = polylog n z / z := by
    rw [eq_div_iff hz0, mul_comm, mul_deriv_polylog_add_one n hz]
  rwa [heq] at hd

/-- Quotient form of the Euler differential recursion away from zero on the principal domain. -/
theorem deriv_polylog_add_one_of_ne_zero (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z :=
  (hasDerivAt_polylog_add_one_of_ne_zero n hz hz0).deriv

/-- For `1 - z ∈ Complex.slitPlane`, the radial quotient `t ↦ polylog n (t * z) / t` is interval
integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_ofReal_mul_div (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 := by
  let G : ℂ → ℂ := fun w ↦ polylog n (w * z)
  have hG_diff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ G (t : ℂ) := fun t ht ↦
    (differentiableAt_polylog n
      (by simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz ht)).comp (t : ℂ)
      (differentiableAt_id.mul_const z)
  have hdslope_cont : ContinuousOn (fun t : ℝ ↦ dslope G 0 (t : ℂ)) (Icc 0 1) := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · exact ((continuousAt_dslope_same.2
        (by simpa using hG_diff 0 (left_mem_Icc.mpr zero_le_one))).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
      exact (((continuousAt_dslope_of_ne hne).2 (hG_diff t ht).continuousAt).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hdslope_int : IntervalIntegrable (fun t : ℝ ↦ dslope G 0 (t : ℂ)) volume 0 1 :=
    (hdslope_cont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  have hae : (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) =ᵐ[volume.restrict (uIoc 0 1)]
      (fun t : ℝ ↦ dslope G 0 (t : ℂ)) := by
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    simp [dslope_of_ne G hne, slope, G, div_eq_inv_mul]
  exact hdslope_int.congr_ae hae.symm

/-- **Recursive radial integral.** On `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, every integer-weight
polylogarithm `polylog (n + 1) z` is the radial integral `∫₀¹ polylog n (t * z) / t dt`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  let H : ℝ → ℂ := fun t ↦ polylog (n + 1) ((t : ℂ) * z)
  have hpath_cont : Continuous (fun t : ℝ ↦ (t : ℂ) * z) :=
    Complex.continuous_ofReal.mul continuous_const
  have hH_cont : ContinuousOn H (Icc 0 1) :=
    (differentiableOn_polylog (n + 1)).continuousOn.comp hpath_cont.continuousOn fun _ ht ↦ by
      simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
  have hH_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt H (polylog n ((t : ℂ) * z) / (t : ℂ)) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
      simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioo_subset_Icc_self ht)
    have hlin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    have hcomp : HasDerivAt H (deriv (polylog (n + 1)) ((t : ℂ) * z) * z) t :=
      (differentiableAt_polylog (n + 1) hslit).hasDerivAt.comp t hlin
    convert hcomp using 1
    rw [div_eq_iff ht0]
    calc polylog n ((t : ℂ) * z)
        = ((t : ℂ) * z) * deriv (polylog (n + 1)) ((t : ℂ) * z) :=
          (mul_deriv_polylog_add_one n hslit).symm
      _ = deriv (polylog (n + 1)) ((t : ℂ) * z) * z * (t : ℂ) := by ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hH_cont hH_deriv
    (intervalIntegrable_polylog_ofReal_mul_div n hz)
  simpa [H] using hftc.symm

/-- Weight one is not continuous at its logarithmic branch point `1`. -/
theorem not_continuousAt_polylog_one_one :
    ¬ ContinuousAt (polylog 1) 1 := by
  intro hc
  have hre_cont : ContinuousAt (fun z : ℂ ↦ (polylog 1 z).re) 1 :=
    Complex.continuous_re.continuousAt.comp hc
  have hpath : Continuous (fun t : ℝ ↦ (1 : ℂ) - (t : ℂ)) :=
    continuous_const.sub Complex.continuous_ofReal
  have ht0 : Tendsto (fun t : ℝ ↦ (1 : ℂ) - (t : ℂ)) (𝓝 0) (𝓝 1) := by
    simpa using (hpath.continuousAt (x := 0)).tendsto
  have hlim0 : Tendsto (fun t : ℝ ↦ (polylog 1 ((1 : ℂ) - (t : ℂ))).re) (𝓝[>] 0) (𝓝 0) := by
    have hcomp := hre_cont.tendsto.comp ht0
    simp only [Function.comp_def, polylog_one, sub_self, Complex.log_zero, neg_zero,
      Complex.zero_re] at hcomp
    simpa [polylog_one] using hcomp.mono_left nhdsWithin_le_nhds
  have htop : Tendsto (fun t : ℝ ↦ (polylog 1 ((1 : ℂ) - (t : ℂ))).re) (𝓝[>] 0) atTop := by
    refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (_ht : 0 < t)
    simp [polylog_one, Complex.log_ofReal_re]
  exact not_tendsto_nhds_of_tendsto_atTop htop _ hlim0

/-- Weight one is not continuous at any real point `x ≥ 1` on the branch cut `[1, ∞)`. -/
theorem not_continuousAt_polylog_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    ¬ ContinuousAt (polylog 1) (x : ℂ) := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · simpa using not_continuousAt_polylog_one_one
  · intro hc
    have him_cont : ContinuousAt (fun z : ℂ ↦ (polylog 1 z).im) (x : ℂ) :=
      Complex.continuous_im.continuousAt.comp hc
    have him_val : (polylog 1 (x : ℂ)).im = -Real.pi := by
      rw [polylog_one, Complex.neg_im, Complex.log_im, neg_inj, Complex.arg_eq_pi_iff]
      exact ⟨by simp; linarith, by simp⟩
    have hlim1 : Tendsto (fun t : ℝ ↦ (polylog 1 ((x : ℂ) + (t : ℂ) * Complex.I)).im)
        (𝓝[>] 0) (𝓝 (-Real.pi)) := by
      have hpath : Continuous (fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * Complex.I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have ht0 : Tendsto (fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * Complex.I) (𝓝 0) (𝓝 (x : ℂ)) := by
        simpa using (hpath.continuousAt (x := 0)).tendsto
      have hcomp : Tendsto (fun t : ℝ ↦ (polylog 1 ((x : ℂ) + (t : ℂ) * Complex.I)).im)
          (𝓝 0) (𝓝 ((polylog 1 (x : ℂ)).im)) :=
        him_cont.tendsto.comp ht0
      rw [him_val] at hcomp
      exact hcomp.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun t : ℝ ↦ (polylog 1 ((x : ℂ) + (t : ℂ) * Complex.I)).im)
        (𝓝[>] 0) (𝓝 Real.pi) := by
      have harg := Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
        (z := 1 - (x : ℂ)) (by simp; linarith) (by simp)
      have hmap : Tendsto (fun t : ℝ ↦ (1 : ℂ) - ((x : ℂ) + (t : ℂ) * Complex.I))
          (𝓝[>] 0) (𝓝[{w : ℂ | w.im < 0}] (1 - (x : ℂ))) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have hc0 : Continuous (fun t : ℝ ↦ (1 : ℂ) - ((x : ℂ) + (t : ℂ) * Complex.I)) := by
            fun_prop
          simpa using (hc0.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
          simp [ht]
      simpa [polylog_one, Complex.log_im] using (harg.comp hmap).neg
    have heq : -Real.pi = Real.pi := tendsto_nhds_unique hlim1 hlim2
    linarith [Real.pi_pos]

/-- Weight one is continuous at `z` if and only if `1 - z ∈ Complex.slitPlane`. -/
@[simp]
theorem continuousAt_polylog_one_iff {z : ℂ} :
    ContinuousAt (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane := by
  refine ⟨fun hc ↦ by_contra fun hz ↦ ?_, fun hz ↦ (differentiableAt_polylog 1 hz).continuousAt⟩
  rw [Complex.mem_slitPlane_iff, not_or, not_lt, ne_eq, Decidable.not_not] at hz
  have hzim : z.im = 0 := by simpa using hz.2
  have hzre : 1 ≤ z.re := by simpa using hz.1
  have hzeq : z = (z.re : ℂ) := Complex.ext rfl (by simp [hzim])
  exact not_continuousAt_polylog_one_of_one_le hzre (hzeq ▸ hc)

/-- Weight one is complex differentiable at `z` if and only if `1 - z ∈ Complex.slitPlane`. -/
@[simp]
theorem differentiableAt_polylog_one_iff {z : ℂ} :
    DifferentiableAt ℂ (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane :=
  ⟨fun h ↦ continuousAt_polylog_one_iff.mp h.continuousAt, differentiableAt_polylog 1⟩

/-- Weight one is complex analytic at `z` if and only if `1 - z ∈ Complex.slitPlane`. -/
@[simp]
theorem analyticAt_polylog_one_iff {z : ℂ} :
    AnalyticAt ℂ (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane :=
  ⟨fun h ↦ continuousAt_polylog_one_iff.mp h.continuousAt, analyticAt_polylog 1⟩

/-- Nonpositive-weight polylogarithms commute with complex conjugation everywhere on `ℂ`,
including at the totalised pole `1`. -/
theorem polylog_conj_of_nonpos {n : ℤ} (hn : n ≤ 0) (z : ℂ) :
    polylog n (starRingEnd ℂ z) = starRingEnd ℂ (polylog n z) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = -(r : ℤ) := ⟨(-n).toNat, by omega⟩
  rw [polylog_neg_nat_eq_div, polylog_neg_nat_eq_div]
  have haeval : Polynomial.aeval (starRingEnd ℂ z) (TauCeti.eulerianPolynomial r) =
      starRingEnd ℂ (Polynomial.aeval z (TauCeti.eulerianPolynomial r)) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int ((starRingEnd ℂ).comp (algebraMap ℤ ℂ)) (algebraMap ℤ ℂ)]
  simp [haeval]

/-- On the principal domain `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, every integer-weight
polylogarithm commutes with complex conjugation. -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n (starRingEnd ℂ z) = starRingEnd ℂ (polylog n z) := by
  rcases le_or_gt n 0 with hn | hn
  · exact polylog_conj_of_nonpos hn z
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
  rcases m with _ | k
  · simp only [Nat.zero_add, Nat.cast_one, polylog_one, map_neg]
    have hconj : (1 : ℂ) - starRingEnd ℂ z = starRingEnd ℂ (1 - z) := by simp
    rw [hconj, Complex.log_conj (1 - z) (Complex.slitPlane_arg_ne_pi hz)]
  · have hcast : ((k + 1 + 1 : ℕ) : ℤ) = ((k + 2 : ℕ) : ℤ) := rfl
    rw [hcast, polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀, map_natCast,
      intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      ← integral_conj]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
      simpa [mul_comm] using Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioc_subset_Icc_self ht)
    have harg : (1 : ℂ) - (t : ℂ) * starRingEnd ℂ z =
        starRingEnd ℂ (1 - (t : ℂ) * z) := by simp
    rw [harg, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hslit)]
    simp

/-- Nonpositive-weight polylogarithms are real-valued on the entire real line, including at `1`. -/
theorem im_polylog_ofReal_of_nonpos {n : ℤ} (hn : n ≤ 0) (x : ℝ) :
    (polylog n x).im = 0 := by
  have hconj := polylog_conj_of_nonpos hn x
  rw [Complex.conj_ofReal] at hconj
  exact Complex.conj_eq_iff_im.mp hconj.symm

/-- For every real `x ≤ 1` and integer weight `n`, `polylog n x` has zero imaginary part. -/
theorem im_polylog_ofReal (n : ℤ) {x : ℝ} (hx : x ≤ 1) :
    (polylog n x).im = 0 := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · have hslit : (1 : ℂ) - (x : ℂ) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_mem_slitPlane]
      linarith
    have hconj := polylog_conj n hslit
    rw [Complex.conj_ofReal] at hconj
    exact Complex.conj_eq_iff_im.mp hconj.symm
  · rcases le_or_gt n 0 with hn | hn
    · exact im_polylog_ofReal_of_nonpos hn 1
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
    rcases m with _ | k
    · simp
    · apply Complex.conj_eq_iff_im.mp
      have hcast : ((k + 1 + 1 : ℕ) : ℤ) = ((k + 2 : ℕ) : ℤ) := rfl
      rw [Complex.ofReal_one, hcast, polylog_nat_add_two, map_mul, map_inv₀, map_natCast,
        intervalIntegral.integral_of_le zero_le_one, ← integral_conj]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · simp
      · have hslit : (1 : ℂ) - (t : ℂ) ∈ Complex.slitPlane := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_mem_slitPlane]
          linarith
        have harg : (1 : ℂ) - (t : ℂ) = starRingEnd ℂ (1 - (t : ℂ)) := by simp
        simp only [mul_one]
        nth_rw 1 [harg]
        rw [Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hslit)]
        simp

/-- For every real `x ≤ 1` and integer weight `n`, `polylog n x` equals its real part coerced to
`ℂ`. -/
theorem ofReal_re_polylog_ofReal (n : ℤ) {x : ℝ} (hx : x ≤ 1) :
    ((polylog n x).re : ℂ) = polylog n x :=
  Complex.ext rfl (im_polylog_ofReal n hx).symm

end TauCeti.Polylog
