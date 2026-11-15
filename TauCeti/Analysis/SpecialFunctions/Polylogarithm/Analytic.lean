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
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Cut-plane holomorphy and the Euler recursion of principal polylogarithms

Every integer-weight principal polylogarithm `Liₙ` is complex analytic on the principal domain
`ℂ ∖ [1, ∞) = {z : ℂ | 1 - z ∈ Complex.slitPlane}`, satisfies the Euler differential recursion
`z * deriv (Li_{n+1}) z = Liₙ z` (equivalently `z * deriv (Liₙ) z = Li_{n-1} z`) there, including
at `z = 0` where both sides vanish, and satisfies the recursive radial-integral identity
`Li_{n+1}(z) = ∫ t in 0..1, Liₙ(t z) / t dt`.

For weights `k + 2 ≥ 2`, differentiating the logarithmic radial integral under the integral sign on
compact subdiscs of `{z | 1 - z ∈ Complex.slitPlane}` uses the uniform lower bound
`exists_le_norm_one_sub_ofReal_mul` on `‖1 - t z‖` to dominate the `z`-derivative
`(-log t) ^ k / (1 - t z)` by a multiple of `|log t| ^ k`. Complex differentiability on the open
principal domain then yields analyticity by Goursat's theorem. Since the principal domain is
star-convex at `0` (`TauCeti.starConvex_one_sub_slitPlane`, hence preconnected), the identity
principle glues the Euler differential recursion from the open unit disc
(`mul_deriv_polylog_add_one_of_norm_lt_one`) to the whole principal domain, and the fundamental
theorem of calculus along `t ↦ Li_{n+1}(t z)` recovers the recursive radial integral in every
integer weight.

Sharpness characterizations at the end confirm that regularity in weight `1` holds on and only on
`ℂ ∖ [1, ∞)`: `Li₁` has a logarithmic singularity at `1` and a `2πi` jump across `(1, ∞)` (in
particular at `3`), so both `ContinuousAt (polylog 1) z` and `AnalyticAt ℂ (polylog 1) z` are
equivalent to `1 - z ∈ Complex.slitPlane`.

## Main declarations

* `TauCeti.Polylog.analyticOnNhd_polylog`, `TauCeti.Polylog.analyticAt_polylog`,
  `TauCeti.Polylog.continuousAt_polylog`, and `TauCeti.Polylog.continuousOn_polylog`:
  holomorphy and continuity of `polylog n` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}` for all `n : ℤ`.
* `TauCeti.Polylog.hasDerivAt_polylog_one` and `TauCeti.Polylog.hasDerivAt_polylog_nat_add_two`:
  explicit complex derivatives of `Li₁` and `Li_{k+2}` on `{z | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.mul_deriv_polylog`, `TauCeti.Polylog.mul_deriv_polylog_add_one`,
  `TauCeti.Polylog.hasDerivAt_polylog`, `TauCeti.Polylog.hasDerivAt_polylog_add_one`,
  `TauCeti.Polylog.deriv_polylog`, and `TauCeti.Polylog.deriv_polylog_add_one`:
  the Euler differential recursion on `{z | 1 - z ∈ Complex.slitPlane}` in both `n` and `n + 1`
  indexings, and its quotient form away from `0`.
* `TauCeti.Polylog.intervalIntegrable_polylog_div`, `TauCeti.Polylog.polylog_eq_integral`, and
  `TauCeti.Polylog.polylog_add_one_eq_integral`:
  recursive radial-integral representations for every `n : ℤ` on
  `{z | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.not_continuousAt_polylog_one_of_one_le`,
  `TauCeti.Polylog.continuousAt_polylog_one_iff`, `TauCeti.Polylog.analyticAt_polylog_one_iff`, and
  `TauCeti.Polylog.not_continuousAt_polylog_one_three`: exact regularity characterizations for
  `polylog 1` along and off `[1, ∞)`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (2)–(3), p. 50.
* Alexander B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology*,
  Advances in Mathematics 114 (1995), §1.0, (1.1), p. 201.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Polylog

/-- On the principal domain `{z | 1 - z ∈ slitPlane}`, `polylog 1` has complex derivative
`(1 - z)⁻¹`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) ((1 - z)⁻¹) z := by
  have h : HasDerivAt (fun w : ℂ ↦ -Complex.log (1 - w)) (-((0 - 1 : ℂ) / (1 - z))) z :=
    (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).clog hz).neg
  convert h using 1
  · ext w; simp
  · ring

/-- Formula for `deriv (polylog 1) z` on `{z | 1 - z ∈ slitPlane}`. -/
theorem deriv_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog 1) z = (1 - z)⁻¹ :=
  (hasDerivAt_polylog_one hz).deriv

/-- Pointwise `z`-derivative of the radial integrand of `polylog (k + 2)` at `t > 0` when
`1 - t * z ∈ Complex.slitPlane`. -/
private lemma hasDerivAt_radialIntegrand (k : ℕ) {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : 1 - (t : ℂ) * z ∈ Complex.slitPlane) :
    HasDerivAt
      (fun w : ℂ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ))
      (((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hlin : HasDerivAt (fun w : ℂ ↦ 1 - (t : ℂ) * w) (0 - (t : ℂ) * 1) z :=
    (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (t : ℂ))
  have hclog : HasDerivAt (fun w : ℂ ↦ -Complex.log (1 - (t : ℂ) * w))
      (-((0 - (t : ℂ) * 1) / (1 - (t : ℂ) * z))) z :=
    (hlin.clog hz).neg
  convert (hclog.const_mul (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ) using 1
  field_simp [htc]
  ring

/-- Parametric differentiation of the radial integral of `polylog (k + 2)` on the principal
domain, yielding both integrability of the differentiated integrand and `HasDerivAt`. -/
private lemma intervalIntegrable_and_hasDerivAt_polylog_nat_add_two (k : ℕ) {z₀ : ℂ}
    (hz₀ : 1 - z₀ ∈ Complex.slitPlane) :
    IntervalIntegrable
        (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀)) volume 0 1 ∧
      HasDerivAt (polylog (k + 2 : ℕ))
        ((Nat.factorial k : ℂ)⁻¹ *
          ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀)) z₀ := by
  have hopen : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z₀ hz₀
  set K : Set ℂ := Metric.closedBall z₀ (ε / 2)
  have hK_nhds : K ∈ 𝓝 z₀ := Metric.closedBall_mem_nhds z₀ (half_pos hε)
  have hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨δ, hδ, hδK⟩ := exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z₀ _) hKΩ
  set F : ℂ → ℝ → ℂ := fun z t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)
  set F' : ℂ → ℝ → ℂ := fun z t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)
  have hlog : IntervalIntegrable (fun t : ℝ ↦ δ⁻¹ * |Real.log t| ^ k) volume 0 1 := by
    simpa [Real.norm_eq_abs, abs_pow] using
      (TauCeti.intervalIntegrable_log_pow k (a := 0) (b := 1)).norm.const_mul δ⁻¹
  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun t : ℝ ↦ δ⁻¹ * |Real.log t| ^ k)
    hK_nhds
    (.of_forall fun z ↦ (by fun_prop : Measurable (F z)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z₀)
    (by fun_prop : Measurable (F' z₀)).aestronglyMeasurable
    (ae_of_all _ fun t ht z hzK ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      have hw : δ ≤ ‖1 - (t : ℂ) * z‖ := hδK z hzK t (Ioc_subset_Icc_self ht)
      dsimp only [F']
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg]
      calc |Real.log t| ^ k / ‖1 - (t : ℂ) * z‖
          ≤ |Real.log t| ^ k / δ := div_le_div_of_nonneg_left (by positivity) hδ hw
        _ = δ⁻¹ * |Real.log t| ^ k := by rw [div_eq_inv_mul])
    hlog
    (ae_of_all _ fun t ht z hzK ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      exact hasDerivAt_radialIntegrand k ht.1
        (mul_comm z (t : ℂ) ▸
          Complex.one_sub_mul_ofReal_mem_slitPlane (hKΩ hzK) (Ioc_subset_Icc_self ht)))
  refine ⟨hdom.1, ?_⟩
  have hdef : polylog (k + 2 : ℕ) = fun z ↦ (Nat.factorial k : ℂ)⁻¹ * ∫ t : ℝ in 0..1, F z t :=
    funext (polylog_nat_add_two k)
  rw [hdef]
  exact hdom.2.const_mul (Nat.factorial k : ℂ)⁻¹

/-- For `z` in the principal domain `{z | 1 - z ∈ slitPlane}`, `t ↦ (-log t) ^ k / (1 - t * z)` is
interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_neg_log_pow_div_one_sub_mul (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 :=
  (intervalIntegrable_and_hasDerivAt_polylog_nat_add_two k hz).1

/-- On the principal domain `{z | 1 - z ∈ slitPlane}`, `polylog (k + 2)` has complex derivative
`(k!)⁻¹ * ∫ t in 0..1, (-log t) ^ k / (1 - t * z)`. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z :=
  (intervalIntegrable_and_hasDerivAt_polylog_nat_add_two k hz).2

/-- Every integer-weight polylogarithm is complex differentiable at each point of the principal
domain `{z | 1 - z ∈ slitPlane}`. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z := by
  have hzne : z ≠ 1 := fun h ↦ Complex.slitPlane_ne_zero hz (by simp [h])
  cases n with
  | ofNat n =>
    rcases n with _ | _ | k
    · exact (analyticAt_polylog_neg_nat 0 hzne).differentiableAt
    · exact (hasDerivAt_polylog_one hz).differentiableAt
    · exact (hasDerivAt_polylog_nat_add_two k hz).differentiableAt
  | negSucc r =>
    simpa [Int.negSucc_eq] using (analyticAt_polylog_neg_nat (r + 1) hzne).differentiableAt

/-- Every integer-weight polylogarithm is complex differentiable on the principal domain
`{z | 1 - z ∈ slitPlane}`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ (differentiableAt_polylog n hz).differentiableWithinAt

/-- Every integer-weight principal polylogarithm `Liₙ` is holomorphic (`AnalyticOnNhd ℂ`) on the
cut plane `ℂ ∖ [1, ∞) = {z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).analyticOnNhd
    (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id))

/-- Pointwise form of `analyticOnNhd_polylog`: `polylog n` is complex analytic at every point `z`
with `1 - z ∈ Complex.slitPlane`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- Every integer-weight polylogarithm is continuous at each point of the principal domain
`{z | 1 - z ∈ slitPlane}`. -/
theorem continuousAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousAt (polylog n) z :=
  (analyticAt_polylog n hz).continuousAt

/-- Every integer-weight polylogarithm is continuous on the principal domain
`{z | 1 - z ∈ slitPlane}`. -/
theorem continuousOn_polylog (n : ℤ) :
    ContinuousOn (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (analyticOnNhd_polylog n).continuousOn

open scoped ComplexOrder in
/-- Euler differential recursion on the principal domain: for every `n : ℤ` and `z : ℂ` with
`1 - z ∈ Complex.slitPlane` (including `z = 0`), `z * deriv (polylog (n + 1)) z = polylog n z`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  set Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane} with hΩ_def
  have h0 : (0 : ℂ) ∈ Ω := by simp [hΩ_def, Complex.one_mem_slitPlane]
  have hf : AnalyticOnNhd ℂ (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w) Ω :=
    fun w hw ↦ analyticAt_id.mul ((analyticOnNhd_polylog (n + 1)).deriv w hw)
  have hloc : (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w) =ᶠ[𝓝 (0 : ℂ)] polylog n := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    exact mul_deriv_polylog_add_one_of_norm_lt_one n (by simpa using hw)
  have hconn : IsPreconnected Ω :=
    ((TauCeti.starConvex_one_sub_slitPlane zero_lt_one).isPathConnected
      h0).isConnected.isPreconnected
  exact hf.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_polylog n) hconn h0 hloc hz

/-- Unshifted Euler differential recursion on the principal domain: for every `n : ℤ` and `z : ℂ`
with `1 - z ∈ Complex.slitPlane` (including `z = 0`),
`z * deriv (polylog n) z = polylog (n - 1) z`. -/
theorem mul_deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog n) z = polylog (n - 1) z := by
  simpa using mul_deriv_polylog_add_one (n - 1) hz

/-- Quotient form of the Euler differential recursion away from `0`: for `1 - z ∈ slitPlane` and
`z ≠ 0`, `polylog n` has complex derivative `polylog (n - 1) z / z`. -/
theorem hasDerivAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    HasDerivAt (polylog n) (polylog (n - 1) z / z) z := by
  have hd := (differentiableAt_polylog n hz).hasDerivAt
  have heq : deriv (polylog n) z = polylog (n - 1) z / z := by
    rw [← mul_deriv_polylog n hz, mul_div_cancel_left₀ _ hz0]
  rwa [heq] at hd

/-- Shifted quotient form of the Euler differential recursion away from `0`: for
`1 - z ∈ slitPlane` and `z ≠ 0`, `polylog (n + 1)` has complex derivative `polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hz0 : z ≠ 0) :
    HasDerivAt (polylog (n + 1)) (polylog n z / z) z := by
  simpa using hasDerivAt_polylog (n + 1) hz hz0

/-- Away from `0` in the principal domain, `deriv (polylog n) z = polylog (n - 1) z / z`. -/
theorem deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog n) z = polylog (n - 1) z / z :=
  (hasDerivAt_polylog n hz hz0).deriv

/-- Away from `0` in the principal domain, `deriv (polylog (n + 1)) z = polylog n z / z`. -/
theorem deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z :=
  (hasDerivAt_polylog_add_one n hz hz0).deriv

/-- Continuity on `uIcc 0 1` of the radial derivative `t ↦ deriv (polylog n) (t * z) * z` for
`1 - z ∈ Complex.slitPlane`. -/
private lemma continuousOn_deriv_polylog_mul (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ ↦ deriv (polylog n) ((t : ℂ) * z) * z) (uIcc 0 1) := by
  refine ((analyticOnNhd_polylog n).deriv.continuousOn.comp
    (Complex.continuous_ofReal.mul continuous_const).continuousOn ?_).mul continuousOn_const
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  change 1 - (t : ℂ) * z ∈ Complex.slitPlane
  exact mul_comm z (t : ℂ) ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz ht

/-- On `uIoc 0 1`, the radial derivative `deriv (polylog (n + 1)) (t * z) * z` equals
`polylog n (t * z) / t`. -/
private lemma deriv_polylog_add_one_ofReal_mul_eq_div (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) {t : ℝ} (ht : t ∈ uIoc (0 : ℝ) 1) :
    deriv (polylog (n + 1)) ((t : ℂ) * z) * z = polylog n ((t : ℂ) * z) / (t : ℂ) := by
  rw [uIoc_of_le zero_le_one] at ht
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
  have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
    mul_comm z (t : ℂ) ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioc_subset_Icc_self ht)
  rw [← mul_deriv_polylog_add_one n hslit]
  field_simp [htc]

/-- For every `n : ℤ` and `z` in the principal domain `{z | 1 - z ∈ slitPlane}`, the radial
quotient `t ↦ polylog n (t * z) / t` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_div (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 := by
  refine (continuousOn_deriv_polylog_mul (n + 1) hz).intervalIntegrable.congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact deriv_polylog_add_one_ofReal_mul_eq_div n hz ht

/-- Recursive radial-integral identity: for every `n : ℤ` and `z` in the principal domain
`{z | 1 - z ∈ slitPlane}`, `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ polylog (n + 1) ((s : ℂ) * z))
        (deriv (polylog (n + 1)) ((t : ℂ) * z) * z) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      mul_comm z (t : ℂ) ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
    have hlin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) (1 * z) t :=
      (Complex.ofRealCLM.hasDerivAt).mul_const z
    rw [one_mul] at hlin
    exact (differentiableAt_polylog (n + 1) hslit).hasDerivAt.comp t hlin
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_deriv_polylog_mul (n + 1) hz).intervalIntegrable
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, polylog_zero,
    sub_zero] at hftc
  rw [← hftc]
  exact intervalIntegral.integral_congr_ae
    (ae_of_all _ fun t ht ↦ deriv_polylog_add_one_ofReal_mul_eq_div n hz ht)

/-- Unshifted recursive radial-integral identity: for every `n : ℤ` and `z` in the principal domain
`{z | 1 - z ∈ slitPlane}`, `polylog n z = ∫ t in 0..1, polylog (n - 1) (t * z) / t`. -/
theorem polylog_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n z = ∫ t : ℝ in 0..1, polylog (n - 1) ((t : ℂ) * z) / (t : ℂ) := by
  simpa using polylog_add_one_eq_integral (n - 1) hz

/-- `polylog 1` is discontinuous at its logarithmic branch point `1`. -/
private lemma not_continuousAt_polylog_one_one : ¬ ContinuousAt (polylog 1) 1 := by
  intro hc
  have hlim1 : Tendsto (fun w : ℂ ↦ Complex.exp (-polylog 1 w)) (𝓝[≠] 1) (𝓝 1) := by
    have hcont : ContinuousAt (fun w : ℂ ↦ Complex.exp (-polylog 1 w)) 1 :=
      Complex.continuous_exp.continuousAt.comp hc.neg
    simpa [polylog_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun w : ℂ ↦ Complex.exp (-polylog 1 w)) (𝓝[≠] 1) (𝓝 0) := by
    have hsub : Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[≠] (1 : ℂ)) (𝓝 (1 - 1)) :=
      (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    rw [sub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
    simp [polylog_one, Complex.exp_log hw']
  exact one_ne_zero (tendsto_nhds_unique hlim1 hlim0)

/-- On the open branch cut `(1, ∞)`, `polylog 1` has a `2πi` jump discontinuity. -/
private lemma not_continuousAt_polylog_one_of_one_lt {x : ℝ} (hx : 1 < x) :
    ¬ ContinuousAt (polylog 1) (x : ℂ) := by
  intro hc
  set w : ℂ := 1 - (x : ℂ) with hw_def
  have hw_re : w.re < 0 := by simp [hw_def]; linarith
  have hw_im : w.im = 0 := by simp [hw_def]
  set r : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  set u : ℕ → ℂ := fun n ↦ (x : ℂ) + (r n : ℂ) * Complex.I
  have hu_lim : Tendsto u atTop (𝓝 (x : ℂ)) := by
    have hinv : Tendsto r atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [u] using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hinv |>.mul_const Complex.I)
  have h1u_lim : Tendsto (fun n : ℕ ↦ 1 - u n) atTop (𝓝[{z : ℂ | z.im < 0}] w) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_const_nhds.sub hu_lim), .of_forall fun n ↦ ?_⟩
    have hrpos : 0 < r n := inv_pos.2 (by positivity)
    simp only [u, mem_ofPred_eq, Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      zero_add, zero_sub, Left.neg_neg_iff]
    exact hrpos
  have hupper : Tendsto (fun n : ℕ ↦ polylog 1 (u n)) atTop
      (𝓝 (-(Real.log ‖w‖ - Real.pi * Complex.I))) := by
    simpa only [polylog_one, Function.comp_def] using
      ((Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hw_re hw_im).comp h1u_lim).neg
  have hlower : Tendsto (fun n : ℕ ↦ polylog 1 (u n)) atTop (𝓝 (polylog 1 (x : ℂ))) :=
    hc.tendsto.comp hu_lim
  have heq := tendsto_nhds_unique hupper hlower
  have him := congrArg Complex.im heq
  simp only [polylog_one, ← hw_def, Complex.neg_im, Complex.log_im,
    Complex.arg_eq_pi_iff.2 ⟨hw_re, hw_im⟩, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_im, Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero, zero_sub,
    neg_neg] at him
  linarith [Real.pi_pos]

/-- Along the closed branch cut `[1, ∞)`, `polylog 1` is everywhere discontinuous: it has a
logarithmic singularity at `1` and a `2πi` jump across `(1, ∞)`. -/
theorem not_continuousAt_polylog_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    ¬ ContinuousAt (polylog 1) (x : ℂ) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simpa using not_continuousAt_polylog_one_one
  · exact not_continuousAt_polylog_one_of_one_lt hx'

/-- `polylog 1` is continuous at `z` if and only if `z` lies in the principal domain
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem continuousAt_polylog_one_iff {z : ℂ} :
    ContinuousAt (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane := by
  refine ⟨fun hc ↦ by_contra fun hz ↦ ?_, continuousAt_polylog 1⟩
  rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hz
  have hzim : z.im = 0 := by simpa using hz.2
  have hzre : 1 ≤ z.re := by simpa using hz.1
  have hzeq : (z.re : ℂ) = z := Complex.ext rfl hzim.symm
  exact not_continuousAt_polylog_one_of_one_le hzre (hzeq ▸ hc)

/-- `polylog 1` is complex analytic at `z` if and only if `z` lies in the principal domain
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticAt_polylog_one_iff {z : ℂ} :
    AnalyticAt ℂ (polylog 1) z ↔ 1 - z ∈ Complex.slitPlane :=
  ⟨fun ha ↦ continuousAt_polylog_one_iff.1 ha.continuousAt, analyticAt_polylog 1⟩

/-- In particular, `polylog 1` is not continuous at `3`, showing that `analyticOnNhd_polylog`
cannot extend across the branch cut `[1, ∞)`. -/
theorem not_continuousAt_polylog_one_three : ¬ ContinuousAt (polylog 1) 3 := by
  simpa using not_continuousAt_polylog_one_of_one_le (x := 3) (by norm_num)

end TauCeti.Polylog
