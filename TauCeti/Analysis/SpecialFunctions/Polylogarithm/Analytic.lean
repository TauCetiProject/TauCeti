/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Nonpositive
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Holomorphy, derivative recursion, and conjugation of principal polylogarithms

In every integer weight `n : ℤ`, the principal polylogarithm `TauCeti.Polylog.polylog n` is
holomorphic on the cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)` and satisfies
Euler's differential recursion `z * deriv (polylog (n + 1)) z = polylog n z` together with the
recursive radial-integral representation `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`.
Away from the cut `[1, ∞)`, principal polylogarithms also commute with complex conjugation, so
they take real values on `(-∞, 1)`; in nonpositive weights this conjugation compatibility extends
to all of `ℂ`.

These properties govern local continuation of the polylogarithm tower `(Log, Li₁, Li₂, …)` and
supply the differential equations used to prove the classical functional equations.

## Main declarations

* `TauCeti.Polylog.analyticOnNhd_polylog`: `polylog n` is complex analytic on
  `{z : ℂ | 1 - z ∈ Complex.slitPlane}` for every `n : ℤ`.
* `TauCeti.Polylog.mul_deriv_polylog_succ`: the Euler recursion
  `z * deriv (polylog (n + 1)) z = polylog n z` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.hasDerivAt_polylog_of_ne_zero`, `TauCeti.Polylog.deriv_polylog_of_ne_zero`:
  `deriv (polylog n) z = polylog (n - 1) z / z` for `z ≠ 0` with `1 - z ∈ Complex.slitPlane`.
* `TauCeti.Polylog.polylog_succ_eq_integral`: the recursive radial integral
  `polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.polylog_conj`, `TauCeti.Polylog.polylog_conj_of_nonpos`: compatibility with
  complex conjugation on `{z : ℂ | 1 - z ∈ Complex.slitPlane}` in all weights and on `ℂ` in
  nonpositive weights.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §§1.1–1.3, (1)–(3), pp. 50–51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
* Alexander B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology*,
  Advances in Mathematics 114 (1995), §1.0, (1.1), p. 201.
-/

public section

open Filter MeasureTheory Polynomial Set Topology

namespace TauCeti.Polylog

/-! ### Differentiation on the principal domain -/

/-- The derivative of `Li₁(z) = -Log(1 - z)` on the principal domain `ℂ ∖ [1, ∞)` is `1 / (1 - z)`,
including at `z = 0` where it equals `1`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) (1 / (1 - z)) z := by
  have hsub : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := (hasDerivAt_id' z).const_sub (1 : ℂ)
  have hlog : HasDerivAt (fun w : ℂ ↦ -Complex.log (1 - w)) (-((-1) / (1 - z))) z :=
    (hsub.clog hz).neg
  refine (hlog.congr_of_eventuallyEq (Eventually.of_forall polylog_one)).congr_deriv ?_
  ring

/-- The complex derivative of `Li₁` on the principal domain `ℂ ∖ [1, ∞)`. -/
theorem deriv_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog 1) z = 1 / (1 - z) :=
  (hasDerivAt_polylog_one hz).deriv

/-- Differentiating the radial integral of `Li_{k+2}` under the integral sign on `ℂ ∖ [1, ∞)`
gives `(1 / k!) ∫₀¹ (-log t)^k / (1 - t z) dt`, together with integrability of that integrand. -/
private lemma intervalIntegrable_and_hasDerivAt_polylog_nat_add_two (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
        (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 ∧
      HasDerivAt (polylog (k + 2 : ℕ))
        ((Nat.factorial k : ℂ)⁻¹ *
          ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  have hopen : IsOpen {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z hz
  set K : Set ℂ := Metric.closedBall z (ε / 2)
  have hK_nhds : K ∈ 𝓝 z := Metric.closedBall_mem_nhds z (half_pos hε)
  have hKΩ : K ⊆ {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨δ, hδ, hδK⟩ := exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z (ε / 2)) hKΩ
  set F : ℂ → ℝ → ℂ := fun w t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ)
  set F' : ℂ → ℝ → ℂ := fun w t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * w)
  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := z) (s := K) (bound := fun t : ℝ ↦ δ⁻¹ * |Real.log t| ^ k)
    (μ := volume) (a := 0) (b := 1) hK_nhds
    (Eventually.of_forall fun w ↦ (by fun_prop : Measurable (F w)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z)
    (by fun_prop : Measurable (F' z)).aestronglyMeasurable
    (ae_of_all _ fun t ht w hw ↦ ?_)
    (((intervalIntegrable_log_pow k).norm.const_mul δ⁻¹).congr fun t _ ↦ by
      simp [Real.norm_eq_abs])
    (ae_of_all _ fun t ht w hw ↦ ?_)
  · refine ⟨hdom.1, ?_⟩
    exact (hdom.2.const_mul (Nat.factorial k : ℂ)⁻¹).congr_of_eventuallyEq
      (Eventually.of_forall (polylog_nat_add_two k))
  · rw [uIoc_of_le zero_le_one] at ht
    have hwδ : δ ≤ ‖1 - (t : ℂ) * w‖ := hδK w hw t (Ioc_subset_Icc_self ht)
    have hinv : (‖1 - (t : ℂ) * w‖)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hwδ
    calc ‖F' w t‖
        = |Real.log t| ^ k * (‖1 - (t : ℂ) * w‖)⁻¹ := by
          simp [F', Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
      _ ≤ |Real.log t| ^ k * δ⁻¹ := by gcongr
      _ = δ⁻¹ * |Real.log t| ^ k := mul_comm _ _
  · rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hmem : 1 - (t : ℂ) * w ∈ Complex.slitPlane :=
      mul_comm (t : ℂ) w ▸ Complex.one_sub_mul_ofReal_mem_slitPlane (hKΩ hw)
        (Ioc_subset_Icc_self ht)
    have hne : 1 - (t : ℂ) * w ≠ 0 := Complex.slitPlane_ne_zero hmem
    have hsub : HasDerivAt (fun u : ℂ ↦ 1 - (t : ℂ) * u) (-(t : ℂ)) w :=
      (hasDerivAt_const_mul (t : ℂ)).const_sub (1 : ℂ)
    have hlog : HasDerivAt (fun u : ℂ ↦ -Complex.log (1 - (t : ℂ) * u))
        (-(-(t : ℂ) / (1 - (t : ℂ) * w))) w :=
      (hsub.clog hmem).neg
    refine ((hlog.const_mul (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)).congr_deriv ?_
    dsimp only [F']
    field_simp

/-- Integral representation of the derivative of `Li_{k+2}` on `ℂ ∖ [1, ∞)`, valid at every point
of the principal domain including `z = 0`. -/
theorem hasDerivAt_polylog_nat_add_two_integral (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z :=
  (intervalIntegrable_and_hasDerivAt_polylog_nat_add_two k hz).2

/-- Every integer-weight polylogarithm is complex differentiable at each point of `ℂ ∖ [1, ∞)`. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z := by
  have hne : z ≠ 1 := by rintro rfl; simp at hz
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (analyticAt_polylog_neg_nat 0 hne).differentiableAt
    · exact (hasDerivAt_polylog_one hz).differentiableAt
    · exact (hasDerivAt_polylog_nat_add_two_integral k hz).differentiableAt
  | negSucc r =>
    exact (analyticAt_polylog_neg_nat (r + 1) hne).differentiableAt

/-- Every integer-weight polylogarithm is complex differentiable on `ℂ ∖ [1, ∞)`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ (differentiableAt_polylog n hz).differentiableWithinAt

/-- Every integer-weight polylogarithm is holomorphic on the principal domain `ℂ ∖ [1, ∞)`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).analyticOnNhd (Complex.isOpen_slitPlane.preimage (by fun_prop))

/-- Every integer-weight polylogarithm is complex analytic at each point of `ℂ ∖ [1, ∞)`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- Every integer-weight polylogarithm is continuous at each point of `ℂ ∖ [1, ∞)`. -/
theorem continuousAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousAt (polylog n) z :=
  (differentiableAt_polylog n hz).continuousAt

/-- Every integer-weight polylogarithm is continuous on `ℂ ∖ [1, ∞)`. -/
theorem continuousOn_polylog (n : ℤ) :
    ContinuousOn (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).continuousOn

/-! ### Euler's differential recursion and the recursive radial integral -/

private lemma hasDerivAt_polylog_one_ofReal_mul {z : ℂ} {t : ℝ}
    (hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ ↦ polylog 1 ((s : ℂ) * z)) (z / (1 - (t : ℂ) * z)) t := by
  have hlin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).mul_const z
  refine ((hasDerivAt_polylog_one hmem).comp t hlin).congr_deriv ?_
  ring

private lemma tendsto_neg_log_pow_mul_polylog_one_nhdsGT_zero (m : ℕ) (z : ℂ) :
    Tendsto
      (fun t : ℝ ↦ ((Nat.factorial (m + 1) : ℂ)⁻¹ * ((-Real.log t : ℝ) : ℂ) ^ (m + 1)) *
        polylog 1 ((t : ℂ) * z))
      (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hexp : (0 : ℝ) < (m + 1 : ℝ)⁻¹ := by positivity
  have hpow : Tendsto
      (fun t : ℝ ↦ (-(Real.log t * t ^ ((m + 1 : ℝ)⁻¹))) ^ (m + 1))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_log_mul_rpow_nhdsGT_zero hexp).neg).pow (m + 1)
  have hbound_lim : Tendsto
      (fun t : ℝ ↦ ((Nat.factorial (m + 1) : ℝ)⁻¹ * (3 / 2 * ‖z‖)) *
        (-(Real.log t * t ^ ((m + 1 : ℝ)⁻¹))) ^ (m + 1))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hpow.const_mul ((Nat.factorial (m + 1) : ℝ)⁻¹ * (3 / 2 * ‖z‖))
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound_lim
  have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have h2 : ∀ᶠ t : ℝ in 𝓝[>] 0, t * ‖z‖ ≤ 1 / 2 := by
    have hlim : Tendsto (fun t : ℝ ↦ t * ‖z‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using
        ((by fun_prop : Continuous fun t : ℝ ↦ t * ‖z‖).tendsto 0).mono_left nhdsWithin_le_nhds
    exact (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ ht ↦ ht.le
  filter_upwards [self_mem_nhdsWithin, h1, h2] with t ht0 ht1 htz
  have ht0' : 0 < t := ht0
  have hnorm : ‖-((t : ℂ) * z)‖ = t * ‖z‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0'.le]
  have hlog : ‖Complex.log (1 - (t : ℂ) * z)‖ ≤ 3 / 2 * (t * ‖z‖) := by
    have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) (by rwa [hnorm])
    rwa [hnorm, ← sub_eq_add_neg] at h
  have hlog_neg : Real.log t < 0 := Real.log_neg ht0' ht1
  have hrpow_id : (-(Real.log t * t ^ ((m + 1 : ℝ)⁻¹))) ^ (m + 1) =
      |Real.log t| ^ (m + 1) * t := by
    have hm : (m + 1 : ℝ) ≠ 0 := by positivity
    rw [abs_of_neg hlog_neg, ← neg_mul, mul_pow, ← Real.rpow_natCast (t ^ _) (m + 1),
      ← Real.rpow_mul ht0'.le, Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ hm, Real.rpow_one]
  calc ‖((Nat.factorial (m + 1) : ℂ)⁻¹ * ((-Real.log t : ℝ) : ℂ) ^ (m + 1)) *
          polylog 1 ((t : ℂ) * z)‖
      = (Nat.factorial (m + 1) : ℝ)⁻¹ * |Real.log t| ^ (m + 1) *
          ‖Complex.log (1 - (t : ℂ) * z)‖ := by
        simp [polylog_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (Nat.factorial (m + 1) : ℝ)⁻¹ * |Real.log t| ^ (m + 1) * (3 / 2 * (t * ‖z‖)) := by
        gcongr
    _ = ((Nat.factorial (m + 1) : ℝ)⁻¹ * (3 / 2 * ‖z‖)) *
          (|Real.log t| ^ (m + 1) * t) := by ring
    _ = ((Nat.factorial (m + 1) : ℝ)⁻¹ * (3 / 2 * ‖z‖)) *
          (-(Real.log t * t ^ ((m + 1 : ℝ)⁻¹))) ^ (m + 1) := by rw [hrpow_id]

private lemma hasDerivAt_radialAntideriv (m : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ ↦ ((Nat.factorial (m + 1) : ℂ)⁻¹ * ((-Real.log s : ℝ) : ℂ) ^ (m + 1)) *
        polylog 1 ((s : ℂ) * z))
      (z * ((Nat.factorial (m + 1) : ℂ)⁻¹ *
          (((-Real.log t : ℝ) : ℂ) ^ (m + 1) / (1 - (t : ℂ) * z))) -
        (Nat.factorial m : ℂ)⁻¹ *
          (((-Real.log t : ℝ) : ℂ) ^ m * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ))) t := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hm1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hfac : (Nat.factorial m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hlogt : HasDerivAt (fun s : ℝ ↦ ((-Real.log s : ℝ) : ℂ)) (-(t : ℂ)⁻¹) t := by
    simpa using ((Real.hasDerivAt_log ht.1.ne').neg).ofReal_comp
  have hpow : HasDerivAt
      (fun s : ℝ ↦ (Nat.factorial (m + 1) : ℂ)⁻¹ * ((-Real.log s : ℝ) : ℂ) ^ (m + 1))
      (-((Nat.factorial m : ℂ)⁻¹ * ((-Real.log t : ℝ) : ℂ) ^ m / (t : ℂ))) t := by
    refine ((hlogt.pow (m + 1)).const_mul (Nat.factorial (m + 1) : ℂ)⁻¹).congr_deriv ?_
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
    mul_comm (t : ℂ) z ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioo_subset_Icc_self ht)
  refine (hpow.mul (hasDerivAt_polylog_one_ofReal_mul hmem)).congr_deriv ?_
  rw [polylog_one]
  ring

private lemma mul_deriv_polylog_nat_add_three (m : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (m + 3 : ℕ)) z = polylog (m + 2 : ℕ) z := by
  have hd := (hasDerivAt_polylog_nat_add_two_integral (m + 1) hz).deriv
  have hcast : ((m + 3 : ℕ) : ℤ) = ((m + 1 + 2 : ℕ) : ℤ) := rfl
  rw [hcast, hd]
  set G : ℝ → ℂ := fun t ↦
    ((Nat.factorial (m + 1) : ℂ)⁻¹ * ((-Real.log t : ℝ) : ℂ) ^ (m + 1)) * polylog 1 ((t : ℂ) * z)
  set g₁ : ℝ → ℂ := fun t ↦
    (Nat.factorial m : ℂ)⁻¹ *
      (((-Real.log t : ℝ) : ℂ) ^ m * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ))
  set g₂ : ℝ → ℂ := fun t ↦
    z * ((Nat.factorial (m + 1) : ℂ)⁻¹ *
      (((-Real.log t : ℝ) : ℂ) ^ (m + 1) / (1 - (t : ℂ) * z)))
  have hg₁_int : IntervalIntegrable g₁ volume 0 1 :=
    (intervalIntegrable_radialIntegrand m z).const_mul (Nat.factorial m : ℂ)⁻¹
  have hg₂_int : IntervalIntegrable g₂ volume 0 1 :=
    ((intervalIntegrable_and_hasDerivAt_polylog_nat_add_two (m + 1) hz).1.const_mul
      (Nat.factorial (m + 1) : ℂ)⁻¹).const_mul z
  have hG1 : Tendsto G (𝓝[<] 1) (𝓝 0) := by
    have hlog1 : ContinuousAt (fun s : ℝ ↦ ((-Real.log s : ℝ) : ℂ)) 1 :=
      (((Real.hasDerivAt_log one_ne_zero).neg).ofReal_comp).continuousAt
    have h1 : ContinuousAt
        (fun s : ℝ ↦ (Nat.factorial (m + 1) : ℂ)⁻¹ * ((-Real.log s : ℝ) : ℂ) ^ (m + 1)) 1 :=
      continuousAt_const.mul (hlog1.pow (m + 1))
    have h2 : ContinuousAt (fun s : ℝ ↦ polylog 1 ((s : ℂ) * z)) 1 :=
      (hasDerivAt_polylog_one_ofReal_mul (by simpa using hz)).continuousAt
    have hval : G 1 = 0 := by simp [G]
    rw [← hval]
    exact (h1.mul h2).tendsto.mono_left nhdsWithin_le_nhds
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun t ht ↦ hasDerivAt_radialAntideriv m hz ht) (hg₂_int.sub hg₁_int)
    (tendsto_neg_log_pow_mul_polylog_one_nhdsGT_zero m z) hG1
  rw [sub_zero, intervalIntegral.integral_sub hg₂_int hg₁_int, sub_eq_zero] at hftc
  calc z * ((Nat.factorial (m + 1) : ℂ)⁻¹ *
          ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ (m + 1) / (1 - (t : ℂ) * z))
      = ∫ t : ℝ in 0..1, g₂ t := by simp only [g₂, intervalIntegral.integral_const_mul]
    _ = ∫ t : ℝ in 0..1, g₁ t := hftc
    _ = polylog (m + 2 : ℕ) z := by
        simp only [g₁, intervalIntegral.integral_const_mul, polylog_nat_add_two]

/-- Euler's differential recursion `z * deriv (polylog (n + 1)) z = polylog n z` holds in every
integer weight `n : ℤ` and at every point `z` of the principal domain `ℂ ∖ [1, ∞)`, including
`z = 0`. -/
theorem mul_deriv_polylog_succ (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  cases n with
  | negSucc r =>
    have hn : (Int.negSucc r) + 1 = -(r : ℤ) := by omega
    have hn' : Int.negSucc r = -((r + 1 : ℕ) : ℤ) := rfl
    rw [hn, hn', polylog_neg_nat_succ]
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast]
    rcases m with _ | _ | m
    · simp only [Nat.cast_zero, zero_add]
      rw [deriv_polylog_one hz, polylog_zero_weight]
      ring
    · have hd := (hasDerivAt_polylog_nat_add_two_integral 0 hz).deriv
      have hcast : ((0 + 1 : ℕ) : ℤ) + 1 = ((0 + 2 : ℕ) : ℤ) := by norm_num
      rw [hcast, hd]
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, zero_add]
      have hint : IntervalIntegrable (fun t : ℝ ↦ z / (1 - (t : ℂ) * z)) volume 0 1 :=
        ((intervalIntegrable_and_hasDerivAt_polylog_nat_add_two 0 hz).1.const_mul z).congr
          fun t _ ↦ by simp [div_eq_mul_inv]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (f := fun t : ℝ ↦ polylog 1 ((t : ℂ) * z))
        (f' := fun t : ℝ ↦ z / (1 - (t : ℂ) * z))
        (fun t ht ↦ hasDerivAt_polylog_one_ofReal_mul (mul_comm (t : ℂ) z ▸
          Complex.one_sub_mul_ofReal_mem_slitPlane hz (by simpa [uIcc_of_le zero_le_one] using ht)))
        hint
      calc z * ∫ t : ℝ in 0..1, 1 / (1 - (t : ℂ) * z)
          = ∫ t : ℝ in 0..1, z / (1 - (t : ℂ) * z) := by
            rw [← intervalIntegral.integral_const_mul]
            exact intervalIntegral.integral_congr fun t _ ↦ by simp [div_eq_mul_inv]
        _ = polylog 1 z := by simpa using hftc
    · have hcast : ((m + 2 : ℕ) : ℤ) + 1 = ((m + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast]
      exact mul_deriv_polylog_nat_add_three m hz

/-- Away from `0` on the principal domain `ℂ ∖ [1, ∞)`, the complex derivative of `polylog n` is
`polylog (n - 1) z / z`. -/
theorem deriv_polylog_of_ne_zero (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog n) z = polylog (n - 1) z / z := by
  have h := mul_deriv_polylog_succ (n - 1) hz
  rw [sub_add_cancel] at h
  exact eq_div_of_mul_eq hz0 (by rwa [mul_comm])

/-- Away from `0` on the principal domain `ℂ ∖ [1, ∞)`, `polylog n` has complex derivative
`polylog (n - 1) z / z`. -/
theorem hasDerivAt_polylog_of_ne_zero (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hz0 : z ≠ 0) :
    HasDerivAt (polylog n) (polylog (n - 1) z / z) z := by
  rw [← deriv_polylog_of_ne_zero n hz hz0]
  exact (differentiableAt_polylog n hz).hasDerivAt

/-- For every integer weight `n` and `z ∈ ℂ ∖ [1, ∞)`, the radial quotient
`t ↦ polylog n (t * z) / t` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_div (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 := by
  set f : ℝ → ℂ := fun t ↦ polylog n ((t : ℂ) * z)
  have hf_cont : ContinuousOn f (Icc 0 1) := by
    intro t ht
    have hmul : ContinuousAt (fun s : ℝ ↦ (s : ℂ) * z) t :=
      (by fun_prop : Continuous fun s : ℝ ↦ (s : ℂ) * z).continuousAt
    have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      mul_comm (t : ℂ) z ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
    exact (ContinuousAt.comp (f := fun s : ℝ ↦ (s : ℂ) * z)
      (continuousAt_polylog n hmem) hmul).continuousWithinAt
  have hf_diff : DifferentiableAt ℝ f 0 := by
    have h0 : 1 - (0 : ℂ) * z ∈ Complex.slitPlane := by simp
    have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * z) z 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const z
    exact ((differentiableAt_polylog n h0).hasDerivAt.comp (0 : ℝ) hlin).differentiableAt
  have hdslope : ContinuousOn (dslope f 0) (Icc 0 1) := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · exact (continuousAt_dslope_same.2 hf_diff).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne ht0).2 (hf_cont t ht)
  refine (hdslope.intervalIntegrable_of_Icc zero_le_one).congr fun t ht ↦ ?_
  rw [uIoc_of_le zero_le_one] at ht
  rw [dslope_of_ne _ ht.1.ne', slope_def_module]
  simp [f, Complex.real_smul, div_eq_inv_mul]

/-- The recursive radial-integral representation `Li_{n+1}(z) = ∫₀¹ Liₙ(t z) / t dt` holds for
every integer weight `n : ℤ` and every `z ∈ ℂ ∖ [1, ∞)`. -/
theorem polylog_succ_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  set H : ℝ → ℂ := fun t ↦ polylog (n + 1) ((t : ℂ) * z)
  have hH_cont : ContinuousOn H (Icc 0 1) := by
    intro t ht
    have hmul : ContinuousAt (fun s : ℝ ↦ (s : ℂ) * z) t :=
      (by fun_prop : Continuous fun s : ℝ ↦ (s : ℂ) * z).continuousAt
    have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      mul_comm (t : ℂ) z ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
    exact (ContinuousAt.comp (f := fun s : ℝ ↦ (s : ℂ) * z)
      (continuousAt_polylog (n + 1) hmem) hmul).continuousWithinAt
  have hH_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt H (polylog n ((t : ℂ) * z) / (t : ℂ)) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      mul_comm (t : ℂ) z ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioo_subset_Icc_self ht)
    have hlin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const z
    have hcomp := ((differentiableAt_polylog (n + 1) hmem).hasDerivAt.comp t hlin)
    refine hcomp.congr_deriv ?_
    have hrec := mul_deriv_polylog_succ n hmem
    apply eq_div_of_mul_eq ht0
    calc deriv (polylog (n + 1)) ((t : ℂ) * z) * z * (t : ℂ)
        = ((t : ℂ) * z) * deriv (polylog (n + 1)) ((t : ℂ) * z) := by ring
      _ = polylog n ((t : ℂ) * z) := hrec
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hH_cont hH_deriv
    (intervalIntegrable_polylog_div n hz)
  simpa [H] using hftc.symm

/-! ### Conjugation compatibility -/

/-- Nonpositive-weight polylogarithms commute with complex conjugation everywhere on `ℂ`,
including at the totalised pole `z = 1`. -/
theorem polylog_neg_nat_conj (r : ℕ) (z : ℂ) :
    polylog (-(r : ℤ)) (starRingEnd ℂ z) = starRingEnd ℂ (polylog (-(r : ℤ)) z) := by
  rw [polylog_neg_nat_eq_div, polylog_neg_nat_eq_div]
  have haeval : aeval (starRingEnd ℂ z) (eulerianPolynomial r) =
      starRingEnd ℂ (aeval z (eulerianPolynomial r)) := by
    simp [aeval_def]
  simp [haeval]

/-- For every nonpositive integer weight `n ≤ 0`, `polylog n` commutes with complex conjugation
on all of `ℂ`. -/
theorem polylog_conj_of_nonpos {n : ℤ} (hn : n ≤ 0) (z : ℂ) :
    polylog n (starRingEnd ℂ z) = starRingEnd ℂ (polylog n z) := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast] at hn ⊢
    obtain rfl : m = 0 := by omega
    exact polylog_neg_nat_conj 0 z
  | negSucc r =>
    exact polylog_neg_nat_conj (r + 1) z

/-- On the principal domain `ℂ ∖ [1, ∞)`, every integer-weight polylogarithm commutes with complex
conjugation. -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n (starRingEnd ℂ z) = starRingEnd ℂ (polylog n z) := by
  cases n with
  | negSucc r => exact polylog_neg_nat_conj (r + 1) z
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast]
    rcases m with _ | _ | k
    · exact polylog_neg_nat_conj 0 z
    · simp only [zero_add, Nat.cast_one, polylog_one, map_neg]
      have hsub : 1 - starRingEnd ℂ z = starRingEnd ℂ (1 - z) := by
        rw [map_sub, map_one]
      rw [hsub, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hz)]
    · have hcast : ((k + 1 + 1 : ℕ) : ℤ) = ((k + 2 : ℕ) : ℤ) := rfl
      rw [hcast, polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀, map_natCast,
        intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
        ← integral_conj]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
        mul_comm (t : ℂ) z ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioc_subset_Icc_self ht)
      have hsub : 1 - (t : ℂ) * starRingEnd ℂ z = starRingEnd ℂ (1 - (t : ℂ) * z) := by
        rw [map_sub, map_one, map_mul, Complex.conj_ofReal]
      rw [hsub, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hmem)]
      simp

/-- On the real ray `(-∞, 1)`, every principal polylogarithm has zero imaginary part. -/
theorem im_polylog_ofReal_eq_zero (n : ℤ) {x : ℝ} (hx : x < 1) :
    (polylog n x).im = 0 := by
  have hz : 1 - (x : ℂ) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_mem_slitPlane]
    linarith
  have hconj := polylog_conj n hz
  simp only [Complex.conj_ofReal] at hconj
  exact Complex.conj_eq_iff_im.mp hconj.symm

/-- On the real ray `(-∞, 1)`, every principal polylogarithm equals its real part. -/
theorem ofReal_re_polylog_ofReal (n : ℤ) {x : ℝ} (hx : x < 1) :
    ((polylog n x).re : ℂ) = polylog n x :=
  Complex.ext (by simp) (by simp [im_polylog_ofReal_eq_zero n hx])

/-! ### Checks and cut witnesses -/

/-- At `z = -1`, the weight-three derivative satisfies `-Li₃'(-1) = Li₂(-1)`. -/
theorem deriv_polylog_three_neg_one :
    deriv (polylog 3) (-1) = -polylog 2 (-1) := by
  have hz : 1 - (-1 : ℂ) ∈ Complex.slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  rw [deriv_polylog_of_ne_zero 3 hz (by norm_num)]
  norm_num
  ring

/-- `Li₁` is not continuous at any point `x > 1` of the real branch cut. -/
theorem not_continuousAt_polylog_one_of_one_lt {x : ℝ} (hx : 1 < x) :
    ¬ ContinuousAt (polylog 1) x := by
  intro hc
  have hpath : Continuous (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  have hlim : Tendsto (fun y : ℝ ↦ (polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (-Real.pi)) := by
    have hc0 : ContinuousAt (polylog 1) ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by simpa using hc
    have hcont1 : ContinuousAt (fun y : ℝ ↦ polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I)) 0 :=
      ContinuousAt.comp (f := fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) hc0 hpath.continuousAt
    have hcont : ContinuousAt (fun y : ℝ ↦ (polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I)).im) 0 :=
      ContinuousAt.comp (f := fun y : ℝ ↦ polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I))
        Complex.continuous_im.continuousAt hcont1
    have hval : (polylog 1 ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)).im = -Real.pi := by
      have hneg : 1 - x < 0 := by linarith
      simp only [Complex.ofReal_zero, zero_mul, add_zero, polylog_one, Complex.neg_im,
        Complex.log_im, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.arg_ofReal_of_neg hneg]
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hnonneg : ∀ᶠ y : ℝ in 𝓝[>] 0,
      0 ≤ (polylog 1 ((x : ℂ) + (y : ℂ) * Complex.I)).im := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : 0 < y := hy
    have him : (1 - ((x : ℂ) + (y : ℂ) * Complex.I)).im < 0 := by simp [hy']
    have harg : (1 - ((x : ℂ) + (y : ℂ) * Complex.I)).arg < 0 :=
      Complex.arg_neg_iff.mpr him
    simp only [polylog_one, Complex.neg_im, Complex.log_im]
    linarith
  have hle : (0 : ℝ) ≤ -Real.pi := ge_of_tendsto hlim hnonneg
  linarith [Real.pi_pos]

/-- Conjugation compatibility fails on the positive-weight branch cut `(1, ∞)`: at `z = 3`,
`Li₁(conj 3) ≠ conj(Li₁(3))`. -/
theorem polylog_one_conj_three_ne :
    polylog 1 (starRingEnd ℂ 3) ≠ starRingEnd ℂ (polylog 1 3) := by
  intro h
  have h3 : starRingEnd ℂ (3 : ℂ) = 3 := by simp [map_ofNat]
  rw [h3, polylog_one_three] at h
  have him := congr_arg Complex.im h
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, Complex.conj_im] at him
  linarith [Real.pi_pos]

end TauCeti.Polylog
