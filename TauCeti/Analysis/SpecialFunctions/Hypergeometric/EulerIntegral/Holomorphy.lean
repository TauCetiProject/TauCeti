/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy

/-!
# Joint holomorphy of Euler's integral in its parameters

Euler's integral `∫₀¹ t^(b-1) (1-t)^(c-b-1) (1-zt)^(-a) dt` (DLMF 15.6.1) is holomorphic in
`(a, b, c, z)` jointly, as a function on `ℂ × ℂ × ℂ × ℂ`, on the region where `0 < re b < re c`
and `1 - z ∈ Complex.slitPlane`. So is its normalization `Complex.eulerIntegral` by
`(Γ(b) Γ(c - b))⁻¹`, whose prefactor is entire. For fixed `b`, `c` the holomorphy in `(a, z)` is
`Complex.analyticOnNhd_eulerIntegral`.

For each `t ∈ (0, 1)` the integrand is holomorphic in the parameters. Near a point
`(a₀, b₀, c₀, z₀)` of the region it is bounded by `C t^(β-1) (1-t)^(γ-1)`, a Beta integrand, with
`β = re b₀ / 2`, `γ = re (c₀ - b₀) / 2`, and `C` a bound for `(1 - zt)^(-a)` on a compact
neighbourhood. Holomorphy then follows from `TauCeti.analyticOnNhd_integral_of_dominated`.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Hypergeometric/ParameterHolomorphy.lean`.

## Main results

* `Complex.analyticOnNhd_integral_eulerIntegrand_joint`: the unnormalized integral is jointly
  holomorphic in `(a, b, c, z)`.
* `Complex.analyticOnNhd_eulerIntegral_joint`: so is `Complex.eulerIntegral`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equation 15.6.1.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace Complex

/-- Near a point of the region `0 < re b < re c`, `1 - z ∈ slitPlane`, Euler's integrand is
bounded for `t ∈ (0, 1)`, uniformly in the parameters, by an integrable function of `t`. -/
theorem exists_bound_eulerIntegrand {q₀ : ℂ × ℂ × ℂ × ℂ} (hb : 0 < q₀.2.1.re)
    (hbc : q₀.2.1.re < q₀.2.2.1.re) (hz : 1 - q₀.2.2.2 ∈ slitPlane) :
    ∃ N ∈ 𝓝 q₀, ∃ bound : ℝ → ℝ, Integrable bound (volume.restrict (Ioo 0 1)) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ q ∈ N, ‖(t : ℂ) ^ (q.2.1 - 1) *
        (1 - (t : ℂ)) ^ (q.2.2.1 - q.2.1 - 1) * (1 - q.2.2.2 * t) ^ (-q.1)‖ ≤ bound t := by
  obtain ⟨a₀, b₀, c₀, z₀⟩ := q₀
  -- A closed disc around `z₀` on which `1 - z` stays in the slit plane.
  obtain ⟨ε, hε, hεz⟩ := Metric.isOpen_iff.mp
    (isOpen_slitPlane.preimage (continuous_const.sub continuous_id)) z₀ hz
  have hρ : closedBall z₀ (ε / 2) ⊆ {z | 1 - z ∈ slitPlane} :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεz
  -- The kernel `(1 - z t)^(-a)` is bounded on a compact neighbourhood.
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod ((isCompact_closedBall a₀ 1).prod
    (isCompact_closedBall z₀ (ε / 2)))).exists_bound_of_continuousOn
    (f := fun p : ℝ × ℂ × ℂ ↦ (1 - p.2.2 * p.1) ^ (-p.2.1)) <| by
      refine continuousOn_of_forall_continuousAt fun p hp ↦ ?_
      exact ContinuousAt.cpow (by fun_prop) (by fun_prop)
        (one_sub_mul_ofReal_mem_slitPlane (hρ hp.2.2) hp.1)
  set β := b₀.re / 2
  set γ := (c₀ - b₀).re / 2
  have hβ : 0 < β := half_pos hb
  have hγ : 0 < γ := half_pos (by simpa using sub_pos.mpr hbc)
  -- Lower exponents bound complex powers of numbers in `(0, 1)`.
  have hpow {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {w : ℂ} {δ : ℝ} (hw : δ ≤ w.re) :
      ‖(x : ℂ) ^ (w - 1)‖ ≤ ‖(x : ℂ) ^ ((δ : ℂ) - 1)‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos hx.1, norm_cpow_eq_rpow_re_of_pos hx.1]
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by simpa using hw)
  refine ⟨{q | β ≤ q.2.1.re ∧ γ ≤ (q.2.2.1 - q.2.1).re ∧ q.1 ∈ closedBall a₀ 1 ∧
      q.2.2.2 ∈ closedBall z₀ (ε / 2)}, ?_,
    fun t ↦ ‖(t : ℂ) ^ ((β : ℂ) - 1) * (1 - (t : ℂ)) ^ ((γ : ℂ) - 1)‖ * C, ?_, ?_⟩
  · have h1 : ∀ᶠ q : ℂ × ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, c₀, z₀), β < q.2.1.re :=
      ((by fun_prop : Continuous fun q : ℂ × ℂ × ℂ × ℂ ↦ q.2.1.re).tendsto _).eventually_const_lt
        (half_lt_self hb)
    have h2 : ∀ᶠ q : ℂ × ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, c₀, z₀), γ < (q.2.2.1 - q.2.1).re :=
      ((by fun_prop : Continuous fun q : ℂ × ℂ × ℂ × ℂ ↦ (q.2.2.1 - q.2.1).re).tendsto
        _).eventually_const_lt (half_lt_self (by simpa using sub_pos.mpr hbc))
    have h3 : ∀ᶠ q : ℂ × ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, c₀, z₀), q.1 ∈ closedBall a₀ 1 :=
      (continuous_fst.tendsto _) (closedBall_mem_nhds a₀ one_pos)
    have h4 : ∀ᶠ q : ℂ × ℂ × ℂ × ℂ in 𝓝 (a₀, b₀, c₀, z₀), q.2.2.2 ∈ closedBall z₀ (ε / 2) :=
      ((by fun_prop : Continuous fun q : ℂ × ℂ × ℂ × ℂ ↦ q.2.2.2).tendsto _)
        (closedBall_mem_nhds z₀ (half_pos hε))
    filter_upwards [h1, h2, h3, h4] with q hq1 hq2 hq3 hq4
    exact ⟨hq1.le, hq2.le, hq3, hq4⟩
  · exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent (by simpa using hβ) (by simpa using hγ))).norm.mul_const C
  · rintro t ht ⟨a, b, c, z⟩ ⟨hqb, hqc, hqa, hqz⟩
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hone : 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    dsimp only at hqb hqc hqa hqz ⊢
    rw [norm_mul, norm_mul, norm_mul, hone]
    gcongr
    · exact hpow ht hqb
    · exact hpow ht' hqc
    · exact hC (t, a, z) ⟨Ioo_subset_Icc_self ht, hqa, hqz⟩

/-- Euler's integral `∫₀¹ t^(b-1) (1-t)^(c-b-1) (1-zt)^(-a) dt` is jointly holomorphic in
`(a, b, c, z)` on the region `0 < re b < re c`, `1 - z ∈ slitPlane`. -/
theorem analyticOnNhd_integral_eulerIntegrand_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ × ℂ × ℂ ↦ ∫ t : ℝ in 0..1, (t : ℂ) ^ (q.2.1 - 1) *
        (1 - (t : ℂ)) ^ (q.2.2.1 - q.2.1 - 1) * (1 - q.2.2.2 * t) ^ (-q.1))
      {q | 0 < q.2.1.re ∧ q.2.1.re < q.2.2.1.re ∧ 1 - q.2.2.2 ∈ slitPlane} := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine TauCeti.analyticOnNhd_integral_of_dominated ?_ ?_ ?_ ?_
  · have hb : Continuous fun q : ℂ × ℂ × ℂ × ℂ ↦ q.2.1.re := by fun_prop
    have hc : Continuous fun q : ℂ × ℂ × ℂ × ℂ ↦ q.2.2.1.re := by fun_prop
    have hz : Continuous fun q : ℂ × ℂ × ℂ × ℂ ↦ 1 - q.2.2.2 := by fun_prop
    exact (isOpen_lt continuous_const hb).inter ((isOpen_lt hb hc).inter
      (isOpen_slitPlane.preimage hz))
  · rintro q ⟨hb, hbc, hz⟩
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (intervalIntegrable_eulerIntegrand q.1 hb hbc hz)).aestronglyMeasurable
  · rintro q ⟨hb, hbc, hz⟩
    obtain ⟨N, hN, bound, hbi, hbound⟩ := exists_bound_eulerIntegrand hb hbc hz
    exact ⟨N, hN, bound, hbi, (ae_restrict_mem measurableSet_Ioo).mono hbound⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rintro q ⟨-, -, hz⟩
    have h0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have h1 : 1 - (t : ℂ) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
      linarith [ht.2]
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((DifferentiableAt.const_cpow (by fun_prop) (Or.inl h0)).mul
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl h1))).mul
      (DifferentiableAt.cpow (by fun_prop) (by fun_prop)
        (one_sub_mul_ofReal_mem_slitPlane hz (Ioo_subset_Icc_self ht)))

/-- Euler's normalized integral `Complex.eulerIntegral` is jointly holomorphic in `(a, b, c, z)`
on the region `0 < re b < re c`, `1 - z ∈ slitPlane`. -/
theorem analyticOnNhd_eulerIntegral_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ × ℂ × ℂ ↦ eulerIntegral q.1 q.2.1 q.2.2.1 q.2.2.2)
      {q | 0 < q.2.1.re ∧ q.2.1.re < q.2.2.1.re ∧ 1 - q.2.2.2 ∈ slitPlane} := by
  have hG : Differentiable ℂ fun q : ℂ × ℂ × ℂ × ℂ ↦ (Gamma q.2.1 * Gamma (q.2.2.1 - q.2.1))⁻¹ := by
    simp only [mul_inv]
    exact (differentiable_one_div_Gamma.comp (by fun_prop)).mul
      (differentiable_one_div_Gamma.comp (by fun_prop))
  simp only [eulerIntegral_def]
  exact ((hG.differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ).mono
    (subset_univ _)).mul analyticOnNhd_integral_eulerIntegrand_joint

end Complex
