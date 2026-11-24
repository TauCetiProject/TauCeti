/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Esseen

/-!
# Characteristic functions and independence

This file contains two groups of results connecting characteristic functions and independence:

1. **Independence from a sub-sigma-algebra via characteristic functions.** Characterizes
   independence of an a.e.-measurable random variable `X` in a complete second-countable real inner
   product space from a sub-sigma-algebra `m` via deterministic conditional characteristic functions
   (`P[exp (⟪X, t⟫ * I) | m]`) and set-integral factorizations
   `∫ ω in A, exp (⟪X ω, t⟫ * I) ∂P = P.real A * φ t` for `A ∈ m`, using
   `MeasureTheory.Measure.ext_of_charFun`.
2. **Small balls of sums of independent random variables.** Combines factorization of the
   characteristic function of an independent sum with Esseen's concentration inequality
   `MeasureTheory.measureReal_closedBall_le_integral_norm_charFun` to bound
   `P.real {ω | |∑ i ∈ s, X i ω - v| ≤ ε}` (and weighted sums `∑ i ∈ s, a i * ξ i`).

## References

* C.-G. Esseen, *On the Kolmogorov–Rogozin inequality for the concentration function*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete 5 (1966), 210–216.
* O. Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021,
  Chapter 6 (conditional characteristic functions).
* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §4.
-/

public section

namespace ProbabilityTheory

section Conditional

open MeasureTheory Complex
open scoped RealInnerProductSpace

variable {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] {m mΩ : MeasurableSpace Ω}
  {P : Measure Ω}

/-- A random variable in a complete second-countable real inner product space has law `μ`
whenever its characteristic integral matches `charFun μ` everywhere. -/
theorem hasLaw_of_forall_integral_exp_inner_mul_I [IsFiniteMeasure P] {μ : Measure E}
    [IsFiniteMeasure μ] {X : Ω → E} (hX : AEMeasurable X P)
    (h : ∀ t : E, ∫ ω, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = charFun μ t) : HasLaw X μ P where
  aemeasurable := hX
  map_eq := by
    have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
    exact Measure.ext_of_charFun (funext fun t ↦ by rw [charFun_map_eq_integral hX t, h t])

/-- A random variable in a complete second-countable real inner product space is independent
of a sub-sigma-algebra `m` if and only if its characteristic integral over every event `A ∈ m`
factors as `(P A).toReal * charFun (P.map X) t`. -/
theorem indep_comap_iff_forall_setIntegral_exp_inner_mul_I [IsZeroOrProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → E} (hX : AEMeasurable X P) :
    Indep (.comap X inferInstance) m P ↔ ∀ t : E, ∀ A, MeasurableSet[m] A →
      ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = ((P A).toReal : ℂ) * charFun (P.map X) t := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP; · simp [Indep_iff]
  have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
  refine ⟨fun hind t A hA ↦ ?_, fun h ↦ (Indep_iff _ _ _).2 ?_⟩
  · have hmap : (P.restrict A).map X = P A • P.map X := by
      ext S hS; rw [Measure.map_apply_of_aemeasurable hX.restrict hS,
        Measure.restrict_apply' (hm A hA), smul_apply, smul_eq_mul,
        Measure.map_apply_of_aemeasurable hX hS, mul_comm]
      exact (Indep_iff _ _ _).1 hind _ _ ⟨S, hS, rfl⟩ hA
    rw [← charFun_map_eq_integral hX.restrict t, hmap, charFun_smul_measure]
  · rintro _ A ⟨S, hS, rfl⟩ hA
    have : IsFiniteMeasure ((P.restrict A).map X) := Measure.isFiniteMeasure_map _ X
    have : IsFiniteMeasure (P A • P.map X) := ⟨by simp⟩
    have hmap := Measure.ext_of_charFun (μ := (P.restrict A).map X) (ν := P A • P.map X)
      (funext fun t ↦ by rw [charFun_map_eq_integral hX.restrict t, h t A hA, charFun_smul_measure])
    simpa only [Measure.map_apply_of_aemeasurable hX.restrict hS, Measure.restrict_apply' (hm A hA),
      smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable hX hS, mul_comm] using
      congrArg (fun ν : Measure E ↦ ν S) hmap

/-- If the characteristic integral of `X` over every event `A ∈ m` factors as
`(P A).toReal * φ t` for some deterministic function `φ`, then `X` is independent of `m`.
When `P` is a probability measure (`P ≠ 0`), evaluating at `A = univ` identifies `φ` with
`charFun (P.map X)`. -/
theorem indep_comap_of_setIntegral_exp_inner_mul_I [IsZeroOrProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} (hX : AEMeasurable X P) {φ : E → ℂ} (h : ∀ t : E, ∀ A, MeasurableSet[m] A →
      ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = ((P A).toReal : ℂ) * φ t) :
    Indep (.comap X inferInstance) m P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP; · simp [Indep_iff]
  have hφ (t : E) : charFun (P.map X) t = φ t := by
    simpa [charFun_map_eq_integral hX t] using h t Set.univ MeasurableSet.univ
  exact (indep_comap_iff_forall_setIntegral_exp_inner_mul_I hm hX).2 fun t A hA ↦ by
    rw [hφ t]
    exact h t A hA

/-- A random variable in a complete second-countable real inner product space is independent
of a sub-sigma-algebra `m` if and only if its conditional characteristic function given `m`
almost surely equals its unconditional characteristic function. -/
theorem indep_comap_iff_forall_condExp_exp_inner_mul_I [IsZeroOrProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} (hX : AEMeasurable X P) : Indep (.comap X inferInstance) m P ↔
      ∀ t : E, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] =ᵐ[P] fun _ ↦ charFun (P.map X) t := by
  rw [indep_comap_iff_forall_setIntegral_exp_inner_mul_I hm hX]
  refine forall_congr' fun t ↦ ?_
  rw [TauCeti.MeasureTheory.condExp_ae_eq_const_iff hm (hX.integrable_exp_inner_mul_I t)]
  simp only [Measure.real, Complex.real_smul, measure_lt_top, true_implies]

/-- If the conditional characteristic function of `X` given `m` is almost surely equal to a
deterministic function `φ`, then `X` is independent of `m`. -/
theorem indep_comap_of_condExp_exp_inner_mul_I [IsZeroOrProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} (hX : AEMeasurable X P) {φ : E → ℂ}
    (h : ∀ t : E, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] =ᵐ[P] fun _ ↦ φ t) :
    Indep (.comap X inferInstance) m P :=
  indep_comap_of_setIntegral_exp_inner_mul_I hm hX fun t A hA ↦ by
    simpa only [Measure.real, Complex.real_smul] using
      (TauCeti.MeasureTheory.condExp_ae_eq_const_iff hm
        (hX.integrable_exp_inner_mul_I t) (φ t)).1 (h t) A hA (measure_lt_top _ _)

end Conditional

section Esseen

open MeasureTheory Metric

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Esseen's inequality for independent sums.** For a finite set `s` of indices and independent
real random variables `X i`, `i ∈ s`, the probability that `∑ i ∈ s, X i` lies within `ε > 0` of
`v` is at most `2 * ε` times the integral over `[-ε⁻¹, ε⁻¹]` of the product of the moduli of the
characteristic functions of the `X i`. -/
theorem iIndepFun.measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun
    {X : ι → Ω → ℝ} {s : Finset ι} (hX : iIndepFun (s.restrict X) P)
    (hmeas : ∀ i ∈ s, AEMeasurable (X i) P) (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i ∈ s, X i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i ∈ s, ‖charFun (P.map (X i)) t‖ := by
  have := hX.isProbabilityMeasure
  have hS : AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) P := Finset.aemeasurable_fun_sum _ hmeas
  have hset : {ω | |∑ i ∈ s, X i ω - v| ≤ ε} = (fun ω ↦ ∑ i ∈ s, X i ω) ⁻¹' closedBall v ε := by
    ext ω
    simp [Real.dist_eq]
  rw [hset, ← map_measureReal_apply_of_aemeasurable hS measurableSet_closedBall]
  refine (measureReal_closedBall_le_integral_norm_charFun v hε).trans_eq ?_
  simp [hX.charFun_map_fun_finsetSum_eq_prod hmeas, Finset.prod_apply, norm_prod]

/-- **Esseen's inequality for independent sums** over a finite index type: the probability that
`∑ i, X i` lies within `ε > 0` of `v` is at most `2 * ε` times the integral over `[-ε⁻¹, ε⁻¹]` of
the product of the moduli of the characteristic functions of the `X i`. -/
theorem iIndepFun.measureReal_abs_sum_sub_le_le_integral_prod_norm_charFun [Fintype ι]
    {X : ι → Ω → ℝ} (hX : iIndepFun X P) (hmeas : ∀ i, AEMeasurable (X i) P) (v : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    P.real {ω | |∑ i, X i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i, ‖charFun (P.map (X i)) t‖ :=
  (hX.restrict _).measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun
    (fun i _ ↦ hmeas i) v hε

/-- **Esseen's inequality for independent weighted sums.** For a finite set `s` of indices,
independent real random variables `ξ i`, `i ∈ s`, and real weights `a i`, the probability that
`∑ i ∈ s, a i * ξ i` lies within `ε > 0` of `v` is at most `2 * ε` times the integral over
`[-ε⁻¹, ε⁻¹]` of `∏ i ∈ s, ‖φ i (a i * t)‖`, where `φ i` is the characteristic function of
`ξ i`. -/
theorem iIndepFun.measureReal_abs_finsetSum_mul_sub_le_le_integral_prod_norm_charFun
    {ξ : ι → Ω → ℝ} {s : Finset ι} (hξ : iIndepFun (s.restrict ξ) P)
    (hmeas : ∀ i ∈ s, AEMeasurable (ξ i) P) (a : ι → ℝ) (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i ∈ s, a i * ξ i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i ∈ s, ‖charFun (P.map (ξ i)) (a i * t)‖ := by
  have hX : iIndepFun (s.restrict fun i ω ↦ a i * ξ i ω) P := by
    simpa [Finset.restrict_def, Function.comp_def] using
      hξ.comp (fun i x ↦ a i * x) fun i ↦ measurable_const_mul (a i)
  refine (hX.measureReal_abs_finsetSum_sub_le_le_integral_prod_norm_charFun
    (fun i hi ↦ (hmeas i hi).const_mul (a i)) v hε).trans_eq ?_
  refine congrArg (2 * ε * ·) (intervalIntegral.integral_congr fun t _ ↦
    Finset.prod_congr rfl fun i hi ↦ ?_)
  rw [charFun_map_mul_comp (hmeas i hi)]

/-- **Esseen's inequality for independent weighted sums** over a finite index type: the
probability that `∑ i, a i * ξ i` lies within `ε > 0` of `v` is at most `2 * ε` times the
integral over `[-ε⁻¹, ε⁻¹]` of `∏ i, ‖φ i (a i * t)‖`, where `φ i` is the characteristic function
of `ξ i`. -/
theorem iIndepFun.measureReal_abs_sum_mul_sub_le_le_integral_prod_norm_charFun [Fintype ι]
    {ξ : ι → Ω → ℝ} (hξ : iIndepFun ξ P) (hmeas : ∀ i, AEMeasurable (ξ i) P) (a : ι → ℝ)
    (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i, a i * ξ i ω - v| ≤ ε} ≤
      2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ i, ‖charFun (P.map (ξ i)) (a i * t)‖ :=
  (hξ.restrict _).measureReal_abs_finsetSum_mul_sub_le_le_integral_prod_norm_charFun
    (fun i _ ↦ hmeas i) a v hε

end Esseen

end ProbabilityTheory
