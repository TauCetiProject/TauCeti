/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.Analysis.Calculus.ExponentialSlope
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Multiplication semigroups on measure-space Lᵖ

For an almost-everywhere measurable nonnegative multiplier `m`, multiplication by
`exp (-t * m)` defines a contraction semigroup on real `Lᵖ(μ)`, for `1 ≤ p < ∞`.
The measure is arbitrary and the multiplier may be unbounded. Its generator acts as
multiplication by `-m` on exactly the functions whose product with `m` lies in `Lᵖ(μ)`.
All formulas for representatives hold almost everywhere.

Strong continuity can fail on L∞ for unbounded multipliers, so the finite-exponent
assumption is required for this general theorem. The proof uses Mathlib's Hölder bilinear
map to construct the operators and dominated convergence for strong continuity and for
the generator difference quotients.

## References

K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Section I.4.c (multiplication semigroups).
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Semigroups

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [MeasurableSpace α] in
private theorem expMeasureMultiplier_bound (m : α → ℝ≥0) (t : ℝ≥0) (a : α) :
    ‖Real.exp (-((t : ℝ) * m a))‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg t.coe_nonneg (m a).coe_nonneg))

private def expMeasureMultiplier (m : α → ℝ≥0) (hm : AEMeasurable m μ) (t : ℝ≥0) :
    Lp ℝ ∞ μ :=
  (memLp_top_of_bound (hm.coe_nnreal_real.const_mul t |>.neg.exp.aestronglyMeasurable)
    1 (.of_forall (expMeasureMultiplier_bound m t))).toLp _

private def measureMultiplicationOperator (m : α → ℝ≥0) (hm : AEMeasurable m μ)
    (t : ℝ≥0) : Lp ℝ p μ →L[ℝ] Lp ℝ p μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ p p (expMeasureMultiplier m hm t)

private theorem measureMultiplicationOperator_coeFn (m : α → ℝ≥0) (hm : AEMeasurable m μ)
    (t : ℝ≥0) (f : Lp ℝ p μ) :
    measureMultiplicationOperator m hm t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) * f a := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p) (expMeasureMultiplier m hm t) f
  have he : expMeasureMultiplier m hm t =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) := MemLp.coeFn_toLp _
  -- Hölder's bundled map has the same underlying map as `holder`.
  exact h.trans (he.mono fun a ha => by simp [ha])

private theorem measureMultiplicationOperator_norm_le (m : α → ℝ≥0)
    (hm : AEMeasurable m μ) (t : ℝ≥0) : ‖measureMultiplicationOperator (p := p) m hm t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [measureMultiplicationOperator_coeFn m hm t f] with a ha
  rw [ha, norm_mul]
  simpa using mul_le_mul_of_nonneg_right (expMeasureMultiplier_bound m t a) (norm_nonneg (f a))

private theorem measureMultiplicationOperator_continuousAt_zero (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ) (f : Lp ℝ p μ) :
    ContinuousAt (fun t : ℝ≥0 => measureMultiplicationOperator m hm t f) 0 := by
  have hzero : measureMultiplicationOperator m hm 0 f = f := by
    apply Lp.ext
    simpa using measureMultiplicationOperator_coeFn m hm 0 f
  rw [ContinuousAt, hzero, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have heq : (fun t : ℝ≥0 => eLpNorm (⇑(measureMultiplicationOperator m hm t f) - ⇑f) p μ) =
      fun t : ℝ≥0 => eLpNorm ((fun a => Real.exp (-((t : ℝ) * m a)) * f a) - ⇑f) p μ := by
    funext t
    exact eLpNorm_congr_ae ((measureMultiplicationOperator_coeFn m hm t f).sub .rfl)
  rw [heq]
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := (2 : ℝ).toNNReal)
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    (.of_forall fun t : ℝ≥0 =>
      (hm.coe_nnreal_real.const_mul (t : ℝ) |>.neg.exp.aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable f)) (Lp.aestronglyMeasurable f) (Lp.memLp f)
  · exact .of_forall fun t => .of_forall fun a => by
      have hbound : ‖Real.exp (-((t : ℝ) * m a)) * f a - f a‖ ≤ 2 * ‖f a‖ := by
        calc ‖Real.exp (-((t : ℝ) * m a)) * f a - f a‖
            ≤ ‖Real.exp (-((t : ℝ) * m a)) * f a‖ + ‖f a‖ := norm_sub_le _ _
          _ ≤ 2 * ‖f a‖ := by
            rw [norm_mul]
            have := expMeasureMultiplier_bound m t a
            nlinarith [norm_nonneg (f a)]
      simpa only [Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, ofReal_norm,
        ENNReal.ofNNReal_toNNReal,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using ENNReal.ofReal_le_ofReal hbound
  · exact .of_forall fun a => by
      have hc : ContinuousAt (fun t : ℝ≥0 => Real.exp (-((t : ℝ) * m a)) * f a) 0 := by
        fun_prop
      simpa using hc.tendsto

/-- Multiplication by `exp (-t * m)` on real measure-space Lᵖ is a contraction semigroup,
for `1 ≤ p < ∞`. No boundedness of the nonnegative multiplier or finiteness of the measure
is required. -/
def ContractionSemigroup.ofMeasureLpMultiplication (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ) : ContractionSemigroup (Lp ℝ p μ) where
  toFun := measureMultiplicationOperator m hm
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    simpa using measureMultiplicationOperator_coeFn m hm 0 f
  map_add' s t := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [measureMultiplicationOperator_coeFn m hm (s + t) f,
      measureMultiplicationOperator_coeFn m hm s (measureMultiplicationOperator m hm t f),
      measureMultiplicationOperator_coeFn m hm t f] with a hst hs ht
    simp only [ContinuousLinearMap.comp_apply, hst, hs, ht, NNReal.coe_add]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  continuousAt_zero' := measureMultiplicationOperator_continuousAt_zero hp m hm
  contracting := measureMultiplicationOperator_norm_le m hm

/-- Almost-everywhere action of the measure-space multiplication semigroup. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_coeFn (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ) (t : ℝ≥0) (f : Lp ℝ p μ) :
    ofMeasureLpMultiplication hp m hm t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) * f a :=
  measureMultiplicationOperator_coeFn m hm t f

private theorem measureMultiplication_quotient_coeFn (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ) (f : Lp ℝ p μ) {t : ℝ} (ht : 0 < t) :
    (1 / t) • (StronglyContinuousSemigroup.realOperator
      (ContractionSemigroup.ofMeasureLpMultiplication hp m hm).toStronglyContinuousSemigroup
      t f - f) =ᵐ[μ]
        fun a => ((Real.exp (-(t * m a)) - 1) / t) * f a := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication hp m hm
  have horbit : S.toStronglyContinuousSemigroup.realOperator t f =ᵐ[μ]
      fun a => Real.exp (-(t * m a)) * f a := by
    rw [StronglyContinuousSemigroup.realOperator_def,
      ContractionSemigroup.toStronglyContinuousSemigroup_apply]
    simpa only [Real.coe_toNNReal t ht.le] using
      ContractionSemigroup.ofMeasureLpMultiplication_coeFn hp m hm t.toNNReal f
  filter_upwards [Lp.coeFn_smul (1 / t) (S.toStronglyContinuousSemigroup.realOperator t f - f),
    Lp.coeFn_sub (S.toStronglyContinuousSemigroup.realOperator t f) f, horbit] with a hs hd ho
  dsimp only [S] at hs hd ho
  simp only [hs, hd, ho, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The generator of the measure-space multiplication semigroup is multiplication by `-m`,
almost everywhere on its domain. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_generator_coeFn (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ)
    (f : (ofMeasureLpMultiplication hp m hm).toStronglyContinuousSemigroup.generator.domain) :
    (ofMeasureLpMultiplication hp m hm).toStronglyContinuousSemigroup.generator f =ᵐ[μ]
      fun a => -(m a : ℝ) * (f : Lp ℝ p μ) a := by
  let S := (ofMeasureLpMultiplication hp m hm).toStronglyContinuousSemigroup
  have hf : (f : Lp ℝ p μ) ∈ S.domain := by
    simpa only [StronglyContinuousSemigroup.generator_domain] using f.property
  have hlim := S.generator_tendsto ⟨f, hf⟩
  -- Strong convergence gives a pointwise convergent subsequence of difference quotients.
  obtain ⟨ts, hts, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae'
  have hformula : ∀ᵐ a ∂μ, ∀ n, 0 < ts n →
      ((1 / ts n) • (S.realOperator (ts n) (f : Lp ℝ p μ) - (f : Lp ℝ p μ))) a =
        ((Real.exp (-(ts n * m a)) - 1) / ts n) * (f : Lp ℝ p μ) a := by
    apply ae_all_iff.mpr
    intro n
    by_cases ht : 0 < ts n
    · exact (measureMultiplication_quotient_coeFn hp m hm f ht).mono fun _ h _ => h
    · exact .of_forall fun _ h => (ht h).elim
  filter_upwards [hae, hformula] with a ha hform
  have hscalar : Tendsto (fun t : ℝ => ((Real.exp (-(t * m a)) - 1) / t) *
      (f : Lp ℝ p μ) a) (𝓝[>] 0) (𝓝 (-(m a : ℝ) * (f : Lp ℝ p μ) a)) := by
    simpa only [neg_mul, mul_neg, mul_comm] using
      (tendsto_exp_mul_sub_one_div (-(m a : ℝ))).mul_const ((f : Lp ℝ p μ) a)
  -- The same subsequence has the explicit scalar derivative as its pointwise limit.
  have heq : (fun n => ((1 / ts n) •
      (S.realOperator (ts n) (f : Lp ℝ p μ) - (f : Lp ℝ p μ))) a) =ᶠ[atTop]
      fun n => ((Real.exp (-(ts n * m a)) - 1) / ts n) * (f : Lp ℝ p μ) a :=
    (hts.eventually self_mem_nhdsWithin).mono fun n hn => hform n hn
  exact tendsto_nhds_unique ha (hscalar.comp hts |>.congr' heq.symm)

/-- The exact generator domain consists of those Lᵖ functions whose product with `m`
is again in Lᵖ. The multiplier may be unbounded. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_mem_domain_iff (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ) (f : Lp ℝ p μ) :
    f ∈ (ofMeasureLpMultiplication hp m hm).toStronglyContinuousSemigroup.domain ↔
      MemLp (fun a => (m a : ℝ) * f a) p μ := by
  let S := (ofMeasureLpMultiplication hp m hm).toStronglyContinuousSemigroup
  constructor
  · intro hf
    let f' : S.generator.domain := ⟨f, by rwa [StronglyContinuousSemigroup.generator_domain]⟩
    have heq : -(S.generator f') =ᵐ[μ] fun a => (m a : ℝ) * f a := by
      filter_upwards [Lp.coeFn_neg (S.generator f'),
        ofMeasureLpMultiplication_generator_coeFn hp m hm f'] with a hn hg
      rw [hn, Pi.neg_apply]
      simp only [S, hg, f', neg_mul, neg_neg]
    exact (Lp.memLp _).ae_eq heq
  · intro hf
    let g := hf.neg.toLp (fun a => -((m a : ℝ) * f a))
    rw [S.mem_domain_iff_tendsto]
    refine ⟨g, ?_⟩
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    have hnorm : (fun t : ℝ => eLpNorm
        (⇑((1 / t) • (S.realOperator t f - f)) - (fun a => -((m a : ℝ) * f a))) p μ) =ᶠ[𝓝[>] 0]
        fun t => eLpNorm ((fun a => ((Real.exp (-(t * m a)) - 1) / t) * f a) -
          (fun a => -((m a : ℝ) * f a))) p μ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact eLpNorm_congr_ae ((measureMultiplication_quotient_coeFn hp m hm f ht).sub .rfl)
    apply Tendsto.congr' hnorm.symm
    apply tendsto_eLpNorm_sub_of_ae_tendsto (C := (2 : ℝ).toNNReal)
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
      (.of_forall fun t : ℝ =>
        (((hm.coe_nnreal_real.const_mul t).neg.exp.sub_const 1).div_const t)
          |>.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) hf.neg.aestronglyMeasurable
      hf
    · -- The scalar difference quotient is bounded by `m`; its error by twice `m * f`.
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact .of_forall fun a => by
        have hexp : Real.exp (-(t * m a)) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (mul_nonneg ht.le (m a).coe_nonneg))
        have hlin := Real.add_one_le_exp (-(t * m a))
        have hquot : ‖(Real.exp (-(t * m a)) - 1) / t‖ ≤ (m a : ℝ) := by
          rw [Real.norm_eq_abs, abs_div, abs_of_nonpos (sub_nonpos.mpr hexp),
            abs_of_pos ht, div_le_iff₀ ht]
          linarith
        have hbound : ‖((Real.exp (-(t * m a)) - 1) / t) * f a - -((m a : ℝ) * f a)‖
            ≤ 2 * ‖(m a : ℝ) * f a‖ := by
          calc ‖((Real.exp (-(t * m a)) - 1) / t) * f a - -((m a : ℝ) * f a)‖
              ≤ ‖((Real.exp (-(t * m a)) - 1) / t) * f a‖ + ‖-((m a : ℝ) * f a)‖ :=
                norm_sub_le _ _
            _ ≤ 2 * ‖(m a : ℝ) * f a‖ := by
              simp only [norm_neg, norm_mul, Real.norm_eq_abs,
                abs_of_nonneg (m a).coe_nonneg]
              rw [Real.norm_eq_abs] at hquot
              nlinarith [abs_nonneg (f a)]
        simpa only [Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, ofReal_norm,
          ENNReal.ofNNReal_toNNReal,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using ENNReal.ofReal_le_ofReal hbound
    · exact .of_forall fun a => by
        simpa only [Pi.mul_apply, Pi.neg_apply, neg_mul, mul_neg, mul_comm] using
          (tendsto_exp_mul_sub_one_div (-(m a : ℝ))).mul_const (f a)

/-- For a positive spectral parameter, the Laplace resolvent of the multiplication
semigroup is multiplication by `(λ + m)⁻¹`, almost everywhere. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_resolvent_coeFn (hp : p ≠ ∞)
    (m : α → ℝ≥0) (hm : AEMeasurable m μ) {c : ℝ} (hc : 0 < c) (f : Lp ℝ p μ) :
    (ofMeasureLpMultiplication hp m hm).resolvent c hc f =ᵐ[μ]
      fun a => (c + (m a : ℝ))⁻¹ * f a := by
  let S := ofMeasureLpMultiplication hp m hm
  let g : S.toStronglyContinuousSemigroup.generator.domain :=
    ⟨S.resolvent c hc f, by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact S.resolvent_mem_domain c hc f⟩
  have hgen := ofMeasureLpMultiplication_generator_coeFn hp m hm g
  have hinv : c • S.resolvent c hc f - S.toStronglyContinuousSemigroup.generator g = f :=
    S.resolventRightInv c hc f
  have heq : (c • S.resolvent c hc f - S.toStronglyContinuousSemigroup.generator g : Lp ℝ p μ)
      =ᵐ[μ] f := by rw [hinv]
  filter_upwards [hgen, heq, Lp.coeFn_sub (c • S.resolvent c hc f)
      (S.toStronglyContinuousSemigroup.generator g), Lp.coeFn_smul c (S.resolvent c hc f)]
    with a hg he hd hs
  simp only [hd, hs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [hg] at he
  have hne : c + (m a : ℝ) ≠ 0 := by positivity
  have hmul : (c + (m a : ℝ)) * (S.resolvent c hc f) a = f a := by
    -- The subtype `g` denotes precisely the resolvent vector in the generator domain.
    simpa only [g, Submodule.coe_mk, neg_mul, sub_neg_eq_add, ← add_mul] using he
  rw [← hmul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end TauCeti.Semigroups
