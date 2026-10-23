/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Multiplication.MeasureLp.Basic
public import TauCeti.Analysis.Semigroups.Resolvent.Identity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Analysis.Calculus.ExponentialSlope

/-!
# Generators of measure-space Lᵖ multiplication semigroups

For an almost everywhere measurable nonnegative multiplier `m`, the generator of
`S(t)f = exp (-t * m) • f` on `Lᵖ(μ; E)`, `1 ≤ p < ∞`, is multiplication by `-m`.
Its domain consists exactly of the vectors for which `m • f` belongs to Lᵖ. The measure
is arbitrary and the multiplier need not be bounded. Generator values and resolvent values
are specified almost everywhere, so they do not depend on choices of representatives.

The exact domain allows the abstract Cauchy problem to be applied to these unbounded
multiplication operators. The resolvent is multiplication by `(λ + m)⁻¹` for `λ > 0`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section I.4.c (multiplication semigroups).

The convergence arguments use Mathlib's almost everywhere subsequence theorem for
convergence in measure and Tau Ceti's dominated convergence theorem in Lᵖ.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Semigroups

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : α → ℝ≥0}

private theorem multiplication_quotient_ae (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (f : Lp E p μ) {t : ℝ} (ht : 0 ≤ t) :
    (1 / t) • (StronglyContinuousSemigroup.realOperator
      (ContractionSemigroup.ofMeasureLpMultiplication hm hp).toStronglyContinuousSemigroup
        t f - f) =ᵐ[μ]
      fun a => ((Real.exp (-((m a : ℝ) * t)) - 1) / t) • f a := by
  rw [StronglyContinuousSemigroup.realOperator_def,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply]
  filter_upwards [Lp.coeFn_smul (1 / t)
    (ContractionSemigroup.ofMeasureLpMultiplication hm hp t.toNNReal f - f),
    Lp.coeFn_sub (ContractionSemigroup.ofMeasureLpMultiplication hm hp t.toNNReal f) f,
    ContractionSemigroup.ofMeasureLpMultiplication_apply_apply_ae hm hp t.toNNReal f]
    with a hsmul hsub hS
  simp only [Pi.smul_apply, Pi.sub_apply, hsmul, hsub, hS, Real.coe_toNNReal t ht]
  rw [mul_comm t]
  have hs : Real.exp (-((m a : ℝ) * t)) • f a - f a =
      (Real.exp (-((m a : ℝ) * t)) - 1) • f a := by
    rw [sub_smul, one_smul]
  rw [hs, smul_smul]
  congr 1
  ring

/-- The generator of a measure-space Lᵖ multiplication semigroup acts as multiplication by
`-m` almost everywhere. No boundedness of the multiplier or finiteness of the measure is needed. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_generator_apply_ae
    (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (f : (ofMeasureLpMultiplication (E := E) hm
      hp).toStronglyContinuousSemigroup.generator.domain) :
    (ofMeasureLpMultiplication hm hp).toStronglyContinuousSemigroup.generator f =ᵐ[μ]
      fun a => -((m a : ℝ) • (f : Lp E p μ) a) := by
  let S := (ofMeasureLpMultiplication (E := E) hm hp).toStronglyContinuousSemigroup
  have hf : (f : Lp E p μ) ∈ S.domain := by
    rw [← S.generator_domain]
    exact f.property
  have hlim := S.generator_tendsto ⟨f, hf⟩
  obtain ⟨ts, hts, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae'
  have hpos : ∀ᶠ n in atTop, 0 < ts n := hts.eventually self_mem_nhdsWithin
  have hquot : ∀ᵐ a ∂μ, ∀ n : ℕ, 0 < ts n →
      ((1 / ts n) • (S.realOperator (ts n) f - (f : Lp E p μ))) a =
        ((Real.exp (-((m a : ℝ) * ts n)) - 1) / ts n) • (f : Lp E p μ) a := by
    refine ae_all_iff.2 fun n => ?_
    by_cases hn : 0 < ts n
    · have hq := multiplication_quotient_ae hm hp (f : Lp E p μ) hn.le
      exact hq.mono fun a ha _ => ha
    · exact .of_forall fun _ h => (hn h).elim
  filter_upwards [hae, hquot] with a ha hqa
  have hpoint := ((TauCeti.tendsto_exp_mul_sub_one_div (-(m a : ℝ))).smul
    (tendsto_const_nhds (x := (f : Lp E p μ) a))).comp hts
  have heq : (fun n => ((1 / ts n) •
      (S.realOperator (ts n) f - (f : Lp E p μ))) a) =ᶠ[atTop]
      fun n => ((Real.exp (-(m a : ℝ) * ts n) - 1) / ts n) • (f : Lp E p μ) a := by
    filter_upwards [hpos] with n hn
    simpa only [neg_mul] using hqa n hn
  simpa only [neg_smul] using tendsto_nhds_unique ha (hpoint.congr' heq.symm)

private theorem tendsto_multiplication_quotient (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (f : Lp E p μ) (hf : MemLp (fun a => (m a : ℝ) • f a) p μ) :
    Tendsto (fun t : ℝ => (1 / t) •
      (StronglyContinuousSemigroup.realOperator
        (ContractionSemigroup.ofMeasureLpMultiplication hm hp).toStronglyContinuousSemigroup
        t f - f))
      (𝓝[>] 0) (𝓝 (-hf.toLp (fun a => (m a : ℝ) • f a))) := by
  let g : Lp E p μ := -hf.toLp (fun a => (m a : ℝ) • f a)
  have hg : g =ᵐ[μ] fun a => -(m a : ℝ) • f a := by
    filter_upwards [Lp.coeFn_neg (hf.toLp _), hf.coeFn_toLp] with a hn hf
    simpa only [g, Pi.neg_apply, hf, neg_smul] using hn
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ g).2
  have hlim : Tendsto (fun t : ℝ => eLpNorm
      ((fun a => ((Real.exp (-((m a : ℝ) * t)) - 1) / t) • f a) -
        (fun a => -(m a : ℝ) • f a)) p μ) (𝓝[>] 0) (𝓝 0) := by
    apply TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
      (.of_forall fun t => by fun_prop) (by fun_prop) hf (C := 1)
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      filter_upwards with a
      have he : Real.exp (-((m a : ℝ) * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      have hlow := Real.one_sub_le_exp_neg ((m a : ℝ) * t)
      have hdlo : -(m a : ℝ) ≤ (Real.exp (-((m a : ℝ) * t)) - 1) / t :=
        (le_div_iff₀ ht).2 (by linarith)
      have hdhi : (Real.exp (-((m a : ℝ) * t)) - 1) / t ≤ 0 :=
        (div_le_iff₀ ht).2 (by linarith)
      have hb : |(Real.exp (-((m a : ℝ) * t)) - 1) / t + (m a : ℝ)| ≤ (m a : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [(m a).coe_nonneg]
      rw [← sub_smul, sub_neg_eq_add]
      have hn : ‖((Real.exp (-((m a : ℝ) * t)) - 1) / t + (m a : ℝ)) • f a‖ ≤
          ‖(m a : ℝ) • f a‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (m a).coe_nonneg]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      simpa only [ofReal_norm, ENNReal.coe_one, one_mul] using
        (ENNReal.ofReal_le_ofReal hn)
    · exact .of_forall fun a => by
        simpa only [neg_mul] using
          (TauCeti.tendsto_exp_mul_sub_one_div (-(m a : ℝ))).smul
            (tendsto_const_nhds (x := f a))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (eLpNorm_congr_ae ((multiplication_quotient_ae hm hp f ht.le).sub hg)).symm

/-- The domain of the multiplication generator is exactly the weighted Lᵖ domain:
`f ∈ D(A)` if and only if `m • f` belongs to Lᵖ. This applies to arbitrary measures and
unbounded almost everywhere measurable multipliers. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_mem_domain_iff
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ) :
    f ∈ (ofMeasureLpMultiplication hm hp).toStronglyContinuousSemigroup.domain ↔
      MemLp (fun a => (m a : ℝ) • f a) p μ := by
  constructor
  · intro hf
    let f' : (ofMeasureLpMultiplication hm hp).toStronglyContinuousSemigroup.generator.domain :=
      ⟨f, by rwa [StronglyContinuousSemigroup.generator_domain]⟩
    have ha := ofMeasureLpMultiplication_generator_apply_ae hm hp f'
    exact ((Lp.memLp _).ae_eq ha).neg.ae_eq (.of_forall fun a => by simp [f'])
  · intro hf
    exact (StronglyContinuousSemigroup.mem_domain_iff_tendsto _ _).2
      ⟨_, tendsto_multiplication_quotient hm hp f hf⟩

variable [CompleteSpace E]

/-- The Laplace resolvent of a measure-space Lᵖ multiplication semigroup is multiplication by
`(λ + m)⁻¹` almost everywhere, for every positive real parameter `λ`. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_resolvent_apply_ae
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) {c : ℝ} (hc : 0 < c) (f : Lp E p μ) :
    (ofMeasureLpMultiplication hm hp).resolvent c hc f =ᵐ[μ]
      fun a => (c + (m a : ℝ))⁻¹ • f a := by
  let S := ofMeasureLpMultiplication (E := E) hm hp
  let r : Lp E p μ := S.resolvent c hc f
  let r' : S.toStronglyContinuousSemigroup.generator.domain :=
    ⟨r, by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact S.resolvent_mem_domain c hc f⟩
  have hgen := ofMeasureLpMultiplication_generator_apply_ae hm hp r'
  have hinv := S.resolventRightInv c hc f
  have hae : c • r - S.toStronglyContinuousSemigroup.generator r' =ᵐ[μ] f := by
    rw [hinv]
  filter_upwards [hae, Lp.coeFn_sub (c • r) (S.toStronglyContinuousSemigroup.generator r'),
    Lp.coeFn_smul c r, hgen] with a ha hsub hsmul hg
  have hg' : (S.toStronglyContinuousSemigroup.generator r') a = -((m a : ℝ) • r a) := hg
  have hmul : (c + (m a : ℝ)) • r a = f a := by
    simpa only [Pi.sub_apply, Pi.smul_apply, hsub, hsmul, hg',
      sub_neg_eq_add, neg_smul, add_smul] using ha
  have hne : c + (m a : ℝ) ≠ 0 := ne_of_gt (by positivity)
  calc
    r a = (c + (m a : ℝ))⁻¹ • ((c + (m a : ℝ)) • r a) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (c + (m a : ℝ))⁻¹ • f a := by rw [hmul]

end TauCeti.Semigroups
