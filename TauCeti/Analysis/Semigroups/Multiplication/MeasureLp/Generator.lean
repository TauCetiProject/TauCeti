/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
public import TauCeti.Analysis.Semigroups.Multiplication.MeasureLp.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Generator of a multiplication semigroup on Lᵖ

For an almost everywhere measurable nonnegative multiplier `m`, the generator of the contraction
semigroup `S(t)f = exp (-t * m) • f` on `Lᵖ(μ; E)` is the generally unbounded multiplication
operator `f ↦ -m • f`. Its exact domain consists of those `f` for which `m • f` belongs to
`Lᵖ`.

The sufficiency of the weighted-`Lᵖ` condition follows by dominated convergence applied to the
exponential difference quotients. For necessity, convergence of the generator quotient in `Lᵖ`
gives an almost everywhere convergent subsequence; the pointwise derivative of the exponential
then identifies its limit with `-m • f`.

## Main declarations

* `TauCeti.Semigroups.ContractionSemigroup.ofMeasureLpMultiplication_mem_domain_iff` identifies
  the generator domain with the weighted-`Lᵖ` condition.
* `TauCeti.Semigroups.ContractionSemigroup.ofMeasureLpMultiplication_generator_apply_ae` computes
  the generator almost everywhere on that domain.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section I.4.c.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Semigroups

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private abbrev measureLpGeneratorQuotient (m : α → ℝ≥0) (f : Lp E p μ) (t : ℝ) :
    α → E :=
  fun a => (1 / t) • (Real.exp (-(t * m a)) • f a - f a)

private abbrev measureLpGeneratorValue (m : α → ℝ≥0) (f : Lp E p μ) : α → E :=
  fun a => (-(m a : ℝ)) • f a

private theorem tendsto_measureLpGeneratorScalar (c : ℝ≥0) :
    Tendsto (fun t : ℝ => (1 / t) * (Real.exp (-(t * c)) - 1))
      (nhdsWithin 0 (Ioi 0)) (nhds (-(c : ℝ))) := by
  have hderiv : HasDerivAt (fun t : ℝ => Real.exp (-(t * c))) (-(c : ℝ)) 0 := by
    simpa using (((hasDerivAt_id 0).mul_const (c : ℝ)).neg.exp)
  convert hderiv.tendsto_slope_zero_right using 1
  simp [one_div]

private theorem abs_measureLpGeneratorScalar_le (c : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    |(1 / t) * (Real.exp (-(t * c)) - 1)| ≤ c := by
  have htc : 0 ≤ t * (c : ℝ) := mul_nonneg ht.le c.coe_nonneg
  have hexp : Real.exp (-(t * c)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr htc)
  have hsub : 1 - Real.exp (-(t * c)) ≤ t * c := by
    linarith [Real.one_sub_le_exp_neg (t * (c : ℝ))]
  rw [abs_of_nonpos]
  · calc
      -(1 / t * (Real.exp (-(t * c)) - 1)) =
          (1 - Real.exp (-(t * c))) / t := by ring
      _ ≤ c := (div_le_iff₀ ht).2 (by simpa only [mul_comm] using hsub)
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hexp)

private theorem measureLpGeneratorQuotient_ae {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) (f : Lp E p μ) :
    (1 / t) • ((ContractionSemigroup.ofMeasureLpMultiplication hm hp).realOperator t f - f)
      =ᵐ[μ] measureLpGeneratorQuotient m f t := by
  filter_upwards [Lp.coeFn_smul (1 / t)
      ((ContractionSemigroup.ofMeasureLpMultiplication hm hp).realOperator t f - f),
    Lp.coeFn_sub
      ((ContractionSemigroup.ofMeasureLpMultiplication hm hp).realOperator t f) f,
    ContractionSemigroup.ofMeasureLpMultiplication_realOperator_apply_ae hm hp ht.le f] with
      a hsmul hsub htime
  rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, htime]

omit [Fact (1 ≤ p)] in
private theorem aestronglyMeasurable_measureLpGeneratorQuotient {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (f : Lp E p μ) (t : ℝ) :
    AEStronglyMeasurable (measureLpGeneratorQuotient m f t) μ := by fun_prop

omit [Fact (1 ≤ p)] in
private theorem aestronglyMeasurable_measureLpGeneratorValue {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (f : Lp E p μ) :
    AEStronglyMeasurable (measureLpGeneratorValue m f) μ := by fun_prop

omit [Fact (1 ≤ p)] in
private theorem tendsto_measureLpGeneratorQuotient (m : α → ℝ≥0) (f : Lp E p μ)
    (a : α) :
    Tendsto (fun t => measureLpGeneratorQuotient m f t a) (nhdsWithin 0 (Ioi 0))
      (nhds (measureLpGeneratorValue m f a)) := by
  have hscalar := tendsto_measureLpGeneratorScalar (m a)
  have hsmul := hscalar.smul_const (f a)
  refine hsmul.congr' ?_
  filter_upwards with t
  simp only [measureLpGeneratorQuotient, one_div]
  rw [smul_sub, smul_smul, ← sub_smul]
  congr 1
  ring

private theorem mem_domain_of_memLp_measureLpMultiplication {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ)
    (hmf : MemLp (fun a => (m a : ℝ) • f a) p μ) :
    f ∈ (ContractionSemigroup.ofMeasureLpMultiplication hm hp).domain := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
  have hvalue : MemLp (measureLpGeneratorValue m f) p μ := by
    apply hmf.neg.ae_eq
    filter_upwards with a
    simp [measureLpGeneratorValue]
  refine (S.mem_domain_iff_tendsto f).2 ⟨hvalue.toLp (measureLpGeneratorValue m f), ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
  refine (TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
    (.of_forall fun t => aestronglyMeasurable_measureLpGeneratorQuotient hm f t)
    (aestronglyMeasurable_measureLpGeneratorValue hm f) hmf (C := 2) ?_ ?_).congr' ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with a
    have hscalar := abs_measureLpGeneratorScalar_le (m a) ht
    have hnorm :
        ‖measureLpGeneratorQuotient m f t a - measureLpGeneratorValue m f a‖ ≤
          2 * ‖(m a : ℝ) • f a‖ := by
      have heq :
          measureLpGeneratorQuotient m f t a - measureLpGeneratorValue m f a =
            ((1 / t) * (Real.exp (-(t * (m a))) - 1) - (-(m a : ℝ))) • f a := by
        simp only [measureLpGeneratorQuotient, measureLpGeneratorValue, one_div]
        module
      rw [heq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (m a).coe_nonneg]
      have hcoeff :
        |(1 / t) * (Real.exp (-(t * (m a))) - 1) - (-(m a : ℝ))|
            ≤ 2 * (m a : ℝ) := by
        calc
          |(1 / t) * (Real.exp (-(t * (m a))) - 1) - (-(m a : ℝ))|
              ≤ |(1 / t) * (Real.exp (-(t * (m a))) - 1)| + |-(m a : ℝ)| :=
                abs_sub _ _
          _ ≤ (m a : ℝ) + (m a : ℝ) := add_le_add hscalar (by simp)
          _ = 2 * (m a : ℝ) := by ring
      calc
        _ ≤ (2 * (m a : ℝ)) * ‖f a‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ = 2 * ((m a : ℝ) * ‖f a‖) := by ring
    rw [← ofReal_norm, ← ofReal_norm]
    calc
      _ ≤ ENNReal.ofReal (2 * ‖(m a : ℝ) • f a‖) := ENNReal.ofReal_le_ofReal hnorm
      _ = (2 : ℝ≥0) * ENNReal.ofReal ‖(m a : ℝ) • f a‖ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  · exact .of_forall fun a => tendsto_measureLpGeneratorQuotient m f a
  · filter_upwards [self_mem_nhdsWithin] with t ht
    apply eLpNorm_congr_ae
    exact ((measureLpGeneratorQuotient_ae hm hp ht f).sub EventuallyEq.rfl).symm

private theorem measureLpGenerator_limit_ae {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f g : Lp E p μ)
    (hg : Tendsto
      (fun t => (1 / t) •
        ((ContractionSemigroup.ofMeasureLpMultiplication hm hp).realOperator t f - f))
      (nhdsWithin 0 (Ioi 0)) (nhds g)) :
    (g : α → E) =ᵐ[μ] measureLpGeneratorValue m f := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
  obtain ⟨ns, hns, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae'
  have hpos : ∀ᶠ n in atTop, 0 < ns n := hns.eventually self_mem_nhdsWithin
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have hquot_ae : ∀ᵐ a ∂μ, ∀ n, N ≤ n →
      ((1 / ns n) • (S.realOperator (ns n) f - f)) a =
        measureLpGeneratorQuotient m f (ns n) a := by
    rw [ae_all_iff]
    intro n
    by_cases hn : N ≤ n
    · filter_upwards [measureLpGeneratorQuotient_ae hm hp (hN n hn) f] with a ha
      exact fun _ => ha
    · exact .of_forall fun _ hn' => (hn hn').elim
  have hpointwise : ∀ a,
      Tendsto (fun n => measureLpGeneratorQuotient m f (ns n) a) atTop
        (nhds (measureLpGeneratorValue m f a)) :=
    fun a => (tendsto_measureLpGeneratorQuotient m f a).comp hns
  filter_upwards [hns_ae, hquot_ae] with a hga hqa
  have hraw : Tendsto (fun n => measureLpGeneratorQuotient m f (ns n) a) atTop
      (nhds (g a)) := hga.congr' <| (eventually_ge_atTop N).mono fun n hn => hqa n hn
  exact tendsto_nhds_unique hraw (hpointwise a)

private theorem memLp_measureLpMultiplication_of_mem_domain {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ)
    (hf : f ∈ (ContractionSemigroup.ofMeasureLpMultiplication hm hp).domain) :
    MemLp (fun a => (m a : ℝ) • f a) p μ := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
  obtain ⟨g, hg⟩ := (S.mem_domain_iff_tendsto f).1 hf
  have hvalue_ae : (g : α → E) =ᵐ[μ] measureLpGeneratorValue m f :=
    measureLpGenerator_limit_ae hm hp f g hg
  have hneg : MemLp (measureLpGeneratorValue m f) p μ :=
    (Lp.memLp g).ae_eq hvalue_ae
  apply hneg.neg.ae_eq
  filter_upwards with a
  simp [measureLpGeneratorValue]

/-- The exact generator domain of the measure-space multiplication semigroup consists of the
functions `f` for which the weighted function `a ↦ m a • f a` belongs to `Lᵖ`. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_mem_domain_iff {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ) :
    f ∈ (ofMeasureLpMultiplication hm hp).domain ↔
      MemLp (fun a => (m a : ℝ) • f a) p μ :=
  ⟨memLp_measureLpMultiplication_of_mem_domain hm hp f,
    mem_domain_of_memLp_measureLpMultiplication hm hp f⟩

/-- The generator of the measure-space multiplication semigroup is multiplication by `-m`,
almost everywhere on its exact weighted-`Lᵖ` domain. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_generator_apply_ae
    {m : α → ℝ≥0} (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (f : (ofMeasureLpMultiplication (E := E) hm hp).domain) :
    (ofMeasureLpMultiplication hm hp).generator ⟨(f : Lp E p μ), by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact f.property⟩ =ᵐ[μ]
      fun a => (-(m a : ℝ)) • (f : Lp E p μ) a := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
  have hae := measureLpGenerator_limit_ae hm hp (f : Lp E p μ)
    (S.generator ⟨(f : Lp E p μ), by rw [S.generator_domain]; exact f.property⟩)
    (S.generator_tendsto f)
  refine hae.trans (.of_forall fun a => ?_)
  rfl

end TauCeti.Semigroups

end

end
