/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Multiplication semigroups on measure-space Lᵖ

For an almost everywhere measurable nonnegative multiplier `m`, multiplication by `exp (-t * m)`
defines a strongly continuous contraction semigroup on `Lᵖ(μ; E)` for `1 ≤ p < ∞`, where `E`
is a real normed space. The measure is arbitrary and the multiplier may be unbounded. The action is
specified almost everywhere, as required for equivalence classes of measurable functions.

Strong continuity comes from dominated convergence in Lᵖ; the multiplier itself need not
belong to any Lᵖ space. This provides multiplication examples with continuous spatial variables,
including Lebesgue measure, in addition to the discrete ℓᵖ examples.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section I.4.c (multiplication semigroups).

The bounded operators use Mathlib's `ContinuousLinearMap.holderL` construction.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Semigroups

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def multiplicationWeight {m : α → ℝ≥0} (hm : AEMeasurable m μ) (t : ℝ≥0) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound (by fun_prop) 1 (.of_forall fun a => by
    simp only [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity))).toLp
    (fun a => Real.exp (-((t : ℝ) * m a)))

private theorem multiplicationWeight_ae {m : α → ℝ≥0} (hm : AEMeasurable m μ) (t : ℝ≥0) :
    multiplicationWeight (μ := μ) hm t =ᵐ[μ] fun a => Real.exp (-((t : ℝ) * m a)) :=
  MemLp.coeFn_toLp _

private def measureLpMultiplicationOperator {m : α → ℝ≥0} (hm : AEMeasurable m μ) (t : ℝ≥0) :
    Lp E p μ →L[ℝ] Lp E p μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ p p (multiplicationWeight hm t)

private theorem measureLpMultiplicationOperator_ae {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (t : ℝ≥0) (f : Lp E p μ) :
    measureLpMultiplicationOperator hm t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) • f a := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder
    (r := p) (multiplicationWeight hm t) f, multiplicationWeight_ae hm t] with a ha hw
  simpa only [measureLpMultiplicationOperator, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.lsmul_apply, hw] using ha

private theorem measureLpMultiplicationOperator_norm_le {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (t : ℝ≥0) : ‖measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm t) zero_le_one ?_
  intro f
  rw [one_mul]
  refine Lp.norm_le_norm_of_ae_le (f := measureLpMultiplicationOperator hm t f) (g := f) ?_
  filter_upwards [measureLpMultiplicationOperator_ae hm t f] with a ha
  rw [ha, norm_smul, Real.norm_eq_abs, Real.abs_exp]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))

private theorem measureLpMultiplicationOperator_zero {m : α → ℝ≥0} (hm : AEMeasurable m μ) :
    measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm 0 =
      ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [measureLpMultiplicationOperator_ae hm 0 f] with a ha
  simpa using ha

private theorem measureLpMultiplicationOperator_add {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (s t : ℝ≥0) :
    measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm (s + t) =
      (measureLpMultiplicationOperator hm s).comp (measureLpMultiplicationOperator hm t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [measureLpMultiplicationOperator_ae hm (s + t) f,
    measureLpMultiplicationOperator_ae hm s (measureLpMultiplicationOperator hm t f),
    measureLpMultiplicationOperator_ae hm t f] with a hst hs ht
  simp only [ContinuousLinearMap.comp_apply, hst, hs, ht, NNReal.coe_add, smul_smul]
  rw [← Real.exp_add]
  congr 2
  ring

private theorem measureLpMultiplicationOperator_continuous {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous (fun t : ℝ≥0 => measureLpMultiplicationOperator hm t f) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (measureLpMultiplicationOperator hm s f)).2
  have hlim : Tendsto
      (fun t : ℝ≥0 => eLpNorm
        ((fun a => Real.exp (-((t : ℝ) * m a)) • f a) -
          (fun a => Real.exp (-((s : ℝ) * m a)) • f a)) p μ) (𝓝 s) (𝓝 0) := by
    apply TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
      (.of_forall fun t => by fun_prop) (by fun_prop) (Lp.memLp f) (C := 2)
    · filter_upwards with t
      filter_upwards with a
      have hbound (u : ℝ≥0) : ‖Real.exp (-((u : ℝ) * m a)) • f a‖ₑ ≤ ‖f a‖ₑ := by
        rw [enorm_smul]
        apply mul_le_of_le_one_left zero_le
        rw [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_le_coe]
        apply NNReal.coe_le_coe.mp
        simp only [coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs, Real.abs_exp,
          Real.exp_le_one_iff]
        exact neg_nonpos.mpr (by positivity)
      calc
        ‖Real.exp (-((t : ℝ) * m a)) • f a - Real.exp (-((s : ℝ) * m a)) • f a‖ₑ
            ≤ ‖Real.exp (-((t : ℝ) * m a)) • f a‖ₑ +
              ‖Real.exp (-((s : ℝ) * m a)) • f a‖ₑ := enorm_sub_le
        _ ≤ ‖f a‖ₑ + ‖f a‖ₑ := add_le_add (hbound t) (hbound s)
        _ = (2 : ℝ≥0) * ‖f a‖ₑ := by simp [two_mul]
    · filter_upwards with a
      have hcont : Continuous (fun t : ℝ≥0 => Real.exp (-((t : ℝ) * m a)) • f a) := by
        fun_prop
      exact hcont.tendsto s
  refine hlim.congr fun t => ?_
  apply eLpNorm_congr_ae
  exact ((measureLpMultiplicationOperator_ae hm t f).sub
    (measureLpMultiplicationOperator_ae hm s f)).symm

/-- The multiplication contraction semigroup on measure-space Lᵖ, for `1 ≤ p < ∞`.
The nonnegative almost everywhere measurable multiplier need not be bounded, and the measure
is arbitrary. -/
def ContractionSemigroup.ofMeasureLpMultiplication {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) : ContractionSemigroup (Lp E p μ) where
  toFun := measureLpMultiplicationOperator hm
  map_zero' := measureLpMultiplicationOperator_zero hm
  map_add' := measureLpMultiplicationOperator_add hm
  continuousAt_zero' := fun f => (measureLpMultiplicationOperator_continuous hm hp f).continuousAt
  contracting := measureLpMultiplicationOperator_norm_le hm

/-- The multiplication semigroup acts by `exp (-t * m)` almost everywhere. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_apply_apply_ae {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (t : ℝ≥0) (f : Lp E p μ) :
    ofMeasureLpMultiplication hm hp t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) • f a :=
  measureLpMultiplicationOperator_ae hm t f

/-- Multiplication semigroup orbits are continuous even when the value space is incomplete. -/
@[fun_prop]
theorem ContractionSemigroup.continuous_ofMeasureLpMultiplication {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous (fun t : ℝ≥0 => ofMeasureLpMultiplication hm hp t f) :=
  measureLpMultiplicationOperator_continuous hm hp f

/-- At a nonnegative real time, the multiplication semigroup acts by `exp (-t * m)` almost
everywhere. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_realOperator_apply_ae {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) {t : ℝ} (ht : 0 ≤ t) (f : Lp E p μ) :
    (ofMeasureLpMultiplication hm hp).realOperator t f =ᵐ[μ]
      fun a => Real.exp (-(t * m a)) • f a := by
  rw [StronglyContinuousSemigroup.realOperator_def,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply]
  simpa only [Real.coe_toNNReal t ht] using
    ofMeasureLpMultiplication_apply_apply_ae hm hp t.toNNReal f

/-- Almost everywhere equal multipliers define the same multiplication semigroup. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_congr_ae {m n : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (h : m =ᵐ[μ] n) :
    ofMeasureLpMultiplication (E := E) hm hp = ofMeasureLpMultiplication (hm.congr h) hp := by
  apply ContractionSemigroup.ext
  intro t
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [ofMeasureLpMultiplication_apply_apply_ae hm hp t f,
    ofMeasureLpMultiplication_apply_apply_ae (hm.congr h) hp t f, h] with a hm hn hmn
  rw [hm, hn, hmn]

end TauCeti.Semigroups
