/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Variation
public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
import TauCeti.Topology.EMetricSpace.VariationOnFromTo

/-!
# Adapted variation parts and finite-horizon vector measures

A continuous adapted real process of locally bounded variation decomposes into two continuous
adapted increasing processes starting at zero. Their sum is the accumulated variation and their
difference is the original process minus its initial value. In particular the parts are
predictable on the original filtration; no moment bounds or usual conditions are needed.

Together with `BoundedVariationOn.vectorMeasureIcc_eq_toSignedMeasure_sub`, this decomposition
identifies the finite-horizon derivative signed measure with the difference of the parts'
Stieltjes measures restricted to `(a, b]`.

For strongly adapted processes valued in a complete normed group with BV paths on a finite
horizon, fixed-set evaluations of the derivative vector measure are strongly measurable at the
horizon. This supplies finite-variation integrators without assuming that the original path is
increasing or globally BV. The open initial endpoint excludes an initial atom.

The construction uses Mathlib's signed-variation formulas
`variationOnFromTo.add_self_monotoneOn` and `variationOnFromTo.sub_self_monotoneOn`, and the
adaptation of accumulated variation from `TauCeti.Probability.Process.Variation`.

## References

* P. Protter, *Stochastic Integration and Differential Equations*, second edition, Chapter I.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory.StronglyAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {X : ℝ≥0 → Ω → ℝ}

/-- The positive and negative variation parts of a continuous adapted locally BV process can
be chosen continuously and predictably on its raw filtration. Both start at zero; their sum
is the accumulated variation, and their difference is the process minus its initial value. -/
theorem exists_stieltjesFunction_sub (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hv : ∀ ω, LocallyBoundedVariationOn (fun t => X t ω) univ) :
    ∃ p q : Ω → StieltjesFunction ℝ≥0,
      (∀ ω, Continuous (p ω)) ∧ (∀ ω, Continuous (q ω)) ∧
      IsStronglyPredictable ℱ (fun t ω => p ω t) ∧
      IsStronglyPredictable ℱ (fun t ω => q ω t) ∧
      (∀ ω, p ω 0 = 0 ∧ q ω 0 = 0) ∧
      (∀ t ω, X t ω - X 0 ω = p ω t - q ω t) ∧
      ∀ t ω, p ω t + q ω t = _root_.variationOnFromTo (fun s => X s ω) univ 0 t := by
  let V := fun t ω => _root_.variationOnFromTo (fun s => X s ω) univ 0 t
  have hVc (ω) : Continuous (fun t => V t ω) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      ((hv ω).continuousWithinAt_variationOnFromTo_iff (mem_univ 0) (mem_univ t)).mpr
        (hc ω |>.continuousAt.continuousWithinAt) |>.continuousAt (by simp)
  -- The canonical signed-variation parts preserve adaptation, unlike arbitrary pathwise choices.
  let p : Ω → StieltjesFunction ℝ≥0 := fun ω =>
    { toFun := fun t => (V t ω + X t ω - X 0 ω) / 2
      mono' := fun s t hst => by
        have h := variationOnFromTo.add_self_monotoneOn (hv ω) (mem_univ 0)
          (mem_univ s) (mem_univ t) hst
        dsimp only [Pi.add_apply] at h
        dsimp only [V]
        linarith
      right_continuous' := fun t =>
        (((hVc ω).add (hc ω)).sub continuous_const).div_const 2
          |>.continuousAt.continuousWithinAt }
  let q : Ω → StieltjesFunction ℝ≥0 := fun ω =>
    { toFun := fun t => (V t ω - X t ω + X 0 ω) / 2
      mono' := fun s t hst => by
        have h := variationOnFromTo.sub_self_monotoneOn (hv ω) (mem_univ 0)
          (mem_univ s) (mem_univ t) hst
        dsimp only [Pi.sub_apply] at h
        dsimp only [V]
        linarith
      right_continuous' := fun t =>
        (((hVc ω).sub (hc ω)).add continuous_const).div_const 2
          |>.continuousAt.continuousWithinAt }
  have hpc (ω) : Continuous (p ω) :=
    (((hVc ω).add (hc ω)).sub continuous_const).div_const 2
  have hqc (ω) : Continuous (q ω) :=
    (((hVc ω).sub (hc ω)).add continuous_const).div_const 2
  -- Transfer the fixed-time variation measurability to the parts, then use their continuity.
  have hVa := hX.variationOnFromTo hc
  have hp : StronglyAdapted ℱ (fun t ω => p ω t) := fun t =>
    ((((hVa t).add (hX t)).sub ((hX 0).mono (ℱ.mono (bot_le : 0 ≤ t)))).measurable.div_const
      2).stronglyMeasurable
  have hq : StronglyAdapted ℱ (fun t ω => q ω t) := fun t =>
    ((((hVa t).sub (hX t)).add ((hX 0).mono (ℱ.mono (bot_le : 0 ≤ t)))).measurable.div_const
      2).stronglyMeasurable
  refine ⟨p, q, hpc, hqc, hp.isStronglyPredictable_of_continuous hpc,
    hq.isStronglyPredictable_of_continuous hqc, ?_, ?_, ?_⟩
  · intro ω
    simp [p, q, V, variationOnFromTo.self]
  · intro t ω
    dsimp [p, q]
    ring
  · intro t ω
    dsimp [p, q]
    ring

section VectorMeasure

variable {R : Type*} [LinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [CompactIccSpace R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology R] [DenselyOrdered R]
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {ℱ : Filtration R m} {X : R → Ω → E} {a b : R}

/-- Every fixed-set evaluation of the finite-horizon Stieltjes vector measure of a strongly
adapted process with BV paths on that horizon is strongly measurable at the horizon.
No moments or path regularity outside the horizon are required. -/
theorem stronglyMeasurable_vectorMeasureIcc_apply (hX : StronglyAdapted ℱ X)
    (hab : a ≤ b)
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) (Icc a b)) (s : Set R) :
    StronglyMeasurable[ℱ b] (fun ω => (hv ω).vectorMeasureIcc hab s) := by
  let : MeasurableSpace Ω := ℱ b
  exact BoundedVariationOn.stronglyMeasurable_vectorMeasureIcc_apply hab
    (fun _ ht => hX.stronglyMeasurable_le ht.2) hv s

/-- Every fixed-set evaluation of the finite-horizon Stieltjes vector measure of a strongly
adapted process with BV paths on that horizon is measurable at the horizon.
No moments or path regularity outside the horizon are required. -/
theorem measurable_vectorMeasureIcc_apply [MeasurableSpace E] [BorelSpace E]
    (hX : StronglyAdapted ℱ X) (hab : a ≤ b)
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) (Icc a b)) (s : Set R) :
    Measurable[ℱ b] (fun ω => (hv ω).vectorMeasureIcc hab s) :=
  (hX.stronglyMeasurable_vectorMeasureIcc_apply hab hv s).measurable

end VectorMeasure

end MeasureTheory.StronglyAdapted
