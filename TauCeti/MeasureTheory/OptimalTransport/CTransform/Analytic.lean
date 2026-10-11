/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Analytic
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.CyclicalMonotonicity

/-!
# Analytic measurability of the infimal `c`-transform

For Polish source and target spaces, a Borel integrand
`(x, y) ↦ (c (x, y) : EReal) - φ x` need not have a Borel infimum over `x`. Its strict sublevel
sets are nevertheless analytic: each is the projection of the corresponding Borel strict
sublevel set of the integrand. Lusin's universal-measurability theorem then makes every such
sublevel measurable in the completion of each s-finite Borel measure. This is the precise
measurability regime used to integrate general Kantorovich potentials without incorrectly claiming
Borel measurability.

The symmetric transform is included with the same hypotheses on the transposed integrand.

The same projection argument applies to Rüschendorf's potential `TauCeti.rockafellarPotential`
of a Borel set `S`, an infimum over finite chains of points of `S`: for each chain length, a strict
sublevel set is the projection of a Borel set of chains and targets, so the potential is
null-measurable. This is what lets the contact potential of a measurable `c`-cyclically monotone
set be integrated.

## Main results

* `TauCeti.analyticSet_setOf_cTransform_lt`: strict sublevels of the infimal transform are
  analytic;
* `TauCeti.nullMeasurableSet_setOf_cTransform_lt`: those sublevels are measurable after
  completing any s-finite Borel measure;
* `TauCeti.nullMeasurable_cTransform`: the transform itself is null-measurable for each s-finite
  Borel measure;
* the corresponding three results with `cTransformSymm` in their names;
* `TauCeti.analyticSet_setOf_rockafellarPotential_lt` and
  `TauCeti.nullMeasurable_rockafellarPotential`: the same two statements for Rüschendorf's
  potential of a Borel set.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 5.
* A. S. Kechris, *Classical Descriptive Set Theory*, Springer-Verlag, 1995, Theorem 29.7.
-/

public section

open MeasureTheory Set

noncomputable section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {c : X × Y → ℝ} {φ : X → EReal} {ψ : Y → EReal}

/-- If a strict sublevel of the defining integrand of a `c`-transform is Borel measurable, the
corresponding strict sublevel of the transform is analytic. It is the second-coordinate projection
of that integrand sublevel. -/
theorem analyticSet_setOf_cTransform_lt (a : EReal)
    (h : MeasurableSet {z : X × Y | (c z : EReal) - φ z.1 < a}) :
    AnalyticSet {y | cTransform c φ y < a} := by
  simpa only [cTransform_apply] using
    MeasureTheory.analyticSet_setOf_iInf_lt
      (fun z : X × Y => (c z : EReal) - φ z.1) a h

/-- If a strict sublevel of the defining integrand of a symmetric `c`-transform is Borel
measurable, the corresponding strict sublevel of the transform is analytic. -/
theorem analyticSet_setOf_cTransformSymm_lt (a : EReal)
    (h : MeasurableSet {z : X × Y | (c z : EReal) - ψ z.2 < a}) :
    AnalyticSet {x | cTransformSymm c ψ x < a} := by
  simpa only [cTransformSymm_apply] using
    MeasureTheory.analyticSet_setOf_iInf_lt
      (fun z : Y × X => (c (z.2, z.1) : EReal) - ψ z.1) a
        (h.preimage measurable_swap)

/-- A strict sublevel of a `c`-transform is measurable after completing any s-finite Borel measure
on the target when the corresponding integrand sublevel is Borel measurable. -/
theorem nullMeasurableSet_setOf_cTransform_lt (μ : Measure Y) [SFinite μ] (a : EReal)
    (h : MeasurableSet {z : X × Y | (c z : EReal) - φ z.1 < a}) :
    NullMeasurableSet {y | cTransform c φ y < a} μ :=
  MeasureTheory.AnalyticSet.nullMeasurableSet (analyticSet_setOf_cTransform_lt a h) μ

/-- A strict sublevel of a symmetric `c`-transform is measurable after completing any s-finite Borel
measure on the source when the corresponding integrand sublevel is Borel measurable. -/
theorem nullMeasurableSet_setOf_cTransformSymm_lt (μ : Measure X) [SFinite μ]
    (a : EReal) (h : MeasurableSet {z : X × Y | (c z : EReal) - ψ z.2 < a}) :
    NullMeasurableSet {x | cTransformSymm c ψ x < a} μ :=
  MeasureTheory.AnalyticSet.nullMeasurableSet (analyticSet_setOf_cTransformSymm_lt a h) μ

/-- A `c`-transform with Borel defining integrand is measurable for the completion of every
s-finite Borel measure on the target. This is deliberately `NullMeasurable`, not Borel
`Measurable`. -/
theorem nullMeasurable_cTransform (μ : Measure Y) [SFinite μ]
    (h : Measurable fun z : X × Y => (c z : EReal) - φ z.1) :
    NullMeasurable (cTransform c φ) μ :=
  measurable_of_Iio fun a =>
    nullMeasurableSet_setOf_cTransform_lt μ a (h measurableSet_Iio)

/-- A symmetric `c`-transform with Borel defining integrand is measurable for the completion of
every s-finite Borel measure on the source. -/
theorem nullMeasurable_cTransformSymm (μ : Measure X) [SFinite μ]
    (h : Measurable fun z : X × Y => (c z : EReal) - ψ z.2) :
    NullMeasurable (cTransformSymm c ψ) μ :=
  measurable_of_Iio fun a =>
    nullMeasurableSet_setOf_cTransformSymm_lt μ a (h measurableSet_Iio)

/-- For a Borel cost and a Borel set `S`, every strict sublevel set of Rüschendorf's potential
`TauCeti.rockafellarPotential c S p` is analytic. -/
theorem analyticSet_setOf_rockafellarPotential_lt {S : Set (X × Y)} (hc : Measurable c)
    (hS : MeasurableSet S) (p : X × Y) (a : EReal) :
    AnalyticSet {x | rockafellarPotential c S p x < a} := by
  -- The admissibility conditions on a chain are folded into the integrand as the value `⊤`.
  set f : (n : ℕ) → (Fin (n + 1) → X × Y) × X → EReal := fun n z =>
    ⨅ (_ : z.1 0 = p) (_ : ∀ i, z.1 i ∈ S), (rockafellarChainValue c z.1 z.2 : EReal) with hf
  have hset : {x | rockafellarPotential c S p x < a} = ⋃ n, {x | (⨅ w, f n (w, x)) < a} := by
    ext x
    simp [rockafellarPotential_def, hf, iInf_lt_iff]
  rw [hset]
  refine AnalyticSet.iUnion fun n => MeasureTheory.analyticSet_setOf_iInf_lt (f n) a ?_
  have hchain : Measurable fun z : (Fin (n + 1) → X × Y) × X =>
      (rockafellarChainValue c z.1 z.2 : EReal) := by
    simp_rw [rockafellarChainValue_def]
    fun_prop
  have heq : {z | f n z < a} =
      {z | z.1 0 = p} ∩ (⋂ i, {z | z.1 i ∈ S}) ∩ {z | (rockafellarChainValue c z.1 z.2 : EReal) < a}
      := by
    ext z
    simp only [hf, mem_ofPred_eq, iInf_lt_iff, mem_inter_iff, mem_iInter, exists_prop]
    tauto
  rw [heq]
  exact (((measurable_pi_apply 0).comp measurable_fst (measurableSet_singleton p)).inter
    (MeasurableSet.iInter fun i => (measurable_pi_apply i).comp measurable_fst hS)).inter
      (hchain measurableSet_Iio)

/-- **Rüschendorf's potential is universally measurable.** For a Borel cost and a Borel set `S`,
the potential `TauCeti.rockafellarPotential c S p` is measurable for the completion of every
s-finite Borel measure on the source. As for the `c`-transform, this is deliberately
`NullMeasurable`, not Borel `Measurable`. -/
theorem nullMeasurable_rockafellarPotential (μ : Measure X) [SFinite μ] {S : Set (X × Y)}
    (hc : Measurable c) (hS : MeasurableSet S) (p : X × Y) :
    NullMeasurable (rockafellarPotential c S p) μ :=
  measurable_of_Iio fun a =>
    MeasureTheory.AnalyticSet.nullMeasurableSet
      (analyticSet_setOf_rockafellarPotential_lt hc hS p a) μ

end TauCeti
