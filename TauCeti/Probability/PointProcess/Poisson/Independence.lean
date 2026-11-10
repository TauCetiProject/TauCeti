/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.RandomMeasure.Independence
import TauCeti.MeasureTheory.Measure.BooleanPartition
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent restrictions of Poisson random measures

Restrictions of a Poisson random measure to any pairwise-disjoint measurable family are
independent as random measures, not just at individual count coordinates. In particular,
the entire past and future restrictions of a temporal Poisson measure are independent.
No local finiteness, atomlessness, or topological structure on the state space is required.

Finite Boolean partitions reduce overlapping evaluation vectors within each restriction
to disjoint counts. The evaluation criterion for random-measure independence extends this
to the Giry sigma-field. The Boolean-partition reconstruction is shared with the
law-determination proof in `TauCeti/Probability/RandomMeasure/Law.lean`.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 3 and 5.
-/

public section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X}

private theorem iIndepFun_inter_fibers (h : IsPoissonRandomMeasure P N Λ)
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B] {c : X → B}
    (hc : Measurable c) {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) :
    ProbabilityTheory.iIndepFun (fun i ω b ↦ N ω (c ⁻¹' {b} ∩ A i)) P := by
  let := h.isProbabilityMeasure
  let C (p : ι × B) := c ⁻¹' {p.2} ∩ A p.1
  have hC p : MeasurableSet (C p) := (hc (measurableSet_singleton _)).inter (hA _)
  have hdC : Pairwise (Disjoint on C) := by
    rintro ⟨i, b⟩ ⟨j, d⟩ hij
    by_cases he : i = j
    · subst j
      exact ((pairwise_disjoint_fiber c) (fun hb ↦ hij (Prod.ext rfl hb))).mono
        inter_subset_left inter_subset_left
    · exact (hd he).mono inter_subset_right inter_subset_right
  let Z (p : ι × B) (ω : Ω) := N ω (C p)
  have hm p : Measurable (Z p) := (Measure.measurable_coe (hC p)).comp h.measurable
  have hind := h.iIndepFun_eval hC hdC
  let μ (i : ι) (b : B) := P.map (Z (i, b))
  let hμ (i : ι) (b : B) : IsProbabilityMeasure (μ i b) :=
    (Measure.isProbabilityMeasure_map_iff (hm (i, b)).aemeasurable).mpr inferInstance
  have hrow i : P.map (fun ω b ↦ Z (i, b) ω) = Measure.infinitePi (μ i) :=
    (hind.precomp (fun _ _ he ↦ congrArg Prod.snd he)).map_fun_eq_infinitePi_map
      (fun b ↦ hm (i, b))
  -- Regroup the independent atom coordinates into one vector for each restriction.
  have hmap := congrArg (fun Q ↦ Q.map (MeasurableEquiv.curry ι B ℝ≥0∞))
    (hind.map_fun_eq_infinitePi_map hm)
  rw [Measure.map_map (MeasurableEquiv.curry ι B ℝ≥0∞).measurable
    (Measurable.of_eval hm), Measure.infinitePi_map_curry (μ := μ)] at hmap
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun i ω b ↦ Z (i, b) ω)
    (fun i ↦ Measurable.of_eval fun b ↦ hm (i, b))).mpr
  simp_rw [hrow]
  convert hmap using 2
  funext ω i b
  simp only [MeasurableEquiv.coe_curry, Function.comp_apply, Function.curry_apply, Z]

/-- Restrictions of a Poisson random measure to any pairwise-disjoint measurable family are
independent for the full evaluation sigma-field. Overlapping test sets within a restriction
and infinite total intensities are permitted. -/
theorem IsPoissonRandomMeasure.iIndepFun_restrict (h : IsPoissonRandomMeasure P N Λ)
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A)) :
    ProbabilityTheory.iIndepFun (fun i ω ↦ (N ω).restrict (A i)) P := by
  classical
  apply (iIndepFun_measure_iff (fun i ↦ (h.restrict (hA i)).measurable.aemeasurable)).mpr
  intro I J
  -- Encode all test sets at once, even when different restrictions use different tests.
  let K := (i : I) × J i
  let D (a : K) : Set X := a.2.val.val
  have hD a : MeasurableSet (D a) := a.2.val.property
  let c : X → (K → Bool) := fun x a ↦ decide (x ∈ D a)
  have hc : Measurable c := TauCeti.measurable_pi_decide_mem hD
  let B := K → Bool
  let Φ (i : I) (v : B → ℝ≥0∞) (a : J i) :=
    ∑ b ∈ Finset.univ.filter (fun b : B ↦ b ⟨i, a⟩ = true), v b
  have hΦ i : Measurable (Φ i) := Measurable.of_eval fun a ↦
    Finset.measurable_fun_sum _ fun b _ ↦ measurable_pi_apply b
  have hrec (μ : Measure X) (i : I) (a : J i) :
      Φ i (fun b ↦ μ (c ⁻¹' {b} ∩ A i)) a = (μ.restrict (A i)) a.val.val := by
    simp_rw [Φ, ← Measure.restrict_apply (hc (measurableSet_singleton _))]
    exact ((μ.restrict (A i)).apply_eq_sum_mem_partition hD ⟨i, a⟩).symm
  have hind := iIndepFun_inter_fibers h hc (fun i : I ↦ hA i)
    (fun i j hij ↦ hd (Subtype.val_injective.ne hij))
  convert hind.comp Φ hΦ using 1
  funext i ω a
  exact (hrec (N ω) i a).symm

/-- Restrictions of a Poisson random measure to two disjoint measurable sets are independent
as random measures for the full evaluation sigma-field. -/
theorem IsPoissonRandomMeasure.indepFun_restrict (h : IsPoissonRandomMeasure P N Λ)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    IndepFun (fun ω ↦ (N ω).restrict s) (fun ω ↦ (N ω).restrict t) P := by
  let A : Bool → Set X := fun b ↦ cond b s t
  have hA b : MeasurableSet (A b) := by cases b <;> assumption
  have hd : Pairwise (Disjoint on A) := pairwise_disjoint_on_bool.mpr hst
  exact (h.iIndepFun_restrict hA hd).indepFun (i := true) (j := false) (by decide)

end TauCeti.Probability
