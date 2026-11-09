/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.RandomMeasure.Independence
import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Independent restrictions of Poisson random measures

Restrictions of a Poisson random measure to disjoint measurable sets are independent as
random measures, not just at individual count coordinates. In particular, the entire past
and future restrictions of a temporal Poisson measure are independent. No local finiteness,
atomlessness, or topological structure on the state space is required.

First, independent counts extend to arbitrary disjoint families, allowing sets of infinite
intensity: their counts are almost surely the constant infinity. Finite Boolean partitions
then reduce overlapping evaluation vectors within each restriction to disjoint counts.
The evaluation criterion for random-measure independence extends this to the Giry sigma-field.
The Boolean-partition argument follows the law-determination proof in
`TauCeti/Probability/RandomMeasure/Law.lean`.

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

/-- Counts of a Poisson random measure on any disjoint measurable family are independent.
Sets of infinite intensity are allowed; their counts are almost surely infinite. -/
theorem IsPoissonRandomMeasure.iIndepFun_eval (h : IsPoissonRandomMeasure P N Λ)
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) : ProbabilityTheory.iIndepFun (fun i ω ↦ N ω (A i)) P := by
  classical
  apply iIndepFun_iff_finset.mpr
  intro I
  let e := Fintype.equivFin I
  let B (j : Fin (Fintype.card I)) := if Λ (A (e.symm j)) < ∞ then A (e.symm j) else ∅
  have hB j : MeasurableSet (B j) := by dsimp [B]; split_ifs <;> simp_all
  have hfin j : Λ (B j) < ∞ := by dsimp [B]; split_ifs <;> simp_all
  have hsub j : B j ⊆ A (e.symm j) := by dsimp [B]; split_ifs <;> simp
  have hdB : Pairwise (Disjoint on B) := by
    intro i j hij
    exact (hd (by exact_mod_cast e.symm.injective.ne hij)).mono (hsub i) (hsub j)
  let φ (j : Fin (Fintype.card I)) (x : ℝ≥0∞) :=
    if Λ (A (e.symm j)) < ∞ then x else ∞
  have hind := (h.iIndepFun hB hfin hdB).comp φ (fun j ↦ by
    dsimp [φ]; split_ifs <;> fun_prop)
  have heq j : (φ j ∘ fun ω ↦ N ω (B j)) =ᵐ[P] fun ω ↦ N ω (A (e.symm j)) := by
    by_cases hj : Λ (A (e.symm j)) < ∞
    · simp [φ, B, hj, Function.comp_def]
    · filter_upwards [h.ae_eq_top (hA _) (not_lt_top_iff.mp hj)] with ω hω
      simp [φ, hj, hω]
  exact (hind.congr heq).of_precomp (g := e.symm) e.symm.surjective

private theorem indepFun_inter_fibers (h : IsPoissonRandomMeasure P N Λ)
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B] {c : X → B}
    (hc : Measurable c) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    IndepFun (fun ω b ↦ N ω (c ⁻¹' {b} ∩ s))
      (fun ω b ↦ N ω (c ⁻¹' {b} ∩ t)) P := by
  let C (u : Set X) (b : B) := c ⁻¹' {b} ∩ u
  have hC (u : Set X) (hu : MeasurableSet u) (b : B) : MeasurableSet (C u b) :=
    (hc (measurableSet_singleton b)).inter hu
  have hd : Pairwise (Disjoint on Sum.elim (C s) (C t)) := by
    rintro (a | a) (b | b) hab
    · exact ((pairwise_disjoint_fiber c) (by simpa using hab)).mono
        inter_subset_left inter_subset_left
    · exact hst.mono inter_subset_right inter_subset_right
    · exact hst.symm.mono inter_subset_right inter_subset_right
    · exact ((pairwise_disjoint_fiber c) (by simpa using hab)).mono
        inter_subset_left inter_subset_left
  have hcounts : ProbabilityTheory.iIndepFun
      (Sum.elim (fun b ω ↦ N ω (C s b)) (fun b ω ↦ N ω (C t b))) P := by
    convert h.iIndepFun_eval (A := Sum.elim (C s) (C t))
      (by rintro (b | b); exacts [hC s hs b, hC t ht b]) hd using 1
    funext j
    cases j <;> rfl
  exact hcounts.indepFun_fun_sumElim
    (fun b ↦ (Measure.measurable_coe (hC s hs b)).comp h.measurable)
    (fun b ↦ (Measure.measurable_coe (hC t ht b)).comp h.measurable)

/-- Restrictions of a Poisson random measure to two disjoint measurable sets are independent
as random measures for the full evaluation sigma-field. Overlapping test sets within either
restriction, infinite total intensities, and multiple occurrences are all permitted. -/
theorem IsPoissonRandomMeasure.indepFun_restrict (h : IsPoissonRandomMeasure P N Λ)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    IndepFun (fun ω ↦ (N ω).restrict s) (fun ω ↦ (N ω).restrict t) P := by
  classical
  let := h.isProbabilityMeasure
  apply (indepFun_measure_iff (h.restrict hs).measurable.aemeasurable
    (h.restrict ht).measurable.aemeasurable).mpr
  intro I J
  -- Encode all test sets at once; each restriction is reconstructed from the same partition.
  let A : I ⊕ J → Set X := Sum.elim (fun a ↦ a.val.val) (fun a ↦ a.val.val)
  have hA : ∀ a, MeasurableSet (A a) := by rintro (a | a) <;> exact a.val.property
  let c : X → ((I ⊕ J) → Bool) := fun x a ↦ decide (x ∈ A a)
  have hc : Measurable c := Measurable.of_eval fun a ↦ by
    simpa [c] using (measurable_const.ite (hA a) measurable_const :
      Measurable fun x ↦ if x ∈ A a then true else false)
  let B := (I ⊕ J) → Bool
  let C (u : Set X) (b : B) := c ⁻¹' {b} ∩ u
  have hind : IndepFun (fun ω b ↦ N ω (C s b)) (fun ω b ↦ N ω (C t b)) P :=
    indepFun_inter_fibers h hc hs ht hst
  let bits (a : I ⊕ J) := Finset.univ.filter fun b : B ↦ b a = true
  let Φ (a : I ⊕ J) (v : B → ℝ≥0∞) := ∑ b ∈ bits a, v b
  have hΦ a : Measurable (Φ a) :=
    Finset.measurable_fun_sum _ fun b _ ↦ measurable_pi_apply b
  -- Finite additivity recovers each test count, including when some atom has infinite mass.
  have hrec (μ : Measure X) (u : Set X) (a : I ⊕ J) :
      Φ a (fun b ↦ μ (C u b)) = (μ.restrict u) (A a) := by
    simp_rw [Φ, C, ← Measure.restrict_apply (hc (measurableSet_singleton _))]
    rw [sum_measure_preimage_singleton (bits a) (fun b _ ↦ hc (measurableSet_singleton b))]
    congr 1
    ext x
    simp [bits, c]
  have hcomp := hind.comp
    (φ := fun v (a : I) ↦ Φ (.inl a) v)
    (ψ := fun v (a : J) ↦ Φ (.inr a) v)
    (Measurable.of_eval fun a ↦ hΦ (.inl a))
    (Measurable.of_eval fun a ↦ hΦ (.inr a))
  simpa only [Function.comp_def, hrec, A, Sum.elim_inl, Sum.elim_inr] using hcomp

end TauCeti.Probability
