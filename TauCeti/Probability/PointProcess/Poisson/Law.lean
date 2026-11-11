/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.RandomMeasure.Law

/-!
# Uniqueness of Poisson random-measure laws

The independent-count specification determines the whole law of a Poisson random measure,
on an arbitrary measurable location space. Two realizations can live on different sample
spaces. Equality here is equality in distribution, not almost-sure equality.

We first compute the joint law of counts on any finite disjoint measurable family, without
requiring finite intensity: an infinite-intensity coordinate has the point mass at infinity.
This handles mixed finite and infinite coordinates and the empty family. The evaluation
uniqueness theorem for random measures then identifies the entire law. No topology,
integer-valued carrier, or finiteness of the total intensity is required.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Proposition 3.2 (uniqueness in distribution from the Poisson counts).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace X] {P : Measure Ω} {P' : Measure Ω'}
  {N : Ω → Measure X} {N' : Ω' → Measure X} {Λ : Measure X}

/-- The joint count law on disjoint measurable sets is a product. Finite-intensity
coordinates have Poisson laws, and infinite-intensity coordinates equal infinity almost
surely. In particular this also describes families mixing both kinds of coordinates. -/
theorem IsPoissonRandomMeasure.hasLaw_eval_pi (h : IsPoissonRandomMeasure P N Λ)
    {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) :
    HasLaw (fun ω i => N ω (A i))
      (Measure.pi fun i => if Λ (A i) = ∞ then Measure.dirac ∞ else
        (poissonMeasure (Λ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  classical
  let := h.isProbabilityMeasure
  -- Replace the infinite-intensity sets by empty sets before applying independence.
  let B : Fin n → Set X := fun i => if Λ (A i) = ∞ then ∅ else A i
  have hB (i) : MeasurableSet (B i) := by
    dsimp [B]
    split_ifs <;> simp_all
  have hfin (i) : Λ (B i) < ∞ := by
    dsimp [B]
    split_ifs with hi
    · simp
    · exact lt_top_iff_ne_top.mpr hi
  have hsub (i) : B i ⊆ A i := by
    dsimp [B]
    split_ifs <;> simp
  have hind := h.iIndepFun hB hfin
    (fun i j hij => (hd hij).mono (hsub i) (hsub j))
  let f : Fin n → ℝ≥0∞ → ℝ≥0∞ := fun i v => if Λ (A i) = ∞ then ∞ else v
  have hf (i) : Measurable (f i) := by
    dsimp [f]
    split_ifs <;> fun_prop
  have heq (i) : (f i ∘ fun ω => N ω (B i)) =ᵐ[P] fun ω => N ω (A i) := by
    by_cases hi : Λ (A i) = ∞
    · filter_upwards [h.ae_eq_top (hA i) hi] with ω hω
      simp [f, hi, hω]
    · simp [f, B, hi, Function.comp_def]
  have hindA : ProbabilityTheory.iIndepFun (fun i ω => N ω (A i)) P :=
    (hind.comp f hf).congr heq
  apply ProbabilityTheory.iIndepFun.hasLaw_pi _ hindA
  intro i
  by_cases hi : Λ (A i) = ∞
  · simp only [hi, ↓reduceIte]
    exact hasLaw_dirac_of_ae_eq (h.ae_eq_top (hA i) hi)
  · simpa only [hi, ↓reduceIte] using h.hasLaw (hA i) (lt_top_iff_ne_top.mpr hi)

/-- Poisson random measures with the same intensity have the same law, including on
arbitrary measurable location spaces and on different sample spaces. This does not assert
almost-sure equality of the random measures. -/
theorem IsPoissonRandomMeasure.identDistrib (h : IsPoissonRandomMeasure P N Λ)
    (h' : IsPoissonRandomMeasure P' N' Λ) : IdentDistrib N N' P P' := by
  let := h.isProbabilityMeasure
  refine ⟨h.measurable.aemeasurable, h'.measurable.aemeasurable, ?_⟩
  apply (Measure.map_eq_iff_forall_map_eval_eq_of_pairwise_disjoint
    h.measurable.aemeasurable h'.measurable.aemeasurable).2
  intro n A hA hd
  exact (h.hasLaw_eval_pi hA hd).map_eq.trans (h'.hasLaw_eval_pi hA hd).map_eq.symm

end TauCeti.Probability
