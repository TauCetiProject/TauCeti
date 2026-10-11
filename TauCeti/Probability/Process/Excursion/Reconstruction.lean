/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Excursion.Basic
public import TauCeti.Probability.Process.PathLaw.Basic

/-!
# Reconstructing a recurrent path from its excursions

A recurrent process that starts at `a₀` returns to it infinitely often, so concatenating its
excursions recovers the path: `pathOfExcursions_excursion` is the identity used here, and it needs
exactly that recurrence.  This file turns it into an identity of laws,

```text
pathLaw μ X = (pathLaw of the excursion process).map (pathOfExcursions a₀)
```

and nothing more.

Only that direction is established.  Concatenation is not injective on arbitrary excursion
sequences — a word containing `a₀` is split further when the excursions are read back — so the
converse `excursion_pathOfExcursions` carries the hypothesis that the words avoid `a₀`, and is not
used here.  What the identity above needs is a pushforward along a measurable map that is a.e. left
inverse to reading the excursions off, not a bijection.

This change of variables does not require any symmetry or mixture representation of the process.
The specialization to a recurrent process is in `TauCeti.Probability.Recurrent.Excursion`.

## Main results

* `TauCeti.Probability.measurable_pathOfExcursions` — concatenation is measurable;
* `TauCeti.Probability.pathLaw_eq_map_pathOfExcursions` — the path law is the pushforward of the
  excursion path law along concatenation.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **Concatenating a sequence of excursions is measurable.** Each coordinate of the concatenated
sequence depends on finitely many excursions. Their measurable lengths determine which word and
coordinate to read, so no discreteness assumption on the state space is needed. -/
theorem measurable_pathOfExcursions (a₀ : α) :
    Measurable (pathOfExcursions a₀ : (ℕ → List α) → ℕ → α) := by
  classical
  -- For finite prefixes, split at the measurable length of the first word and recurse on the tail.
  have hloop : ∀ n i, Measurable fun v : Fin n → List α => loopPathAt a₀ (List.ofFn v) i := by
    intro n
    induction n with
    | zero =>
      intro i
      simp_rw [List.ofFn_zero, loopPathAt_eq_of_loopSteps_le a₀ (bs := []) (by simp)]
      exact measurable_const
    | succ n ih =>
      intro i
      cases i with
      | zero =>
        simp only [loopPathAt_zero]
        exact measurable_const
      | succ i =>
        have hlen : Measurable fun v : Fin (n + 1) → List α => (v 0).length :=
          measurable_list_length.comp (measurable_pi_apply 0)
        have htail : Measurable fun v : Fin (n + 1) → List α => fun j : Fin n => v j.succ :=
          Measurable.of_eval fun j => measurable_pi_apply j.succ
        have hread : Measurable fun p : (Fin n → List α) × ℕ =>
            loopPathAt a₀ (List.ofFn p.1) p.2 :=
          measurable_from_prod_countable_left fun j => ih j
        have hidx : Measurable fun v : Fin (n + 1) → List α => i - (v 0).length :=
          Measurable.of_discrete.comp hlen
        have hpiece : Measurable fun v : Fin (n + 1) → List α =>
            if i < (v 0).length then (v 0).getD i a₀
            else loopPathAt a₀ (List.ofFn fun j : Fin n => v j.succ) (i - (v 0).length) :=
          Measurable.ite (hlen (MeasurableSet.of_discrete (s := {l | i < l})))
            ((measurable_list_getD i a₀).comp (measurable_pi_apply 0))
            (hread.comp (htail.prodMk hidx))
        convert hpiece using 1
        funext v
        rw [List.ofFn_succ]
        by_cases hi : i < (v 0).length
        · simp only [hi, ite_true]
          rw [loopPathAt_cons_of_lt a₀ _ _ hi, List.getD_eq_getElem _ _ hi]
        · simp only [hi, ite_false]
          have heq : i + 1 = (v 0).length + 1 + (i - (v 0).length) := by omega
          rw [heq, loopPathAt_cons_add]
  -- Coordinate i factors through the first i + 1 excursions.
  refine Measurable.of_eval fun i => ?_
  have hfac : (fun b : ℕ → List α => pathOfExcursions a₀ b i) =
      (fun v : Fin (i + 1) → List α => loopPathAt a₀ (List.ofFn v) i) ∘
        fun (b : ℕ → List α) (j : Fin (i + 1)) => b j.val := by
    funext b
    have hi : i ≤ loopSteps ((List.range (i + 1)).map b) := by
      have hle := length_le_loopSteps ((List.range (i + 1)).map b)
      simp only [List.length_map, List.length_range] at hle
      omega
    rw [Function.comp_apply, pathOfExcursions_eq_loopPathAt a₀ b hi]
    congr 1
    refine List.ext_getElem (by simp) fun j hj hj' => ?_
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [hfac]
  exact (hloop (i + 1) i).comp (Measurable.of_eval fun j => measurable_pi_apply _)

/-! ## Reconstructing the path law -/

/-- **The path law of a process returning infinitely often to `a₀` is the image of its excursion
law.** Almost every sample path starts at and returns infinitely often to `a₀`, so concatenating
its excursions recovers it. Only the base state's singleton needs to be measurable. -/
theorem pathLaw_eq_map_pathOfExcursions
    (hX : ∀ i, AEMeasurable (X i) μ) (ha₀ : MeasurableSet ({a₀} : Set α))
    (hreturns : ∀ᵐ ω ∂μ, {n | X n ω = a₀}.Infinite)
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    pathLaw μ X = (pathLaw μ (excursionProcess X a₀)).map (pathOfExcursions a₀) := by
  have hΦ : AEMeasurable (fun ω k => excursionProcess X a₀ k ω) μ :=
    AEMeasurable.of_eval fun k => aemeasurable_excursionProcess hX a₀ ha₀ k
  have hae : (pathOfExcursions a₀ ∘ fun ω k => excursionProcess X a₀ k ω) =ᵐ[μ]
      fun ω i => X i ω := by
    filter_upwards [h0, hreturns] with ω hω0 hωinf
    simpa [Function.comp_def] using pathOfExcursions_excursion hωinf hω0
  rw [pathLaw_def, pathLaw_def,
    AEMeasurable.map_map_of_aemeasurable (measurable_pathOfExcursions a₀).aemeasurable hΦ,
    Measure.map_congr hae]

end Probability

end TauCeti
