/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import TauCeti.MeasureTheory.MeasurableSpace.List
public import TauCeti.Combinatorics.Enumerative.ExcursionProcess
import TauCeti.Probability.Process.SuccessorArray

/-!
# Excursion processes

The excursions of a process away from a state form a process of finite words. Reading an
excursion is measurable when the base state's singleton is measurable; no recurrence or
symmetry assumption is needed. When a path starts at the base state and makes the visit closing
its prescribed excursions, the excursion-prefix event agrees with a finite-path event.

These change-of-variables facts let excursion laws be studied independently of any symmetry
of the original process. Concatenation and reconstruction of the path law are developed in
`TauCeti.Probability.Process.Excursion.Reconstruction`.

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

/-- The excursion process of `X` away from `a₀`: its `k`-th value is the finite word the sample
path traverses strictly between its `k`-th and `(k + 1)`-st visits to `a₀`. -/
def excursionProcess (X : ℕ → Ω → α) (a₀ : α) : ℕ → Ω → List α :=
  fun k ω => excursion (fun n => X n ω) a₀ k

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem excursionProcess_apply (X : ℕ → Ω → α) (a₀ : α) (k : ℕ) (ω : Ω) :
    excursionProcess X a₀ k ω = excursion (fun n => X n ω) a₀ k :=
  (rfl)

section Measurability

/-- **An excursion is a measurable function of the path.** The two endpoint visit times are
measurable and range over a countable set, and on each of their fibres the excursion reads a fixed
finite list of coordinates. -/
theorem measurable_excursion (a₀ : α) (k : ℕ) (ha₀ : MeasurableSet ({a₀} : Set α)) :
    Measurable fun x : ℕ → α => excursion x a₀ k := by
  have hidx : Measurable fun x : ℕ → α => (visitTime x a₀ k + 1, visitTime x a₀ (k + 1)) :=
    (Measurable.of_discrete.comp
        (measurable_visitTime a₀ k ha₀)).prodMk
      (measurable_visitTime a₀ (k + 1) ha₀)
  have hread : Measurable fun p : (ℕ → α) × ℕ × ℕ => (List.Ico p.2.1 p.2.2).map p.1 := by
    apply measurable_from_prod_countable_left
    intro q
    dsimp only
    induction List.Ico q.1 q.2 using List.ofFnRec with | _ n f
    simp_rw [List.map_ofFn]
    exact measurable_list_ofFn.comp (Measurable.of_eval fun i => measurable_pi_apply (f i))
  have hunfold : (fun x : ℕ → α => excursion x a₀ k) =
      fun x : ℕ → α => (List.Ico (visitTime x a₀ k + 1) (visitTime x a₀ (k + 1))).map x :=
    funext fun x => excursion_def x a₀ k
  rw [hunfold]
  exact hread.comp (measurable_id.prodMk hidx)

/-- Every excursion of a process with a.e. measurable coordinates is a.e. measurable when the
base state's singleton is measurable. -/
theorem aemeasurable_excursionProcess {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (a₀ : α) (ha₀ : MeasurableSet ({a₀} : Set α)) (k : ℕ) :
    AEMeasurable (excursionProcess X a₀ k) μ :=
  (measurable_excursion a₀ k ha₀).comp_aemeasurable (AEMeasurable.of_eval hX)

end Measurability

variable {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

omit [MeasurableSpace α] in
/-- **Prescribing the first excursions is a finite-path event.** For a process almost surely
starting at `a₀` and almost surely making a `bs.length`-th visit to `a₀`, having `bs` as its first
`bs.length` excursions is, up to a null set, spelling out the loop word of `bs`. Only the visit
closing the last prescribed excursion is used, so this asks less than returning to `a₀` infinitely
often, let alone recurrence of the whole process; `TauCeti.exists_visitCount_of_infinite` supplies
the hypothesis from infinitely many returns. -/
theorem measure_setOf_excursionPrefix_eq {bs : List (List α)}
    (hvisit : ∀ᵐ ω ∂μ, ∃ n, X n ω = a₀ ∧ visitCount (fun n => X n ω) a₀ n = bs.length)
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) (havoid : ∀ e ∈ bs, a₀ ∉ e) :
    μ {ω | excursionPrefix (fun n => X n ω) a₀ bs.length = bs} =
      μ {ω | ∀ i ≤ loopSteps bs, X i ω = loopPathAt a₀ bs i} := by
  refine (measure_congr (Filter.eventuallyEqSet_iff.2 ?_)).symm
  filter_upwards [h0, hvisit] with ω hω0 hω
  exact eqOn_loopPathAt_iff_excursionPrefix_eq havoid hω hω0

end Probability

end TauCeti

end

end
