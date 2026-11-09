/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The measurable structure on lists

Mathlib equips no type of lists with a measurable structure. This file gives `List α` the structure
transported from its length-indexed representation `Σ n, Fin n → α`. Thus each fixed-length stratum
has the finite product structure, and the list space is their countable disjoint union.
List length and reading a fixed coordinate with a default are measurable for any measurable state
space.

When `α` is countable with measurable singletons, this structure is discrete. In particular, a
process whose values are finite words over a countable alphabet, such as the excursion process of a
path, has a countable discrete value space.

## Main declarations

* `TauCeti.instMeasurableSpaceList`: the measurable structure on `List α` induced by its
  length-indexed representation.
* `TauCeti.measurable_list_ofFn`: assembling a finite tuple into a list is measurable.
* `TauCeti.measurable_from_list_iff`: a map out of lists is measurable if and only if it is
  measurable on each fixed-length stratum.
* `TauCeti.instDiscreteMeasurableSpaceList`: discreteness when `α` is countable with measurable
  singletons.
* `TauCeti.measurable_list_length`: list length is measurable.
* `TauCeti.measurable_list_getD`: reading a coordinate with a fixed default is measurable.
-/

public section

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- The measurable structure on lists induced through
`List.equivSigmaTuple : List α ≃ Σ n, Fin n → α`. -/
instance instMeasurableSpaceList : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

/-- Assembling a finite tuple into a list is measurable for the length-indexed measurable
structure on lists. -/
theorem measurable_list_ofFn {n : ℕ} :
    Measurable (List.ofFn : (Fin n → α) → List α) := by
  rw [measurable_comap_iff]
  have hcomp : List.equivSigmaTuple ∘ List.ofFn = Sigma.mk (β := fun m => Fin m → α) n :=
    funext fun g => List.equivSigmaTuple.apply_symm_apply (⟨n, g⟩ : Σ m, Fin m → α)
  rw [hcomp]
  -- The sigma measurable structure is the infimum of the pushforwards along the strata.
  exact measurable_iff_le_map.2 (iInf_le _ n)

/-- A map out of lists is measurable if and only if it is measurable on each fixed-length
stratum, parametrized by `List.ofFn`. -/
theorem measurable_from_list_iff {β : Type*} [MeasurableSpace β] {f : List α → β} :
    Measurable f ↔ ∀ n, Measurable fun g : Fin n → α => f (List.ofFn g) := by
  refine ⟨fun hf n => hf.comp measurable_list_ofFn, fun h => ?_⟩
  -- The sigma measurable structure is the infimum of the pushforwards along the strata.
  have hsigma : Measurable (f ∘ List.equivSigmaTuple.symm) := by
    refine measurable_iff_comap_le.2 (le_iInf fun n => ?_)
    rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
    exact (h n).comap_le
  simpa [Function.comp_assoc] using hsigma.comp (comap_measurable List.equivSigmaTuple)

/-- Lists over a countable measurable space with measurable singletons form a discrete measurable
space. -/
instance instDiscreteMeasurableSpaceList [Countable α] [MeasurableSingletonClass α] :
    DiscreteMeasurableSpace (List α) :=
  ⟨fun _ => measurable_mem.1 <| measurable_from_list_iff.2 fun _ => .of_discrete⟩

/-- List length is measurable for the length-indexed measurable structure. -/
theorem measurable_list_length : Measurable (List.length : List α → ℕ) :=
  measurable_from_list_iff.2 fun _ => by simp

/-- Reading a fixed list coordinate with a fixed default is measurable. -/
theorem measurable_list_getD (i : ℕ) (a : α) :
    Measurable (fun l : List α => l.getD i a) := by
  refine measurable_from_list_iff.2 fun n => ?_
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem, hi] using measurable_pi_apply (⟨i, hi⟩ : Fin n)
  · simp [Nat.le_of_not_gt hi]

end TauCeti

end
