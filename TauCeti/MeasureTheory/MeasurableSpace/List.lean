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

## Main definitions

* `TauCeti.instMeasurableSpaceList`: the measurable structure on `List α` induced by its
  length-indexed representation.
* `TauCeti.instDiscreteMeasurableSpaceList`: discreteness when `α` is countable with measurable
  singletons.
* `TauCeti.measurable_list_ofFn`: assembling a finite tuple into a list is measurable.
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

/-- Lists over a countable measurable space with measurable singletons form a discrete measurable
space. -/
instance instDiscreteMeasurableSpaceList [Countable α] [MeasurableSingletonClass α] :
    DiscreteMeasurableSpace (List α) :=
  ⟨fun s => by
    -- Unfold measurability in the structure pulled back along the list-tuple equivalence.
    change ∃ t : Set (Σ n, Fin n → α), MeasurableSet t ∧
      Set.preimage (List.equivSigmaTuple : List α → Σ n, Fin n → α) t = s
    refine ⟨Set.image List.equivSigmaTuple s, ?_, ?_⟩
    -- The sigma measurable space tests measurability separately on each fixed-length stratum.
    · apply MeasurableSpace.measurableSet_iInf.2
      intro n
      change MeasurableSet (Set.preimage (Sigma.mk n) (Set.image List.equivSigmaTuple s))
      let _ : MeasurableSingletonClass (Fin n → α) := inferInstance
      let _ : DiscreteMeasurableSpace (Fin n → α) := inferInstance
      exact MeasurableSet.of_discrete
    · exact Set.preimage_image_eq s List.equivSigmaTuple.injective⟩

/-- Assembling a finite tuple into a list is measurable for the length-indexed measurable
structure on lists. -/
theorem measurable_list_ofFn {n : ℕ} :
    Measurable (List.ofFn : (Fin n → α) → List α) := by
  rw [measurable_comap_iff]
  have hmk : Measurable fun g : Fin n → α => (⟨n, g⟩ : Σ m, Fin m → α) := by
    refine Measurable.of_le_map ?_
    -- The sigma measurable space is the infimum over its fixed-length strata.
    change (⨅ m : ℕ, MeasurableSpace.map
      (@Sigma.mk ℕ (fun m => Fin m → α) m) inferInstance) ≤
        MeasurableSpace.map (@Sigma.mk ℕ (fun m => Fin m → α) n) inferInstance
    exact iInf_le _ n
  have hcomp : (List.equivSigmaTuple ∘ (List.ofFn : (Fin n → α) → List α)) =
      fun g => (⟨n, g⟩ : Σ m, Fin m → α) := by
    funext g
    simpa only [Function.comp_apply, List.equivSigmaTuple_symm_apply] using
      List.equivSigmaTuple.apply_symm_apply (⟨n, g⟩ : Σ m, Fin m → α)
  rw [hcomp]
  exact hmk

/-- List length is measurable for the length-indexed measurable structure. -/
theorem measurable_list_length : Measurable (List.length : List α → ℕ) := by
  have h : Measurable (fun v : Σ n, Fin n → α => v.1) := by
    intro s _
    apply MeasurableSpace.measurableSet_iInf.2
    intro n
    -- The sigma measurable space tests the preimage separately on each fixed-length stratum.
    change MeasurableSet {_f : Fin n → α | n ∈ s}
    by_cases hn : n ∈ s <;> simp [hn]
  exact h.comp (comap_measurable List.equivSigmaTuple)

/-- Reading a fixed list coordinate with a fixed default is measurable. -/
theorem measurable_list_getD (i : ℕ) (a : α) :
    Measurable (fun l : List α => l.getD i a) := by
  have h : Measurable (fun v : Σ n, Fin n → α => (List.ofFn v.2).getD i a) := by
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.2
    intro n
    -- On the length-n stratum, the sigma preimage is evaluation on finite tuples.
    change MeasurableSet {f : Fin n → α | (List.ofFn f).getD i a ∈ s}
    have hf : Measurable (fun f : Fin n → α => (List.ofFn f).getD i a) := by
      by_cases hi : i < n
      · simpa [List.getD_eq_getElem, hi] using measurable_pi_apply (⟨i, hi⟩ : Fin n)
      · have heq (f : Fin n → α) : (List.ofFn f).getD i a = a :=
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
        simp_rw [heq]
        exact measurable_const
    exact hf hs
  have hcomp : (fun v : Σ n, Fin n → α => (List.ofFn v.2).getD i a) ∘
      List.equivSigmaTuple = (fun l : List α => l.getD i a) := by
    funext l
    exact congrArg (fun l => l.getD i a) (List.ofFn_get l)
  rw [← hcomp]
  exact h.comp (comap_measurable List.equivSigmaTuple)

end TauCeti

end
