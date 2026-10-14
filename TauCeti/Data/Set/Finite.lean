/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finite.Sigma

/-!
# Finite subsets of a set as finsets of the subtype

A finite set `s ⊆ S` is the image under `Subtype.val` of a finset of the subtype `↥S` with the same
number of elements (`Set.Finite.exists_finset_subtype_image_val_eq`). This is the reading of a
finite set of elements of a subgroup, a submodule or any other set-like structure as a `Finset` of
that structure, which is the form the generation and rank statements over a `Finset` of a subgroup
take.
-/

public section

namespace Set.Finite

variable {α : Type*} {S s : Set α}

/-- A finite set `s ⊆ S` is the image of a finset of the subtype `↥S` with `Nat.card s`
elements. -/
theorem exists_finset_subtype_image_val_eq (hs : s.Finite) (hsub : s ⊆ S) :
    ∃ t : Finset S, t.card = Nat.card s ∧ Subtype.val '' (t : Set S) = s := by
  classical
  have hpre : (Subtype.val ⁻¹' s : Set S).Finite := hs.preimage Subtype.val_injective.injOn
  refine ⟨hpre.toFinset, ?_, ?_⟩
  · rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset, hpre.coe_toFinset,
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (by rwa [Subtype.range_coe])]
  · rw [hpre.coe_toFinset, Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]

end Set.Finite

/-- A finite family of finite sets admits an enumeration of its index-element pairs. -/
theorem Set.exists_enumeration_finite_family {ι A : Type*} [Finite ι] (T : ι → Set A)
    (hTfin : ∀ i, (T i).Finite) :
    ∃ (m : ℕ) (idx : Fin m → ι) (t : Fin m → A), (∀ j, t j ∈ T (idx j)) ∧
      ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a := by
  have : ∀ i, Finite (T i) := fun i ↦ (hTfin i).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ((i : ι) × T i)
  exact ⟨m, fun j ↦ (e.symm j).1, fun j ↦ (e.symm j).2, fun j ↦ (e.symm j).2.2,
    fun i a ha ↦ ⟨e ⟨i, a, ha⟩, by simp,
      congrArg (fun x : (i : ι) × T i ↦ (x.2 : A)) (e.symm_apply_apply _)⟩⟩
