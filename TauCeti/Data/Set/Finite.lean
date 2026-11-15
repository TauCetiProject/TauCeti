/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Set.Finite.Range

/-!
# Finite subsets of a set as finsets of the subtype

A finite set `s ⊆ S` is the image under `Subtype.val` of a finset of the subtype `↥S` with the same
number of elements (`Set.Finite.exists_finset_subtype_image_val_eq`). This is the reading of a
finite set of elements of a subgroup, a submodule or any other set-like structure as a `Finset` of
that structure, which is the form the generation and rank statements over a `Finset` of a subgroup
take.

A finite family of finite sets has its index-element pairs enumerated by some `Fin m`
(`Set.exists_enumeration_finite_family`), and a function on a finite type factors as an injective
enumeration of its values after a surjection (`TauCeti.exists_embedding_fin_comp_eq`).
A map from a finite type with the same range as an injective map is injective
(`Function.Injective.of_range_eq`).
-/

public section

namespace Set.Finite

variable {α : Type*} {S s : Set α}

/-- A finite set `s ⊆ S` is the image of a finset of the subtype `↥S` with `Nat.card s`
elements. -/
theorem exists_finset_subtype_image_val_eq (hs : s.Finite) (hsub : s ⊆ S) :
    ∃ t : Finset S, t.card = Nat.card s ∧ Subtype.val '' (t : Set S) = s := by
  lift s to Set S using hsub
  lift s to Finset S using Set.Finite.of_finite_image hs Subtype.val_injective.injOn
  exact ⟨s, by simp [Set.ncard_image_of_injective _ Subtype.val_injective], rfl⟩

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

/-- A map from a finite type with the same range as an injective map is injective. -/
theorem Function.Injective.of_range_eq {ι β : Type*} [Finite ι] {f g : ι → β}
    (hf : Function.Injective f) (h : Set.range f = Set.range g) : Function.Injective g := by
  have e : ι ≃ Set.range g :=
    (Equiv.ofInjective f hf).trans (Equiv.subtypeEquivRight fun x => by rw [h])
  exact Subtype.val_injective.comp
    ((Finite.injective_iff_surjective_of_equiv e).2 Set.rangeFactorization_surjective)

namespace TauCeti

/-- A function `h` from a finite type factors as an injective enumeration `b : Fin m ↪ γ` of its
values after a surjection `g` onto `Fin m`. -/
theorem exists_embedding_fin_comp_eq {δ γ : Type*} [Finite δ] (h : δ → γ) :
    ∃ (m : ℕ) (b : Fin m ↪ γ) (g : δ → Fin m), b ∘ g = h ∧ g.Surjective := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range h)
  exact ⟨m, e.symm.toEmbedding.trans (.subtype _), e ∘ Set.rangeFactorization h,
    by ext; simp, e.surjective.comp Set.rangeFactorization_surjective⟩

end TauCeti
