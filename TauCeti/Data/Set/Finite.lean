/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Basic.Finite.Sigma
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Set.Finite.Lattice
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

If only finitely many points of a set have values of `f` below some cutoff, then `f` is bounded
below on that set (`Set.Finite.bddBelow_image_of_setOf_lt`). If this holds for every cutoff and
for two functions `f` and `g`, it also holds for `f x + g y` on pairs
(`Set.Finite.setOf_and_add_lt`).
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

variable {β γ : Type*}

/-- If only finitely many points `x` with `p x` have `f x` below a cutoff `C`, then `f` is bounded
below on these points. -/
theorem bddBelow_image_of_setOf_lt [LinearOrder γ] {p : α → Prop} {f : α → γ} {C : γ}
    (hf : {x | p x ∧ f x < C}.Finite) : BddBelow (f '' {x | p x}) := by
  have : Nonempty γ := ⟨C⟩
  obtain ⟨m, hm⟩ := (hf.image f).bddBelow
  refine ⟨min m C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases lt_or_ge (f x) C with hC | hC
  · exact (min_le_left _ _).trans (hm ⟨x, ⟨hx, hC⟩, rfl⟩)
  · exact (min_le_right _ _).trans hC

/-- If `f` and `g` have only finitely many values below each cutoff on the points satisfying `p`
and `q`, then so does `f x + g y` on the pairs `(x, y)` satisfying both. -/
theorem setOf_and_add_lt [AddCommGroup γ] [LinearOrder γ] [IsOrderedAddMonoid γ] {p : α → Prop}
    {q : β → Prop} {f : α → γ} {g : β → γ} (hf : ∀ C, {x | p x ∧ f x < C}.Finite)
    (hg : ∀ C, {y | q y ∧ g y < C}.Finite) (C : γ) :
    {z : α × β | (p z.1 ∧ q z.2) ∧ f z.1 + g z.2 < C}.Finite := by
  obtain ⟨m, hm⟩ := bddBelow_image_of_setOf_lt (hf 0)
  obtain ⟨m', hm'⟩ := bddBelow_image_of_setOf_lt (hg 0)
  refine ((hf (C - m')).prod (hg (C - m))).subset fun z ⟨⟨hp, hq⟩, hC⟩ => ?_
  have h₁ : m ≤ f z.1 := hm ⟨z.1, hp, rfl⟩
  have h₂ : m' ≤ g z.2 := hm' ⟨z.2, hq, rfl⟩
  exact ⟨⟨hp, lt_sub_iff_add_lt.2 ((add_le_add le_rfl h₂).trans_lt hC)⟩,
    ⟨hq, lt_sub_iff_add_lt'.2 ((add_le_add h₁ le_rfl).trans_lt hC)⟩⟩

end Set.Finite

/-- A finite family of finite sets admits an enumeration of its index-element pairs. -/
theorem Set.exists_enumeration_finite_family {ι A : Type*} [Finite ι] (T : ι → Set A)
    (hTfin : ∀ i, (T i).Finite) :
    ∃ (m : ℕ) (idx : Fin m → ι) (t : Fin m → A), (∀ j, t j ∈ T (idx j)) ∧
      ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a := by
  have : ∀ i, Finite (T i) := fun i ↦ (hTfin i).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ((i : ι) × T i)
  exact ⟨m, fun j ↦ (e.symm j).1, fun j ↦ (e.symm j).2, fun j ↦ (e.symm j).2.property,
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
