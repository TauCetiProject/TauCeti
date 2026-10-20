/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.PartialEquiv

/-!
# Composition of partial equivalences

Partial equivalences `f : M ≃ₚ[L] N` and `g : N ≃ₚ[L] P` compose when the codomain of `f` lies in
the domain of `g`. The composite has the domain of `f`, applies `f`, then `g`, and has as codomain
the image under `g` of the codomain of `f`. It is monotone in both partial equivalences.

## Main definitions

* `FirstOrder.Language.PartialEquiv.comp`: the composite of compatible partial equivalences.

## Main results

* `FirstOrder.Language.PartialEquiv.toEquiv_apply_of_le`: a larger partial equivalence agrees
  with a smaller one on the smaller domain.
* `FirstOrder.Language.PartialEquiv.mem_cod_comp`: the codomain of a composite.
* `FirstOrder.Language.PartialEquiv.comp_le_comp`: composition is monotone in both arguments.
* `FirstOrder.Language.FGEquiv.exists_le_and_le_dom_of_fg`: in a family of finitely generated
  partial equivalences closed under forth extensions, every member extends to cover any finitely
  generated substructure.
-/

public section

universe u v w w' w''

namespace FirstOrder.Language.PartialEquiv

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
variable [L.Structure M] [L.Structure N] [L.Structure P]

/-- A larger partial equivalence takes the same values on the domain of a smaller one. -/
theorem toEquiv_apply_of_le {f g : M ≃ₚ[L] N} (h : f ≤ g) {x : M} (hx : x ∈ f.dom) :
    (g.toEquiv ⟨x, dom_le_dom h hx⟩ : N) = f.toEquiv ⟨x, hx⟩ :=
  congrArg Subtype.val (toEquiv_inclusion_apply h ⟨x, hx⟩)

/-- The composite of partial equivalences `f : M ≃ₚ[L] N` and `g : N ≃ₚ[L] P` when the codomain
of `f` lies in the domain of `g`. It has the domain of `f`. -/
noncomputable def comp (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) : M ≃ₚ[L] P where
  dom := f.dom
  cod := (g.domRestrict h).cod
  toEquiv := (g.domRestrict h).toEquiv.comp f.toEquiv

/-- The composite has the domain of the first partial equivalence. -/
@[simp]
theorem dom_comp (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) :
    (g.comp f h).dom = f.dom := (rfl)

/-- The composite applies the first partial equivalence, then the second. -/
@[simp]
theorem comp_apply (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) (x : (g.comp f h).dom) :
    ((g.comp f h).toEquiv x : P) =
      g.toEquiv
        (Substructure.inclusion h (f.toEquiv (Substructure.inclusion (dom_comp g f h).le x))) :=
  (rfl)

/-- The codomain of the composite is the image under the second partial equivalence of the
codomain of the first. -/
@[simp]
theorem mem_cod_comp (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) {p : P} :
    p ∈ (g.comp f h).cod ↔ ∃ y : f.cod, (g.toEquiv (Substructure.inclusion h y) : P) = p :=
  Iff.rfl

/-- The codomain of the composite lies in the codomain of the second partial equivalence. -/
theorem cod_comp_le (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) :
    (g.comp f h).cod ≤ g.cod := by
  intro p hp
  obtain ⟨y, rfl⟩ := (mem_cod_comp g f h).1 hp
  exact (g.toEquiv _).2

/-- When the codomain of the first partial equivalence is the domain of the second, the composite
has the codomain of the second. -/
theorem cod_comp_of_eq (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) (he : f.cod = g.dom) :
    (g.comp f h).cod = g.cod := by
  refine le_antisymm (cod_comp_le g f h) fun p hp => (mem_cod_comp g f h).2 ?_
  let z := g.toEquiv.symm ⟨p, hp⟩
  exact ⟨⟨z, he.ge z.2⟩, by simp [z, Substructure.inclusion]⟩

/-- Composition of partial equivalences is monotone in both arguments. -/
theorem comp_le_comp {f f' : M ≃ₚ[L] N} {g g' : N ≃ₚ[L] P} (hf : f ≤ f') (hg : g ≤ g')
    (h : f.cod ≤ g.dom) (h' : f'.cod ≤ g'.dom) : g.comp f h ≤ g'.comp f' h' := by
  have hdom : (g.comp f h).dom ≤ (g'.comp f' h').dom := by
    rw [dom_comp, dom_comp]
    exact dom_le_dom hf
  refine (le_def _ _).2 ⟨hdom, ?_⟩
  ext ⟨x, hx⟩
  have hx' : x ∈ f.dom := (dom_comp g f h).le hx
  have hf' := toEquiv_apply_of_le hf hx'
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Substructure.coe_subtype, comp_apply]
  -- Both sides apply `g'` and `g` to the same value of `f`.
  refine (congrArg (fun y : g'.dom => (g'.toEquiv y : P)) (Subtype.ext ?_)).trans
    (toEquiv_apply_of_le hg (h (f.toEquiv ⟨x, hx'⟩).2))
  simpa using hf'

end FirstOrder.Language.PartialEquiv

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

open PartialEquiv

/-- In a family of finitely generated partial equivalences closed under forth extensions, every
member extends within the family to one whose domain contains a given finitely generated
substructure. -/
theorem FGEquiv.exists_le_and_le_dom_of_fg {T : Set (L.FGEquiv M N)}
    (hT : ∀ g ∈ T, ∀ m : M, ∃ g' ∈ T, m ∈ g'.1.dom ∧ g ≤ g') {g : L.FGEquiv M N} (hg : g ∈ T)
    {A : L.Substructure M} (hA : A.FG) : ∃ g' ∈ T, A ≤ g'.1.dom ∧ g ≤ g' := by
  classical
  obtain ⟨s, rfl⟩ := hA
  -- Extend one generator at a time.
  suffices ∃ g' ∈ T, (s : Set M) ⊆ g'.1.dom ∧ g ≤ g' from
    let ⟨g', hg', hs, hgg'⟩ := this; ⟨g', hg', Substructure.closure_le.2 hs, hgg'⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, by simp, le_rfl⟩
  | insert a s _ ih =>
    obtain ⟨g₁, hg₁, hs, hgg₁⟩ := ih
    obtain ⟨g₂, hg₂, ha, hg₁g₂⟩ := hT g₁ hg₁ a
    refine ⟨g₂, hg₂, ?_, hgg₁.trans hg₁g₂⟩
    rw [Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨ha, hs.trans (dom_le_dom hg₁g₂)⟩

end FirstOrder.Language
