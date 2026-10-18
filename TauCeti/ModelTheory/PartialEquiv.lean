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
the domain of `g`. The composite has the domain of `f` and applies `f`, then `g`; it is monotone
in both partial equivalences.

## Main definitions

* `FirstOrder.Language.PartialEquiv.comp`: the composite of compatible partial equivalences.

## Main results

* `FirstOrder.Language.PartialEquiv.comp_le_comp`: composition is monotone in both arguments.
-/

public section

universe u v w w' w''

namespace FirstOrder.Language.PartialEquiv

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
variable [L.Structure M] [L.Structure N] [L.Structure P]

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
theorem comp_apply (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) {x : M}
    (hx : x ∈ f.dom) :
    ((g.comp f h).toEquiv ⟨x, (dom_comp g f h).ge hx⟩ : P) =
      g.toEquiv ⟨f.toEquiv ⟨x, hx⟩, h (f.toEquiv ⟨x, hx⟩).2⟩ := (rfl)

/-- Composition of partial equivalences is monotone in both arguments. -/
theorem comp_le_comp {f f' : M ≃ₚ[L] N} {g g' : N ≃ₚ[L] P} (hf : f ≤ f') (hg : g ≤ g')
    (h : f.cod ≤ g.dom) (h' : f'.cod ≤ g'.dom) : g.comp f h ≤ g'.comp f' h' := by
  have hdom : (g.comp f h).dom ≤ (g'.comp f' h').dom := by
    rw [dom_comp, dom_comp]
    exact dom_le_dom hf
  refine (le_def _ _).2 ⟨hdom, ?_⟩
  ext ⟨x, hx⟩
  rw [dom_comp] at hx
  have hf' := congrArg Subtype.val (toEquiv_inclusion_apply hf ⟨x, hx⟩)
  have hg' := congrArg Subtype.val (toEquiv_inclusion_apply hg ⟨_, h (f.toEquiv ⟨x, hx⟩).2⟩)
  simp only [Substructure.coe_inclusion] at hf' hg'
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Substructure.coe_subtype,
    Substructure.coe_inclusion, comp_apply _ _ _ hx,
    comp_apply _ _ _ (dom_le_dom hf hx), hf']
  exact hg'

end FirstOrder.Language.PartialEquiv
