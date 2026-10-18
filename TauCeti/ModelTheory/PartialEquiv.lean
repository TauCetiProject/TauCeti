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
@[expose] noncomputable def comp (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) :
    M ≃ₚ[L] P where
  dom := f.dom
  cod := (g.domRestrict h).cod
  toEquiv := (g.domRestrict h).toEquiv.comp f.toEquiv

/-- The composite has the domain of the first partial equivalence. -/
@[simp]
theorem dom_comp (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) :
    (g.comp f h).dom = f.dom := rfl

/-- The composite applies the first partial equivalence, then the second. -/
theorem comp_apply (g : N ≃ₚ[L] P) (f : M ≃ₚ[L] N) (h : f.cod ≤ g.dom) {x : M}
    (hx : x ∈ (g.comp f h).dom) :
    ((g.comp f h).toEquiv ⟨x, hx⟩ : P) = g.toEquiv ⟨f.toEquiv ⟨x, hx⟩, h (f.toEquiv _).2⟩ := rfl

/-- Composition of partial equivalences is monotone in both arguments. -/
theorem comp_le_comp {f f' : M ≃ₚ[L] N} {g g' : N ≃ₚ[L] P} (hf : f ≤ f') (hg : g ≤ g')
    (h : f.cod ≤ g.dom) (h' : f'.cod ≤ g'.dom) : g.comp f h ≤ g'.comp f' h' := by
  refine ⟨show f.dom ≤ f'.dom from dom_le_dom hf, ?_⟩
  ext ⟨x, hx⟩
  have hf' := congrArg Subtype.val (toEquiv_inclusion_apply hf ⟨x, hx⟩)
  have hg' := congrArg Subtype.val (toEquiv_inclusion_apply hg ⟨_, h (f.toEquiv ⟨x, hx⟩).2⟩)
  change (g'.toEquiv ⟨f'.toEquiv ⟨x, dom_le_dom hf hx⟩, _⟩ : P) = g.toEquiv ⟨f.toEquiv ⟨x, hx⟩, _⟩
  simp only [Substructure.coe_inclusion] at hf' hg'
  simp only [hf']
  exact hg'

end FirstOrder.Language.PartialEquiv
