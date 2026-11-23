/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Restricting maps over a base to preimages

For continuous maps `p : E → B` and `q : E' → B`, a map `f : E → E'` over `B` (`q ∘ f = p`) carries
the preimage `p⁻¹(S)` of a subset `S` of `B` into `q⁻¹(S)`. This file records the restriction
`TauCeti.restrictPreimageMap S hf : C(p ⁻¹' S, q ⁻¹' S)` and its functoriality.
-/

public section

universe u u' u'' v

namespace TauCeti

variable {E : Type u} {E' : Type u'} {E'' : Type u''} {B : Type v} [TopologicalSpace E]
  [TopologicalSpace E'] [TopologicalSpace E''] [TopologicalSpace B]

/-- A map `f` over `B` restricts to a map between the preimages of a subset `S` of `B`. -/
def restrictPreimageMap {p : C(E, B)} {q : C(E', B)} (S : Set B) {f : C(E, E')}
    (hf : q.comp f = p) : C(p ⁻¹' S, q ⁻¹' S) :=
  ⟨fun e : p ⁻¹' S ↦ ⟨f e.val, by
    rw [Set.mem_preimage, ← ContinuousMap.comp_apply, hf]
    exact e.property⟩, by fun_prop⟩

@[simp]
theorem coe_restrictPreimageMap {p : C(E, B)} {q : C(E', B)} (S : Set B) {f : C(E, E')}
    (hf : q.comp f = p) (e : p ⁻¹' S) : (restrictPreimageMap S hf e : E') = f e :=
  (rfl)

@[simp]
theorem restrictPreimageMap_comp {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)} (S : Set B)
    {f : C(E, E')} {g : C(E', E'')} (hf : q.comp f = p) (hg : r.comp g = q) :
    (restrictPreimageMap S hg).comp (restrictPreimageMap S hf) =
      restrictPreimageMap (f := g.comp f) S (by rw [← ContinuousMap.comp_assoc, hg, hf]) :=
  (rfl)

@[simp]
theorem restrictPreimageMap_id {p : C(E, B)} (S : Set B) :
    restrictPreimageMap (f := .id E) S (ContinuousMap.comp_id p) = .id _ :=
  (rfl)

end TauCeti
