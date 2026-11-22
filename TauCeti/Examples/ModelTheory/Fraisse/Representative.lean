/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Fraisse.Representative
import Mathlib.ModelTheory.Graph

/-!
# Regression examples: isomorphism closures of representative families

In the language of graphs, with `K₁` the one-vertex graph and `K₂` the complete graph on two
vertices:

* the isomorphism closure of the empty family is empty;
* the family of two copies of `K₁` has the same closure as the family of one copy: duplicate
  representatives change nothing;
* `K₂` is not in that closure, since it has two vertices.
-/

open FirstOrder FirstOrder.Language CategoryTheory

-- The isomorphism closure of the empty family is empty.
example {L : Language} (F : Empty → Bundled L.Structure) : representativeClass F = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h =>
    let ⟨i, _⟩ := mem_representativeClass_iff.1 h
    i.elim

-- Two copies of `K₁` generate the same class as one copy.
example :
    let K₁ : Bundled Language.graph.Structure :=
      @Bundled.of _ (Fin 1) (⊥ : SimpleGraph (Fin 1)).structure
    representativeClass (fun _ : Fin 2 => K₁) = representativeClass (fun _ : Unit => K₁) := by
  intro K₁
  ext M
  simp only [mem_representativeClass_iff]
  exact ⟨fun ⟨_, h⟩ => ⟨(), h⟩, fun ⟨_, h⟩ => ⟨0, h⟩⟩

-- `K₂` is not in the closure of `K₁`: an isomorphism would biject two vertices with one.
example :
    let K₁ : Bundled Language.graph.Structure :=
      @Bundled.of _ (Fin 1) (⊥ : SimpleGraph (Fin 1)).structure
    let K₂ : Bundled Language.graph.Structure :=
      @Bundled.of _ (Fin 2) (⊤ : SimpleGraph (Fin 2)).structure
    K₂ ∉ representativeClass (fun _ : Fin 2 => K₁) := by
  intro K₁ K₂ h
  obtain ⟨_, ⟨e⟩⟩ := mem_representativeClass_iff.1 h
  have := Fintype.card_congr (α := Fin 2) (β := Fin 1) e.toEquiv
  simp at this
