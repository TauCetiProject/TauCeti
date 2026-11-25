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
  representatives change nothing (`representativeClass_comp`);
* `K₂` is not in that closure, since it has two vertices.

The two membership simp rules are exercised too: `simp` puts each representative in its closure, and
unfolds membership in the closure to an isomorphism with some representative.
-/

open FirstOrder FirstOrder.Language CategoryTheory

-- The isomorphism closure of the empty family is empty.
example {L : Language} (F : Empty → Bundled L.Structure) : representativeClass F = ∅ :=
  representativeClass_eq_empty_iff.2 inferInstance

-- Two copies of `K₁` generate the same class as one copy, by surjective reindexing.
example :
    let K₁ : Bundled Language.graph.Structure :=
      @Bundled.of _ (Fin 1) (⊥ : SimpleGraph (Fin 1)).structure
    representativeClass (fun _ : Fin 2 => K₁) = representativeClass (fun _ : Unit => K₁) :=
  representativeClass_comp (F := fun _ : Unit => _) (g := fun _ : Fin 2 => ()) fun _ => ⟨0, rfl⟩

-- Each representative is in the closure, by `simp`.
example {L : Language} (F : Fin 2 → Bundled L.Structure) : F 1 ∈ representativeClass F := by
  simp

-- `K₂` is not in the closure of `K₁`: an isomorphism would biject two vertices with one.
example :
    let K₁ : Bundled Language.graph.Structure :=
      @Bundled.of _ (Fin 1) (⊥ : SimpleGraph (Fin 1)).structure
    let K₂ : Bundled Language.graph.Structure :=
      @Bundled.of _ (Fin 2) (⊤ : SimpleGraph (Fin 2)).structure
    K₂ ∉ representativeClass (fun _ : Fin 2 => K₁) := by
  intro K₁ K₂
  simp only [mem_representativeClass_iff, not_exists, not_nonempty_iff]
  exact fun _ => ⟨fun e => by
    simpa using Fintype.card_congr (α := Fin 2) (β := Fin 1) e.toEquiv⟩
