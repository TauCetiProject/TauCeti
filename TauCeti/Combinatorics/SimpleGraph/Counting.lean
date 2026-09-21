/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Counting graph homomorphisms

Cardinality bounds for homomorphisms and injective homomorphisms between finite simple graphs.
These compare graph homomorphism counts with all vertex maps and embeddings, enabling the
normalization and estimates used for finite homomorphism densities.

## Main results

* `SimpleGraph.card_hom_le` bounds homomorphisms by all vertex maps.
* `SimpleGraph.card_injective_hom_le` bounds injective homomorphisms by vertex embeddings.
* `SimpleGraph.card_injective_hom_eq_sum_map_le` counts injective homomorphisms by the vertex
  embeddings whose mapped graph lies below the target.
-/

public section

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The number of homomorphisms from `F` to `G` is bounded by the number of vertex maps. -/
theorem card_hom_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) ≤ Fintype.card W ^ Fintype.card V := by
  classical
  calc Nat.card (F →g G) ≤ Nat.card (V → W) :=
        Nat.card_le_card_of_injective (fun φ => (φ : V → W))
          (fun a b h => by ext x; exact congrFun h x)
    _ = Fintype.card W ^ Fintype.card V := by rw [Nat.card_eq_fintype_card, Fintype.card_fun]

/-- The number of injective homomorphisms from `F` to `G` is bounded by the number of embeddings
of the vertex types. -/
theorem card_injective_hom_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ}
      ≤ (Fintype.card W).descFactorial (Fintype.card V) := by
  classical
  calc Nat.card {φ : F →g G // Function.Injective φ} ≤ Nat.card (V ↪ W) :=
        Nat.card_le_card_of_injective (fun φ => ⟨(φ.1 : V → W), φ.2⟩)
          (fun a b h => by
            ext x; exact congrFun (congrArg (fun e : V ↪ W => (e : V → W)) h) x)
    _ = (Fintype.card W).descFactorial (Fintype.card V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]

open Classical in
/-- Injective graph homomorphisms are counted by the vertex embeddings whose mapped graph lies
below the host graph. -/
theorem card_injective_hom_eq_sum_map_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ} =
      ∑ f : V ↪ W, if F.map f ≤ G then 1 else 0 := by
  let e : {φ : F →g G // Function.Injective φ} ≃ {f : V ↪ W // F.map f ≤ G} :=
    { toFun := fun φ =>
        ⟨⟨φ.1, φ.2⟩, (map_le_iff_le_comap _ _ _).2 fun {_ _} hab => φ.1.map_rel hab⟩
      invFun := fun f =>
        ⟨⟨f.1, fun {_ _} hab => (map_le_iff_le_comap _ _ _).1 f.2 hab⟩, f.1.injective⟩
      left_inv := by
        intro φ
        apply Subtype.ext
        exact RelHom.ext fun _ => rfl
      right_inv := by
        intro f
        apply Subtype.ext
        exact DFunLike.ext _ _ fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

end SimpleGraph
