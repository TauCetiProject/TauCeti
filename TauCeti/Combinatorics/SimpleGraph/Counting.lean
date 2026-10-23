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
The cardinality bounds use `Nat.card` and need only `Finite` vertex types, without chosen
enumerations. The sum and labelled-copy-count formulas use `Fintype` as required by their
right-hand sides.

## Main results

* `SimpleGraph.card_hom_le` bounds homomorphisms by all vertex maps.
* `SimpleGraph.card_injective_hom_le` bounds injective homomorphisms by vertex embeddings.
* `SimpleGraph.card_injective_hom_eq_sum_map_le` counts injective homomorphisms by the vertex
  embeddings whose mapped graph lies below the target.
* `SimpleGraph.card_hom_eq_card_adjPreservingMaps` counts homomorphisms by the
  adjacency-preserving vertex maps.
* `SimpleGraph.card_injective_hom_eq_labelledCopyCount` identifies the number of injective
  homomorphisms with Mathlib's `SimpleGraph.labelledCopyCount`, so injective homomorphism counts
  and labelled copy counts are one counting convention, not two.
-/

public section

namespace SimpleGraph

variable {V W : Type*}

/-- Homomorphisms and adjacency-preserving vertex maps are counted alike. -/
theorem card_hom_eq_card_adjPreservingMaps (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) = Nat.card {ψ : V → W // ∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b)} :=
  Nat.card_congr
    { toFun := fun φ => ⟨⇑φ, fun _ _ h => φ.map_rel h⟩
      invFun := fun ψ => ⟨ψ.1, fun {_ _} h => ψ.2 _ _ h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section CardinalityBounds

variable [Finite V] [Finite W]

/-- The number of homomorphisms from `F` to `G` is bounded by the number of vertex maps. -/
theorem card_hom_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) ≤ Nat.card W ^ Nat.card V := by
  calc Nat.card (F →g G) ≤ Nat.card (V → W) :=
        Nat.card_le_card_of_injective (fun φ => (φ : V → W))
          (fun a b h => by ext x; exact congrFun h x)
    _ = Nat.card W ^ Nat.card V := Nat.card_fun

/-- The number of injective homomorphisms from `F` to `G` is bounded by the number of embeddings
of the vertex types. -/
theorem card_injective_hom_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ}
      ≤ (Nat.card W).descFactorial (Nat.card V) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite W
  calc Nat.card {φ : F →g G // Function.Injective φ} ≤ Nat.card (V ↪ W) :=
        Nat.card_le_card_of_injective (fun φ => ⟨(φ.1 : V → W), φ.2⟩)
          (fun a b h => by
            ext x; exact congrFun (congrArg (fun e : V ↪ W => (e : V → W)) h) x)
    _ = (Nat.card W).descFactorial (Nat.card V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
        simp only [Nat.card_eq_fintype_card]

end CardinalityBounds

variable [Fintype V] [Fintype W]

/-- The number of injective homomorphisms from `F` to `G` is Mathlib's labelled copy count.

`SimpleGraph.Copy F G` is definitionally an injective homomorphism, so this is an equivalence of
subtypes. Mathlib takes the host graph first: `G.labelledCopyCount F` counts copies of `F` inside
`G`.

Deliberately not `@[simp]`: the left-hand side is not in simp normal form, since `Nat.card` of a
`Fintype` rewrites to `Fintype.card`. -/
theorem card_injective_hom_eq_labelledCopyCount (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ} = G.labelledCopyCount F := by
  -- `labelledCopyCount` is defined by `classical exact Fintype.card (Copy H G)`, so unfolding it
  -- exposes a `Fintype (Copy F G)` that only `classical` provides.
  classical
  rw [labelledCopyCount, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun φ => ⟨φ.1, φ.2⟩
      invFun := fun c => ⟨c.toHom, c.injective'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open Classical in
/-- Injective graph homomorphisms are counted by the vertex embeddings whose mapped graph lies
below the host graph. -/
theorem card_injective_hom_eq_sum_map_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ} =
      ∑ f : V ↪ W, if F.map f ≤ G then 1 else 0 := by
  let e : {φ : F →g G // Function.Injective φ} ≃ {f : V ↪ W // F.map f ≤ G} :=
    { toFun := fun φ =>
        ⟨⟨φ.1, φ.2⟩, map_le_iff_le_comap.2 fun {_ _} hab => φ.1.map_rel hab⟩
      invFun := fun f =>
        ⟨⟨f.1, fun {_ _} hab => map_le_iff_le_comap.1 f.2 hab⟩, f.1.injective⟩
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
