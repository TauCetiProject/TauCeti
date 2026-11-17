/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Set.PowersetCard

import TauCeti.Algebra.BigOperators.Finset.Powerset

/-!
# Maps, coercions and enumerations of fixed-cardinality subsets

`Set.powersetCard.map_injective` shows that vertex embeddings induce injective maps on
fixed-cardinality subsets. `Set.powersetCard.map_refl` and `Set.powersetCard.map_map` show that
these induced maps respect identities and composition of embeddings.

`Set.powersetCard.coe_ofSingleton` identifies the finite set underlying the singleton
equivalence. It lets computations with fixed-cardinality subsets use the usual singleton API.

`Set.powersetCard.fintypeCard` counts the `n`-element subsets of a finite type, and
`Set.powersetCard.finChooseEquiv m j` enumerates the `j`-element subsets of `Fin m` by
`Fin (m.choose j)`.

`Set.powersetCard.prod_prod` and `Set.powersetCard.sum_sum` count over the `n`-element subsets of
a finite type: each element lies in `(card α - 1).choose (n - 1)` of them.
-/

public section

namespace Set.powersetCard

/-- An embedding induces an injective map on fixed-cardinality subsets. -/
theorem map_injective {α β : Type*} (n : ℕ) (f : α ↪ β) :
    Function.Injective (map n f) := by
  intro s t h
  apply Subtype.ext
  simpa only [val_map, Finset.map_inj] using congrArg Subtype.val h

/-- The identity embedding induces the identity map on fixed-cardinality subsets. -/
@[simp]
theorem map_refl {α : Type*} (n : ℕ) : map n (Function.Embedding.refl α) = id :=
  funext fun s ↦ Subtype.ext <| by rw [val_map, Finset.map_refl, id_eq]

/-- Mapping fixed-cardinality subsets along two embeddings in turn is mapping along their
composite. -/
@[simp]
theorem map_map {α β γ : Type*} (n : ℕ) (f : α ↪ β) (g : β ↪ γ) (s : powersetCard α n) :
    map n g (map n f s) = map n (f.trans g) s :=
  Subtype.ext <| by simp only [val_map, Finset.map_map]

/-- The finite set underlying the singleton equivalence is the singleton itself. -/
@[simp]
theorem coe_ofSingleton {α : Type*} (a : α) :
    ((ofSingleton a : powersetCard α 1) : Finset α) = {a} := rfl

/-- The number of `n`-element subsets of a finite type `α` is `(card α).choose n`. -/
theorem fintypeCard {α : Type*} [Fintype α] (n : ℕ) :
    Fintype.card (powersetCard α n) = (Fintype.card α).choose n := by
  rw [← Nat.card_eq_fintype_card, powersetCard.card, Nat.card_eq_fintype_card]

/-- An enumeration of the `j`-element subsets of `Fin m` by `Fin (m.choose j)`. -/
noncomputable def finChooseEquiv (m j : ℕ) : powersetCard (Fin m) j ≃ Fin (m.choose j) :=
  Fintype.equivFinOfCardEq <| by rw [fintypeCard, Fintype.card_fin]

/-- **Double counting over the `n`-element subsets of a finite type**: for `0 < n`, the product
over the `n`-element subsets of the products over their elements is
`(∏ i, f i) ^ (card α - 1).choose (n - 1)`. -/
@[to_additive /-- **Double counting over the `n`-element subsets of a finite type**: for `0 < n`,
the sum over the `n`-element subsets of the sums over their elements is
`(card α - 1).choose (n - 1) • ∑ i, f i`. -/]
theorem prod_prod {α β : Type*} [CommMonoid β] [Fintype α] {n : ℕ} (hn : 0 < n) (f : α → β) :
    ∏ t : powersetCard α n, ∏ i ∈ (t : Finset α), f i =
      (∏ i, f i) ^ (Fintype.card α - 1).choose (n - 1) := by
  rw [← Finset.card_univ, ← Finset.prod_powersetCard_prod hn]
  exact (Finset.prod_subtype (Finset.univ.powersetCard n)
    (fun _ ↦ Finset.mem_powersetCard_univ.trans mem_iff.symm) fun t ↦ ∏ i ∈ t, f i).symm

end Set.powersetCard
