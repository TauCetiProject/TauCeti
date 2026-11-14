/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.PowersetCard

/-!
# Maps, coercions and enumerations of fixed-cardinality subsets

`Set.powersetCard.map_injective` shows that vertex embeddings induce injective maps on
fixed-cardinality subsets. `Set.powersetCard.map_refl` and `Set.powersetCard.map_map` show that
these induced maps respect identities and composition of embeddings.

`Set.powersetCard.coe_ofSingleton`, `Set.powersetCard.mem_ofSingleton`, and
`Set.powersetCard.map_ofSingleton` relate the singleton equivalence to finite sets and embeddings,
`Set.powersetCard.map_compl_equiv` commutes `map` along an equivalence with `compl`, and
`Set.powersetCard.le_card` and `Set.powersetCard.sub_add_eq_card` record the cardinality bound
witnessed by an `r`-element subset of a finite type.

`Set.powersetCard.finChooseEquiv m j` enumerates the `j`-element subsets of `Fin m` by
`Fin (m.choose j)`.
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

/-- Membership in `Set.powersetCard.ofSingleton a` is equality with `a`. -/
@[simp]
theorem mem_ofSingleton {α : Type*} {a b : α} : b ∈ ofSingleton a ↔ b = a :=
  Finset.mem_singleton

/-- Mapping a singleton subset along an embedding sends `ofSingleton a` to `ofSingleton (f a)`. -/
@[simp]
theorem map_ofSingleton {α β : Type*} (f : α ↪ β) (a : α) :
    map 1 f (ofSingleton a) = ofSingleton (f a) :=
  Subtype.ext (Finset.map_singleton f a)

/-- Mapping along an equivalence commutes with complementation of fixed-cardinality subsets. -/
@[simp]
theorem map_compl_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {m n : ℕ} (hm : m + n = Fintype.card α) (e : α ≃ β) (s : powersetCard α n) :
    map m e.toEmbedding (compl hm s) =
      compl (hm.trans (Fintype.card_congr e)) (map n e.toEmbedding s) := by
  refine eq_iff_subset.mpr fun b hb ↦ ?_
  obtain ⟨a, rfl⟩ := e.surjective b
  simpa using hb

/-- Every `r`-element subset of a finite type `α` satisfies `r ≤ Fintype.card α`. -/
theorem le_card {α : Type*} [Fintype α] {r : ℕ} (T : powersetCard α r) :
    r ≤ Fintype.card α :=
  nonempty_iff.mp ⟨T⟩

/-- The complementary cardinality `Fintype.card α - r` and `r` sum to `Fintype.card α`. -/
theorem sub_add_eq_card {α : Type*} [Fintype α] {r : ℕ} (T : powersetCard α r) :
    Fintype.card α - r + r = Fintype.card α :=
  Nat.sub_add_cancel (le_card T)

/-- Every `r`-element subset of `Fin m` satisfies `r ≤ m`. -/
theorem le_of_fin {m r : ℕ} (T : powersetCard (Fin m) r) : r ≤ m := by
  simpa using le_card T

/-- The complementary cardinality `m - r` and `r` sum to `Fintype.card (Fin m)`. -/
theorem sub_add_eq_card_fin {m r : ℕ} (T : powersetCard (Fin m) r) :
    m - r + r = Fintype.card (Fin m) := by
  simpa using sub_add_eq_card T

/-- An enumeration of the `j`-element subsets of `Fin m` by `Fin (m.choose j)`. -/
noncomputable def finChooseEquiv (m j : ℕ) : powersetCard (Fin m) j ≃ Fin (m.choose j) :=
  Fintype.equivFinOfCardEq <| by
    rw [← Nat.card_eq_fintype_card, powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]

end Set.powersetCard
