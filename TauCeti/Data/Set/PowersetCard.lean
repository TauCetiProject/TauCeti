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

`Set.powersetCard.coe_ofSingleton` identifies the finite set underlying the singleton
equivalence. It lets computations with fixed-cardinality subsets use the usual singleton API.
For `p + 1 = Fintype.card α`, `Set.powersetCard.omitOne` is the equivalence sending `a : α` to the
`p`-element subset `Finset.univ.erase a` omitting `a`.

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

section OmitOne

variable {α : Type*} [DecidableEq α] [Fintype α] {p : ℕ}

/-- The equivalence sending `a : α` to the `p`-element subset `Finset.univ.erase a` omitting `a`,
where `p + 1 = Fintype.card α`. -/
noncomputable def omitOne (hm : p + 1 = Fintype.card α) : α ≃ powersetCard α p :=
  ofSingleton.trans (compl hm)

/-- `omitOne hm a` is the complement of the singleton `{a}`. -/
theorem omitOne_apply (hm : p + 1 = Fintype.card α) (a : α) :
    omitOne hm a = compl hm (ofSingleton a) :=
  (rfl)

/-- The finite set underlying `omitOne hm a` is `Finset.univ.erase a`. -/
@[simp]
theorem coe_omitOne (hm : p + 1 = Fintype.card α) (a : α) :
    ((omitOne hm a : powersetCard α p) : Finset α) = Finset.univ.erase a := by
  ext b
  simp [omitOne_apply, Finset.mem_erase]

/-- An element belongs to `omitOne hm a` precisely when it differs from `a`. -/
@[simp]
theorem mem_omitOne {hm : p + 1 = Fintype.card α} {a b : α} :
    b ∈ omitOne hm a ↔ b ≠ a := by
  rw [← mem_coe_iff, coe_omitOne, Finset.mem_erase]
  simp

/-- Taking the complement of `omitOne hm a` recovers the singleton `{a}`. -/
@[simp]
theorem compl_omitOne (hm : p + 1 = Fintype.card α) (a : α) :
    compl ((Nat.add_comm 1 p).trans hm) (omitOne hm a) = ofSingleton a := by
  rw [omitOne_apply, ← compl_symm (hm := hm), Equiv.symm_apply_apply]

end OmitOne

/-- An enumeration of the `j`-element subsets of `Fin m` by `Fin (m.choose j)`. -/
noncomputable def finChooseEquiv (m j : ℕ) : powersetCard (Fin m) j ≃ Fin (m.choose j) :=
  Fintype.equivFinOfCardEq <| by
    rw [← Nat.card_eq_fintype_card, powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]

end Set.powersetCard
