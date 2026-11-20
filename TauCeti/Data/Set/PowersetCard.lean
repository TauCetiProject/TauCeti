/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Maps, coercions and enumerations of fixed-cardinality subsets

`Set.powersetCard.map_injective` shows that embeddings induce injective maps on
fixed-cardinality subsets. `Set.powersetCard.map_refl` and `Set.powersetCard.map_map` show that
these induced maps respect identities and composition of embeddings.

`Set.powersetCard.coe_ofSingleton` identifies the finite set underlying the singleton
equivalence. It lets computations with fixed-cardinality subsets use the usual singleton API.

`Set.powersetCard.finChooseEquiv m j` enumerates the `j`-element subsets of `Fin m` by
`Fin (m.choose j)`.

When the source is `Fin r`, the embeddings `Fin r ↪ β` whose unordered image
`Set.powersetCard.ofFinEmb r β` equals a prescribed `r`-element subset `t` correspond to the
embeddings `Fin r ↪ t.val` (`Set.powersetCard.ofFinEmbFiberEquiv`), so there are `r!` of them
without any finiteness assumption on `β` (`Set.powersetCard.natCard_ofFinEmb_eq`). Precomposing an
embedding or injective `r`-tuple by a permutation of `Fin r` leaves its unordered image unchanged
(`Set.powersetCard.ofFinEmb_trans_perm`, `Set.powersetCard.ofFinEmb_comp_perm`), and two embeddings
`Fin r ↪ β` have the same unordered image precisely when they differ by a permutation of `Fin r`
(`Set.powersetCard.ofFinEmb_eq_iff_exists_perm`).
-/

public section

namespace Set.powersetCard

/-- An embedding induces an injective map on fixed-cardinality subsets. -/
theorem map_injective {α β : Type*} (n : ℕ) (f : α ↪ β) :
    Function.Injective (map n f) := fun s t h ↦
  Subtype.ext <| Finset.map_injective f <| by simpa only [val_map] using congrArg Subtype.val h

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

/-- An enumeration of the `j`-element subsets of `Fin m` by `Fin (m.choose j)`. -/
noncomputable def finChooseEquiv (m j : ℕ) : powersetCard (Fin m) j ≃ Fin (m.choose j) :=
  Fintype.equivFinOfCardEq <| by
    rw [← Nat.card_eq_fintype_card, powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]

variable {β : Type*} {r : ℕ}

/-- The embeddings `Fin r ↪ β` with unordered image `t` correspond to the embeddings of `Fin r`
into `t`. -/
def ofFinEmbFiberEquiv (t : Set.powersetCard β r) :
    {f : Fin r ↪ β // ofFinEmb r β f = t} ≃ (Fin r ↪ t.val) where
  toFun f :=
    ⟨fun i ↦ ⟨f.1 i, by rcases f with ⟨f, rfl⟩; simp⟩,
      fun _ _ h ↦ f.1.injective (congrArg Subtype.val h)⟩
  invFun g :=
    ⟨g.trans (Function.Embedding.subtype _), eq_iff_subset.2 fun b hb ↦ by
      obtain ⟨i, rfl⟩ := (mem_ofFinEmb_iff_mem_range r β _ b).1 (mem_coe_iff.1 hb)
      exact (g i).2⟩
  left_inv _ := Subtype.ext (Function.Embedding.ext fun _ ↦ rfl)
  right_inv _ := Function.Embedding.ext fun _ ↦ Subtype.ext rfl

/-- The embedding `ofFinEmbFiberEquiv t f` takes the same values as `f`. -/
@[simp]
theorem ofFinEmbFiberEquiv_apply_coe (t : Set.powersetCard β r)
    (f : {f : Fin r ↪ β // ofFinEmb r β f = t}) (i : Fin r) :
    (ofFinEmbFiberEquiv t f i : β) = f.1 i :=
  (rfl)

/-- The embedding `(ofFinEmbFiberEquiv t).symm g` takes the same values as `g`. -/
@[simp]
theorem ofFinEmbFiberEquiv_symm_apply_coe (t : Set.powersetCard β r)
    (g : Fin r ↪ t.val) (i : Fin r) :
    ((ofFinEmbFiberEquiv t).symm g).1 i = (g i : β) :=
  (rfl)

/-- Exactly `r!` embeddings `Fin r ↪ β` have a prescribed `r`-element subset `t` as unordered
image. -/
theorem natCard_ofFinEmb_eq (t : Set.powersetCard β r) :
    Nat.card {f : Fin r ↪ β // ofFinEmb r β f = t} = r.factorial := by
  rw [Nat.card_congr (ofFinEmbFiberEquiv t), Nat.card_eq_fintype_card]
  simp [Fintype.card_embedding_eq, Nat.descFactorial_self]

/-- Precomposing an embedding `Fin r ↪ β` with a permutation of `Fin r` leaves its unordered
image unchanged. -/
@[simp]
theorem ofFinEmb_trans_perm (σ : Equiv.Perm (Fin r)) (f : Fin r ↪ β) :
    ofFinEmb r β (σ.toEmbedding.trans f) = ofFinEmb r β f :=
  SetLike.coe_injective <| by
    simp only [coe_ofFinEmb, Function.Embedding.coe_trans, Equiv.coe_toEmbedding]
    exact σ.surjective.range_comp f

/-- Precomposing an injective `r`-tuple with a permutation of `Fin r` leaves its unordered
image unchanged. -/
@[simp]
theorem ofFinEmb_comp_perm (σ : Equiv.Perm (Fin r)) (x : Fin r → β)
    (h : Function.Injective (x ∘ σ)) :
    ofFinEmb r β ⟨x ∘ σ, h⟩ = ofFinEmb r β ⟨x, (σ.injective_comp x).1 h⟩ := by
  have htr : (⟨x ∘ σ, h⟩ : Fin r ↪ β) = σ.toEmbedding.trans ⟨x, (σ.injective_comp x).1 h⟩ :=
    Function.Embedding.ext fun _ ↦ rfl
  rw [htr, ofFinEmb_trans_perm]

/-- Two embeddings `Fin r ↪ β` have the same unordered image if and only if they differ by a
permutation of `Fin r`. -/
theorem ofFinEmb_eq_iff_exists_perm (f g : Fin r ↪ β) :
    ofFinEmb r β f = ofFinEmb r β g ↔ ∃ σ : Equiv.Perm (Fin r), ⇑f = ⇑g ∘ σ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hfg : Set.range f = Set.range g := by rw [← coe_ofFinEmb, h, coe_ofFinEmb]
    -- `σ i` is the unique preimage under `g` of `f i`, which lies in `Set.range g`.
    refine ⟨(Equiv.ofInjective f f.injective).trans <| (Set.equivOfEq hfg).trans
      (Equiv.ofInjective g g.injective).symm, funext fun i ↦ ?_⟩
    simp only [Equiv.coe_trans, Function.comp_apply, Equiv.ofInjective_apply,
      Set.equivOfEq_apply, Equiv.apply_ofInjective_symm]
  · rintro ⟨σ, hfg⟩
    have htr : f = σ.toEmbedding.trans g := Function.Embedding.ext (congrFun hfg)
    rw [htr, ofFinEmb_trans_perm]

end Set.powersetCard
