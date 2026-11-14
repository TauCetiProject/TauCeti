/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Fintype.EquivFin

/-!
# Embeddings with a prescribed image of a finite subset

Fix two subsets of cardinality `r` in finite types. There are at most
`r! * |β|^(|α| - r)` embeddings from `α` to `β` taking the first subset onto the second.
This separates the choices on a prescribed subset from the unconstrained remaining vertices,
as needed when bounding the number of copies affected by a hyperedge edit.

When the source is `Fin r` itself, the embeddings `Fin r ↪ β` whose unordered image
`Set.powersetCard.ofFinEmb r β` equals a prescribed `r`-element subset `t` correspond to the
embeddings `Fin r ↪ t.val`, so there are `r!` of them without any finiteness assumption on `β`,
and two embeddings `Fin r ↪ β` have the same unordered image precisely when they differ by a
permutation of `Fin r`.
-/

public section

namespace Set.powersetCard

variable {β : Type*} {r : ℕ}

/-- The embeddings `Fin r ↪ β` with unordered image `t` correspond to the embeddings of `Fin r`
into `t`. -/
def ofFinEmbFiberEquiv (t : Set.powersetCard β r) :
    {f : Fin r ↪ β // ofFinEmb r β f = t} ≃ (Fin r ↪ t.val) where
  toFun f :=
    ⟨fun i ↦ ⟨f.1 i, by
        have h := congrArg Subtype.val f.2
        rw [val_ofFinEmb] at h
        exact h ▸ Finset.mem_map_of_mem f.1 (Finset.mem_univ i)⟩,
      fun _ _ h ↦ f.1.injective (congrArg Subtype.val h)⟩
  invFun g :=
    ⟨g.trans (Function.Embedding.subtype _), Subtype.ext <| by
      rw [val_ofFinEmb]
      refine Finset.eq_of_subset_of_card_le (fun b hb ↦ ?_) (by simp [card_eq])
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb
      exact (g i).2⟩
  left_inv _ := Subtype.ext (Function.Embedding.ext fun _ ↦ rfl)
  right_inv _ := Function.Embedding.ext fun _ ↦ Subtype.ext rfl

@[simp]
theorem ofFinEmbFiberEquiv_apply_coe (t : Set.powersetCard β r)
    (f : {f : Fin r ↪ β // ofFinEmb r β f = t}) (i : Fin r) :
    (ofFinEmbFiberEquiv t f i : β) = f.1 i :=
  (rfl)

@[simp]
theorem ofFinEmbFiberEquiv_symm_apply_coe (t : Set.powersetCard β r)
    (g : Fin r ↪ t.val) (i : Fin r) :
    ((ofFinEmbFiberEquiv t).symm g).1 i = (g i : β) :=
  (rfl)

/-- Exactly `r!` embeddings `Fin r ↪ β` have a prescribed `r`-element subset `t` as unordered
image. -/
theorem natCard_ofFinEmb_eq (t : Set.powersetCard β r) :
    Nat.card {f : Fin r ↪ β // ofFinEmb r β f = t} = r.factorial := by
  rw [Nat.card_congr (ofFinEmbFiberEquiv t), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, card_eq,
    Nat.descFactorial_self]

/-- Precomposing an embedding `Fin r ↪ β` with a permutation of `Fin r` leaves its unordered
image unchanged. -/
@[simp]
theorem ofFinEmb_trans_perm (σ : Equiv.Perm (Fin r)) (f : Fin r ↪ β) :
    ofFinEmb r β (σ.toEmbedding.trans f) = ofFinEmb r β f :=
  SetLike.coe_injective <| by
    simp only [coe_ofFinEmb, Function.Embedding.coe_trans, Equiv.coe_toEmbedding]
    exact σ.surjective.range_comp f

/-- Two embeddings `Fin r ↪ β` have the same unordered image if and only if they differ by a
permutation of `Fin r`. -/
theorem ofFinEmb_eq_iff_exists_perm (f g : Fin r ↪ β) :
    ofFinEmb r β f = ofFinEmb r β g ↔ ∃ σ : Equiv.Perm (Fin r), ⇑f = ⇑g ∘ σ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · set t := ofFinEmb r β g
    let f' := ofFinEmbFiberEquiv t ⟨f, h⟩
    let g' := ofFinEmbFiberEquiv t ⟨g, rfl⟩
    have hcard : Fintype.card (Fin r) = Fintype.card t.val := by simp [card_eq]
    let ef := Equiv.ofBijective f' ((Fintype.bijective_iff_injective_and_card f').2
      ⟨f'.injective, hcard⟩)
    let eg := Equiv.ofBijective g' ((Fintype.bijective_iff_injective_and_card g').2
      ⟨g'.injective, hcard⟩)
    refine ⟨ef.trans eg.symm, funext fun i ↦ ?_⟩
    exact (congrArg Subtype.val (eg.apply_symm_apply (ef i))).symm
  · rintro ⟨σ, hfg⟩
    have htr : f = σ.toEmbedding.trans g := Function.Embedding.ext (congrFun hfg)
    rw [htr, ofFinEmb_trans_perm]

end Set.powersetCard

namespace TauCeti

/-- The embeddings taking one prescribed `r`-element subset onto another are bounded by the
`r!` bijections on those subsets and arbitrary choices on the complement. -/
theorem card_embedding_map_eq_le {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    {s : Set.powersetCard α r} {t : Set.powersetCard β r} :
    Nat.card {f : α ↪ β // Set.powersetCard.map r f s = t} ≤
      r.factorial * Fintype.card β ^ (Fintype.card α - r) := by
  classical
  let code : {f : α ↪ β // Set.powersetCard.map r f s = t} →
      (s.val ↪ t.val) × (↥(s.valᶜ) → β) := fun f ↦
    (⟨fun a ↦ ⟨f.val a, by
        have hm : f.val a ∈ (Set.powersetCard.map r f.val s).val := by
          simp only [Set.powersetCard.val_map, Finset.mem_map]
          exact ⟨a, a.prop, rfl⟩
        simpa only [f.prop] using hm⟩,
      fun a b h ↦ Subtype.ext (f.val.injective (congrArg Subtype.val h))⟩,
      fun a ↦ f.val a)
  have hinj : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    ext a
    by_cases ha : a ∈ s.val
    · exact congrArg Subtype.val
        (congrFun (congrArg (fun p ↦ (p.1 : s.val → t.val)) h) ⟨a, ha⟩)
    · exact congrFun (congrArg Prod.snd h) ⟨a, Finset.mem_compl.mpr ha⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fun, Fintype.card_coe, Set.powersetCard.card_eq, Finset.card_compl,
    Nat.descFactorial_self] using Nat.card_le_card_of_injective code hinj

/-- Among injective `r`-tuples in a finite type, `r!` have a prescribed `r`-element subset `t` as
unordered image. -/
theorem card_filter_ofFinEmb_eq {β : Type*} [Fintype β] [DecidableEq β] {r : ℕ}
    (t : Set.powersetCard β r) :
    Finset.card (Finset.univ.filter fun x : {x : Fin r → β // Function.Injective x} ↦
      Set.powersetCard.ofFinEmb r β ⟨x.1, x.2⟩ = t) = r.factorial := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← Set.powersetCard.natCard_ofFinEmb_eq t]
  exact Nat.card_congr ((Equiv.subtypeInjectiveEquivEmbedding (Fin r) β).subtypeEquiv fun _ ↦
    Iff.rfl)

end TauCeti
