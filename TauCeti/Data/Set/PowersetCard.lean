/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Fintype.CardEmbedding

import TauCeti.Algebra.BigOperators.Finset.Powerset

/-!
# Maps, coercions and enumerations of fixed-cardinality subsets

`Set.powersetCard.map_injective` shows that vertex embeddings induce injective maps on
fixed-cardinality subsets. `Set.powersetCard.map_refl` and `Set.powersetCard.map_map` show that
these induced maps respect identities and composition of embeddings.

`Set.powersetCard.coe_ofSingleton`, `Set.powersetCard.mem_ofSingleton`, and
`Set.powersetCard.map_ofSingleton` relate the singleton equivalence to finite sets and embeddings,
`Set.powersetCard.map_compl_equiv` commutes `map` along an equivalence with `compl`,
`Set.powersetCard.disjoint_map` and `Set.powersetCard.map_disjUnion` relate `map` along an
embedding to disjointness and `disjUnion`, `Set.powersetCard.le_card` and
`Set.powersetCard.sub_add_eq_card` record the cardinality bound witnessed by an `r`-element subset
of a finite type, and `Set.powersetCard.subsingleton_of_card_eq` together with the
`Unique`/`Subsingleton` instances witness uniqueness at cardinalities `0` and `Fintype.card α`.
For `p + 1 = Fintype.card α`, `Set.powersetCard.omitOne` is the equivalence sending `a : α` to the
`p`-element subset `Finset.univ.erase a` omitting `a`.

`Set.powersetCard.val_ofFinEmb_fin_three` lists the three elements of the subset enumerated by an
embedding of `Fin 3`.

`Set.powersetCard.fintypeCard` counts the `n`-element subsets of a finite type, and
`Set.powersetCard.finChooseEquiv m j` enumerates the `j`-element subsets of `Fin m` by
`Fin (m.choose j)`.

`Set.powersetCard.prod_prod` and `Set.powersetCard.sum_sum` count over the `n`-element subsets of
a finite type: each element lies in `(card α - 1).choose (n - 1)` of them.

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
theorem mem_ofSingleton {α : Type*} {a b : α} : b ∈ ofSingleton a ↔ b = a := by
  rw [← mem_coe_iff, coe_ofSingleton, Finset.mem_singleton]

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

/-- Mapping along an embedding preserves disjointness of fixed-cardinality subsets. -/
theorem disjoint_map {α β : Type*} {m n : ℕ} (f : α ↪ β)
    {s : powersetCard α m} {t : powersetCard α n} :
    Disjoint (map m f s).val (map n f t).val ↔ Disjoint s.val t.val := by
  rw [val_map, val_map, Finset.disjoint_map]

/-- Mapping along an embedding commutes with disjoint union of fixed-cardinality subsets. -/
@[simp]
theorem map_disjUnion {α β : Type*} {m n : ℕ} (f : α ↪ β)
    {s : powersetCard α m} {t : powersetCard α n} (hst : Disjoint s.val t.val) :
    map (m + n) f (disjUnion hst) =
      disjUnion (s := map m f s) (t := map n f t) ((disjoint_map f).mpr hst) :=
  Subtype.ext (Finset.map_disjUnion (f := f) s.val t.val hst)

/-- Every `r`-element subset of a finite type `α` satisfies `r ≤ Fintype.card α`. -/
theorem le_card {α : Type*} [Fintype α] {r : ℕ} (T : powersetCard α r) :
    r ≤ Fintype.card α := by
  simpa [ENat.card_eq_coe_fintype_card] using nonempty_iff.mp ⟨T⟩

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

/-- Every `0`-element subset of `α` has underlying finite set `∅`. -/
@[simp]
theorem coe_eq_empty {α : Type*} (s : powersetCard α 0) : (s : Finset α) = ∅ :=
  Finset.card_eq_zero.mp (card_eq s)

/-- The empty finite set is the unique `0`-element subset of `α`. -/
instance instUniqueZero {α : Type*} : Unique (powersetCard α 0) where
  default := ⟨∅, Finset.card_empty⟩
  uniq s := Subtype.ext (coe_eq_empty s)

/-- When `d = Fintype.card α`, `Set.powersetCard α d` has at most one element. -/
theorem subsingleton_of_card_eq {α : Type*} [Fintype α] {d : ℕ} (hd : d = Fintype.card α) :
    Subsingleton (powersetCard α d) :=
  ⟨fun s t ↦ Subtype.ext <|
    (Finset.eq_univ_of_card _ ((card_eq s).trans hd)).trans
      (Finset.eq_univ_of_card _ ((card_eq t).trans hd)).symm⟩

/-- A finite type `α` has at most one `Fintype.card α`-element subset. -/
instance instSubsingletonCard {α : Type*} [Fintype α] :
    Subsingleton (powersetCard α (Fintype.card α)) :=
  subsingleton_of_card_eq rfl

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
@[simp, grind =]
theorem mem_omitOne {hm : p + 1 = Fintype.card α} {a b : α} :
    b ∈ omitOne hm a ↔ b ≠ a := by
  rw [← mem_coe_iff, coe_omitOne, Finset.mem_erase]
  simp

/-- Taking the complement of `omitOne hm a` recovers the singleton `{a}`. -/
@[simp]
theorem compl_omitOne (hm : p + 1 = Fintype.card α) (a : α) :
    compl ((Nat.add_comm 1 p).trans hm) (omitOne hm a) = ofSingleton a := by
  rw [omitOne_apply, ← compl_symm (hm := hm), Equiv.symm_apply_apply]

/-- `(omitOne hm).symm s` recovers the unique element outside `s` via `compl` and
`ofSingleton.symm`. -/
theorem omitOne_symm_apply (hm : p + 1 = Fintype.card α) (s : powersetCard α p) :
    (omitOne hm).symm s = ofSingleton.symm (compl ((Nat.add_comm 1 p).trans hm) s) := by
  simp [omitOne, compl_symm]

/-- `(omitOne hm).symm s` equals `a` precisely when `a` does not belong to `s`. -/
theorem omitOne_symm_apply_eq_iff {hm : p + 1 = Fintype.card α} {s : powersetCard α p} {a : α} :
    (omitOne hm).symm s = a ↔ a ∉ s := by
  rw [Equiv.symm_apply_eq, eq_iff_subset, coe_omitOne, Finset.subset_erase]
  simp [mem_coe_iff]

/-- The element `(omitOne hm).symm s` omitted by `s` does not belong to `s`. -/
@[simp, grind .]
theorem omitOne_symm_notMem (hm : p + 1 = Fintype.card α) (s : powersetCard α p) :
    (omitOne hm).symm s ∉ s :=
  omitOne_symm_apply_eq_iff.mp rfl

end OmitOne

/-- The three-element subset enumerated by an embedding `f : Fin 3 ↪ α` is `{f 0, f 1, f 2}`. -/
theorem val_ofFinEmb_fin_three {α : Type*} [DecidableEq α] (f : Fin 3 ↪ α) :
    (ofFinEmb 3 α f : Finset α) = {f 0, f 1, f 2} := by
  ext v
  simp [val_ofFinEmb, Fin.exists_fin_succ, eq_comm]

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

variable {β : Type*} {r : ℕ}

/-- The embeddings `Fin r ↪ β` with unordered image `t` correspond to the embeddings of `Fin r`
into `t`. -/
def ofFinEmbFiberEquiv (t : Set.powersetCard β r) :
    {f : Fin r ↪ β // ofFinEmb r β f = t} ≃ (Fin r ↪ t.val) where
  toFun f :=
    ⟨fun i ↦ ⟨f.val i, by
        have h := congrArg Subtype.val f.property
        rw [val_ofFinEmb] at h
        exact h ▸ Finset.mem_map_of_mem f.val (Finset.mem_univ i)⟩,
      fun _ _ h ↦ f.val.injective (congrArg Subtype.val h)⟩
  invFun g :=
    ⟨g.trans (Function.Embedding.subtype _), Subtype.ext <| by
      rw [val_ofFinEmb]
      refine Finset.eq_of_subset_of_card_le (fun b hb ↦ ?_) (by simp [card_eq])
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb
      exact (g i).property⟩
  left_inv _ := Subtype.ext (Function.Embedding.ext fun _ ↦ rfl)
  right_inv _ := Function.Embedding.ext fun _ ↦ Subtype.ext rfl

/-- Applying `ofFinEmbFiberEquiv t` preserves vertex values. -/
@[simp]
theorem ofFinEmbFiberEquiv_apply_coe (t : Set.powersetCard β r)
    (f : {f : Fin r ↪ β // ofFinEmb r β f = t}) (i : Fin r) :
    (ofFinEmbFiberEquiv t f i : β) = f.val i :=
  (rfl)

/-- Applying `(ofFinEmbFiberEquiv t).symm` preserves vertex values. -/
@[simp]
theorem ofFinEmbFiberEquiv_symm_apply_coe (t : Set.powersetCard β r)
    (g : Fin r ↪ t.val) (i : Fin r) :
    ((ofFinEmbFiberEquiv t).symm g).val i = (g i : β) :=
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
  · set t := ofFinEmb r β g
    let f' := ofFinEmbFiberEquiv t ⟨f, h⟩
    let g' := ofFinEmbFiberEquiv t ⟨g, rfl⟩
    have hcard : Fintype.card (Fin r) = Fintype.card t.val := by simp [card_eq]
    let ef := Equiv.ofBijective f' ((Fintype.bijective_iff_injective_and_card f').2
      ⟨f'.injective, hcard⟩)
    let eg := Equiv.ofBijective g' ((Fintype.bijective_iff_injective_and_card g').2
      ⟨g'.injective, hcard⟩)
    refine ⟨ef.trans eg.symm, funext fun i ↦ ?_⟩
    calc
      f i = (ef i : β) := by
        simp only [ef, f', Equiv.ofBijective_apply, ofFinEmbFiberEquiv_apply_coe]
      _ = (eg (eg.symm (ef i)) : β) := (congrArg Subtype.val (eg.apply_symm_apply (ef i))).symm
      _ = (g ∘ ⇑(ef.trans eg.symm)) i := by
        simp only [Function.comp_apply, Equiv.trans_apply, eg, g', Equiv.ofBijective_apply,
          ofFinEmbFiberEquiv_apply_coe]
  · rintro ⟨σ, hfg⟩
    have htr : f = σ.toEmbedding.trans g := Function.Embedding.ext (congrFun hfg)
    rw [htr, ofFinEmb_trans_perm]

end Set.powersetCard
