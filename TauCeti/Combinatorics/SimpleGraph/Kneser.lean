/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Kneser graphs

For a family `𝓕` of finite subsets of `α`, the Kneser graph `TauCeti.kneserGraphOf 𝓕` has the
members of `𝓕` as vertices, two of them adjacent when they are distinct and disjoint. The Kneser
graph `TauCeti.kneserGraph α k`, written `KG(α, k)`, is the case of the `k`-element subsets
of `α`. The clause "distinct" matters only for the empty set, which is disjoint from itself:
with it, `∅` is adjacent to every other member of the family and the graph has no loop.

Kneser graphs are the subject of Lovász's theorem on their chromatic number and of Dol'nikov's
bound by the colourability defect. This file sets up the graphs and their basic facts.

## Main definitions

* `TauCeti.kneserGraphOf 𝓕`: the Kneser graph of a family `𝓕 : Set (Finset α)`.
* `TauCeti.kneserGraph α k`: the Kneser graph of the `k`-element subsets of `α`.
* `TauCeti.kneserGraphOneIso α`: `KG(α, 1)` is isomorphic to the complete graph on `α`.
* `TauCeti.kneserGraphOfEmbedding`, `TauCeti.kneserGraphEmbedding`: an injection `α ↪ β`
  induces embeddings of Kneser graphs.

## Main results

* `TauCeti.kneserGraph_eq_bot_iff`: `KG(α, k)` has no edge exactly when `k = 0` or
  `|α| < 2k`.
* `TauCeti.kneserGraph_degree`, `TauCeti.kneserGraph_isRegularOfDegree`: for `k ≥ 1`, every
  vertex of `KG(α, k)` has degree `binom(|α| - k, k)`.

## References

* L. Lovász, *Kneser's conjecture, chromatic number, and homotopy*, J. Combin. Theory Ser. A 25
  (1978), 319-324.
* J. Matoušek, *Using the Borsuk-Ulam theorem*, Springer, 2003, Section 3.3.
-/

public section

open Finset SimpleGraph

namespace TauCeti

variable {α β : Type*}

/-- The Kneser graph of a family `𝓕` of finite sets: its vertices are the members of `𝓕`, two of
them adjacent when they are distinct and disjoint. -/
def kneserGraphOf (𝓕 : Set (Finset α)) : SimpleGraph 𝓕 where
  Adj A B := A ≠ B ∧ Disjoint (A : Finset α) B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The Kneser graph `KG(α, k)`: the `k`-element subsets of `α`, two adjacent when they are
distinct and disjoint. -/
def kneserGraph (α : Type*) (k : ℕ) : SimpleGraph {s : Finset α | s.card = k} :=
  kneserGraphOf {s : Finset α | s.card = k}

section Of

variable {𝓕 : Set (Finset α)}

/-- Two members of `𝓕` are adjacent in `kneserGraphOf 𝓕` when they are distinct and disjoint. -/
@[simp]
theorem kneserGraphOf_adj {A B : 𝓕} :
    (kneserGraphOf 𝓕).Adj A B ↔ A ≠ B ∧ Disjoint (A : Finset α) B :=
  Iff.rfl

/-- A nonempty member of `𝓕` is adjacent to exactly the members disjoint from it. -/
theorem kneserGraphOf_adj_iff_disjoint {A B : 𝓕} (hA : (A : Finset α).Nonempty) :
    (kneserGraphOf 𝓕).Adj A B ↔ Disjoint (A : Finset α) B := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  exact hA.ne_empty ((disjoint_self_iff_empty _).1 h)

/-- Adjacency in `kneserGraphOf 𝓕` is decidable when equality on `α` is. -/
instance [DecidableEq α] (𝓕 : Set (Finset α)) : DecidableRel (kneserGraphOf 𝓕).Adj :=
  fun _ _ => decidable_of_iff' _ kneserGraphOf_adj

/-- An injection `f : α ↪ β` that maps every member of `𝓕` into `𝓖` induces an embedding of
`kneserGraphOf 𝓕` into `kneserGraphOf 𝓖`, given by `A ↦ A.map f`. -/
def kneserGraphOfEmbedding (f : α ↪ β) {𝓖 : Set (Finset β)} (h : ∀ A ∈ 𝓕, A.map f ∈ 𝓖) :
    kneserGraphOf 𝓕 ↪g kneserGraphOf 𝓖 where
  toFun A := ⟨(A : Finset α).map f, h A A.property⟩
  inj' _ _ hAB := Subtype.ext (map_inj.1 (congrArg Subtype.val hAB))
  map_rel_iff' {A B} := by
    rw [kneserGraphOf_adj, kneserGraphOf_adj]
    exact and_congr (not_congr (Subtype.ext_iff.trans (map_inj.trans Subtype.ext_iff.symm)))
      (disjoint_map f)

/-- The embedding `kneserGraphOfEmbedding f h` sends `A` to `A.map f`. -/
@[simp]
theorem coe_kneserGraphOfEmbedding_apply (f : α ↪ β) {𝓖 : Set (Finset β)}
    (h : ∀ A ∈ 𝓕, A.map f ∈ 𝓖) (A : 𝓕) :
    (kneserGraphOfEmbedding f h A : Finset β) = (A : Finset α).map f :=
  (rfl)

end Of

section KneserGraph

variable {k : ℕ}

/-- Two `k`-subsets are adjacent in `KG(α, k)` when they are distinct and disjoint. -/
@[simp]
theorem kneserGraph_adj {A B : {s : Finset α | s.card = k}} :
    (kneserGraph α k).Adj A B ↔ A ≠ B ∧ Disjoint (A : Finset α) B :=
  Iff.rfl

/-- For `k ≥ 1`, two `k`-subsets are adjacent in `KG(α, k)` exactly when they are disjoint. -/
theorem kneserGraph_adj_iff_disjoint (hk : 0 < k) {A B : {s : Finset α | s.card = k}} :
    (kneserGraph α k).Adj A B ↔ Disjoint (A : Finset α) B :=
  kneserGraphOf_adj_iff_disjoint (card_pos.1 (A.property.symm ▸ hk))

/-- Adjacency in `KG(α, k)` is decidable when equality on `α` is. -/
instance [DecidableEq α] (k : ℕ) : DecidableRel (kneserGraph α k).Adj :=
  fun _ _ => decidable_of_iff' _ kneserGraph_adj

/-- `KG(α, 0)` has no edge: its one vertex is `∅`, and the clause `A ≠ B` removes the loop. -/
@[simp]
theorem kneserGraph_zero (α : Type*) : kneserGraph α 0 = ⊥ := by
  ext A B
  have hA : (A : Finset α) = ∅ := card_eq_zero.1 A.property
  have hB : (B : Finset α) = ∅ := card_eq_zero.1 B.property
  simp [Subtype.ext_iff, hA, hB]

/-- `KG(α, k)` has no edge exactly when `k = 0` or `|α| < 2k`. -/
theorem kneserGraph_eq_bot_iff [Fintype α] :
    kneserGraph α k = ⊥ ↔ k = 0 ∨ Fintype.card α < 2 * k := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · refine or_iff_not_imp_left.2 fun hk => not_le.1 fun hle => ?_
    obtain ⟨A, -, hA⟩ := exists_subset_card_eq (s := (univ : Finset α)) (n := k)
      (by rw [card_univ]; omega)
    obtain ⟨B, hBA, hB⟩ := exists_subset_card_eq (s := Aᶜ) (n := k)
      (by rw [card_compl, hA]; omega)
    have hadj : (kneserGraph α k).Adj ⟨A, hA⟩ ⟨B, hB⟩ :=
      (kneserGraph_adj_iff_disjoint (Nat.pos_of_ne_zero hk)).2
        (disjoint_left.2 fun a haA haB => mem_compl.1 (hBA haB) haA)
    rw [h] at hadj
    exact hadj
  · rintro (rfl | hlt)
    · exact kneserGraph_zero α
    · ext A B
      simp only [kneserGraph_adj, bot_adj, iff_false, not_and]
      intro _ hAB
      have := card_union_of_disjoint hAB
      have := card_le_univ ((A : Finset α) ∪ B)
      have hA : (A : Finset α).card = k := A.property
      have hB : (B : Finset α).card = k := B.property
      omega

/-- If `|α| < 2k`, then `KG(α, k)` has no edge: two disjoint `k`-subsets need `2k` points. -/
theorem kneserGraph_eq_bot [Fintype α] (h : Fintype.card α < 2 * k) : kneserGraph α k = ⊥ :=
  kneserGraph_eq_bot_iff.2 (Or.inr h)

/-- For `k ≥ 1`, every vertex of `KG(α, k)` has degree `binom(|α| - k, k)`: its neighbours are
the `k`-subsets of its complement. -/
theorem kneserGraph_degree [Fintype α] (hk : 0 < k) (A : {s : Finset α | s.card = k})
    [Fintype ((kneserGraph α k).neighborSet A)] :
    (kneserGraph α k).degree A = (Fintype.card α - k).choose k := by
  classical
  have hA : #(A : Finset α)ᶜ = Fintype.card α - k := by rw [card_compl, A.property]
  rw [← card_neighborFinset_eq_degree, ← hA, ← card_powersetCard]
  refine card_nbij Subtype.val (fun B hB => ?_) Subtype.val_injective.injOn fun s hs => ?_
  · rw [mem_coe, mem_neighborFinset, kneserGraph_adj_iff_disjoint hk] at hB
    exact mem_powersetCard.2 ⟨subset_compl_iff_disjoint_left.2 hB, B.property⟩
  · obtain ⟨hsA, hs⟩ := mem_powersetCard.1 hs
    refine ⟨⟨s, hs⟩, ?_, rfl⟩
    rw [mem_coe, mem_neighborFinset, kneserGraph_adj_iff_disjoint hk]
    exact subset_compl_iff_disjoint_left.1 hsA

/-- For `k ≥ 1`, `KG(α, k)` is regular of degree `binom(|α| - k, k)`. -/
theorem kneserGraph_isRegularOfDegree [Fintype α] (hk : 0 < k)
    [(kneserGraph α k).LocallyFinite] :
    (kneserGraph α k).IsRegularOfDegree ((Fintype.card α - k).choose k) :=
  fun A => kneserGraph_degree hk A

/-- `KG(α, 1)` is isomorphic to the complete graph on `α`, by `{a} ↦ a`. -/
noncomputable def kneserGraphOneIso (α : Type*) : kneserGraph α 1 ≃g completeGraph α :=
  RelIso.symm
    { toFun a := ⟨{a}, card_singleton a⟩
      invFun A := (card_eq_one.1 A.property).choose
      left_inv a := singleton_injective (card_eq_one.1 (card_singleton a)).choose_spec.symm
      right_inv A := Subtype.ext (card_eq_one.1 A.property).choose_spec.symm
      map_rel_iff' {a b} := by simp [Subtype.ext_iff] }

/-- The inverse of `kneserGraphOneIso α` sends `a` to `{a}`. -/
@[simp]
theorem coe_kneserGraphOneIso_symm_apply (a : α) :
    ((kneserGraphOneIso α).symm a : Finset α) = {a} :=
  (rfl)

/-- The isomorphism `kneserGraphOneIso α` sends `{a}` to `a`. -/
@[simp]
theorem kneserGraphOneIso_apply_singleton (a : α) :
    kneserGraphOneIso α ⟨{a}, card_singleton a⟩ = a :=
  (kneserGraphOneIso α).apply_symm_apply a

/-- An injection `f : α ↪ β` induces an embedding of `KG(α, k)` into `KG(β, k)`, given by
`A ↦ A.map f`. -/
def kneserGraphEmbedding (f : α ↪ β) (k : ℕ) : kneserGraph α k ↪g kneserGraph β k :=
  kneserGraphOfEmbedding f fun _ hA => (card_map f).trans hA

/-- The embedding `kneserGraphEmbedding f k` sends `A` to `A.map f`. -/
@[simp]
theorem coe_kneserGraphEmbedding_apply (f : α ↪ β) (k : ℕ) (A : {s : Finset α | s.card = k}) :
    (kneserGraphEmbedding f k A : Finset β) = (A : Finset α).map f :=
  (rfl)

end KneserGraph

end TauCeti
