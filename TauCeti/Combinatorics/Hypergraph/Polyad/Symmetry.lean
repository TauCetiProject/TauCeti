/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Tactic.FinCases

/-!
# Transversal polyads, canonical cell ordering, and role symmetries

An injective triple `x : Fin 3 → V` determines an unordered triple `tripleSet x` in
`Set.powersetCard V 3`. On a general polyad `P`, up to six role-ordered triples in `P.support` can
share the same unordered triple; when the three vertex cells of `P` are pairwise distinct
(`Polyad3.IsTransversal`), `tripleSet` is injective on `P.support`, so unordered-triple counts on
any subset `A ⊆ P.support` agree with `relDensityOn` counts on `A`.

Given an indexing `idx : S.vertexPart.parts ≃ Fin k` of the vertex cells, a transversal polyad is
*canonical* (`Polyad3.IsCanonical`) when `idx c₀ < idx c₁ < idx c₂`. Distinct canonical polyads
have disjoint unordered-triple supports, allowing independent recolorings on each canonical
polyad's unordered triples to be glued without conflict. Every transversal polyad is related to a
canonical polyad by compositions of the adjacent role swaps `Polyad3.swap01` and `Polyad3.swap12`,
which preserve support cardinality, relative color densities, coarse parent densities, and rank-one
top regularity.

This file also records the upper bound `card_subpolyad3_le` (`2 ^ (3 * |V| ^ 2)`) on the number of
subpolyads of a polyad on `V`.

## Main definitions

* `TauCeti.tripleSet`: the unordered triple in `Set.powersetCard V 3` underlying an injective
  triple `{x : Fin 3 → V // Function.Injective x}`.
* `TauCeti.Polyad3.IsTransversal`: the three vertex cells of a polyad are pairwise distinct.
* `TauCeti.Polyad3.IsCanonical`: the three vertex cells of a polyad are strictly increasing under a
  cell indexing.
* `TauCeti.Polyad3.swap01`, `TauCeti.Polyad3.swap12`: adjacent role swaps on polyads.

## Main results

* `TauCeti.card_subpolyad3_le`: a polyad on `V` has at most `2 ^ (3 * |V| ^ 2)` subpolyads.
* `TauCeti.Polyad3.injOn_tripleSet_support`: `tripleSet` is injective on the support of a
  transversal polyad.
* `TauCeti.Polyad3.disjoint_image_tripleSet_of_isCanonical`: distinct canonical polyads have
  disjoint unordered-triple supports.
* `TauCeti.Polyad3.exists_isCanonical_of_isTransversal`: every transversal polyad can be permuted
  into canonical cell order while preserving support size, fine and coarse relative densities, and
  rank-one top regularity.
-/

public section

open Finset Function

namespace TauCeti

/-- Every polyad on `V` has at most `2 ^ (3 * |V| ^ 2)` subpolyads, since each of its three
selected pair graphs is a subset of the distinct ordered pairs on `V`. -/
theorem card_subpolyad3_le {κ V : Type*} [Fintype V] [DecidableEq V]
    {S : PairSkeleton3 κ V} (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) ≤ 2 ^ (3 * Fintype.card V ^ 2) := by
  classical
  let g : Subpolyad3 P →
      ↥(P.pairSupport₀₁.powerset ×ˢ P.pairSupport₀₂.powerset ×ˢ P.pairSupport₁₂.powerset) :=
    fun W ↦ ⟨(W.pair₀₁, W.pair₀₂, W.pair₁₂),
      mem_product.2 ⟨mem_powerset.2 W.pair₀₁_sub,
        mem_product.2 ⟨mem_powerset.2 W.pair₀₂_sub, mem_powerset.2 W.pair₁₂_sub⟩⟩⟩
  have hginj : Injective g := fun W₁ W₂ h ↦ by
    have h' := Subtype.ext_iff.1 h
    simp only [g, Prod.mk.injEq] at h'
    exact Subpolyad3.ext_data h'.1 h'.2.1 h'.2.2
  have hpair_le (A : Finset {p : V × V // p.1 ≠ p.2}) : #A ≤ Fintype.card V ^ 2 :=
    (card_le_univ A).trans ((Fintype.card_subtype_le _).trans_eq (by rw [Fintype.card_prod, sq]))
  have hcard := Fintype.card_le_of_injective g hginj
  rw [Fintype.card_coe, card_product, card_product, card_powerset, card_powerset,
    card_powerset] at hcard
  refine hcard.trans ?_
  calc 2 ^ #P.pairSupport₀₁ * (2 ^ #P.pairSupport₀₂ * 2 ^ #P.pairSupport₁₂)
      = 2 ^ (#P.pairSupport₀₁ + #P.pairSupport₀₂ + #P.pairSupport₁₂) := by
        rw [← pow_add, ← pow_add, add_assoc]
    _ ≤ 2 ^ (3 * Fintype.card V ^ 2) := Nat.pow_le_pow_right two_pos (by
        have := hpair_le P.pairSupport₀₁
        have := hpair_le P.pairSupport₀₂
        have := hpair_le P.pairSupport₁₂
        omega)

section UnorderedTriples

variable {κ V : Type*}

/-- The unordered 3-element subset of `V` determined by an injective triple `Fin 3 → V`. -/
def tripleSet (x : {x : Fin 3 → V // Injective x}) : Set.powersetCard V 3 :=
  Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩

/-- `tripleSet` is `Set.powersetCard.ofFinEmb 3 V` applied to the underlying embedding. -/
theorem tripleSet_def (x : {x : Fin 3 → V // Injective x}) :
    tripleSet x = Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ :=
  (rfl)

/-- A vertex belongs to `tripleSet x` iff it is one of the three coordinates of `x`. -/
@[simp]
theorem mem_tripleSet_iff {x : {x : Fin 3 → V // Injective x}} {v : V} :
    v ∈ (tripleSet x).1 ↔ ∃ i : Fin 3, x.1 i = v := by
  simp [tripleSet]

private def pairSwap (p : {p : V × V // p.1 ≠ p.2}) : {p : V × V // p.1 ≠ p.2} :=
  ⟨p.1.swap, p.2.symm⟩

private theorem pairSwap_involutive : Involutive (pairSwap (V := V)) :=
  fun _ ↦ Subtype.ext (Prod.swap_swap _)

private def triplePerm (σ : Equiv.Perm (Fin 3)) :
    {x : Fin 3 → V // Injective x} ≃ {x : Fin 3 → V // Injective x} where
  toFun x := ⟨x.1 ∘ σ, x.2.comp σ.injective⟩
  invFun x := ⟨x.1 ∘ σ.symm, x.2.comp σ.symm.injective⟩
  left_inv x := Subtype.ext (by ext i; simp)
  right_inv x := Subtype.ext (by ext i; simp)

private theorem tripleSet_triplePerm (σ : Equiv.Perm (Fin 3))
    (x : {x : Fin 3 → V // Injective x}) :
    tripleSet (triplePerm σ x) = tripleSet x := by
  apply Subtype.ext
  ext v
  simp only [tripleSet, triplePerm, Equiv.coe_fn_mk, Set.powersetCard.val_ofFinEmb, mem_map,
    mem_univ, true_and, Function.Embedding.coeFn_mk, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨σ i, hi⟩, fun ⟨j, hj⟩ ↦ ⟨σ.symm j, by simpa using hj⟩⟩

private theorem relDensityOn_map_triplePerm [DecidableEq κ] (H : Colored3Graph κ V) (c : κ)
    (σ : Equiv.Perm (Fin 3)) (A : Finset {x : Fin 3 → V // Injective x}) :
    H.relDensityOn c (A.map (triplePerm σ).toEmbedding) = H.relDensityOn c A := by
  rw [Colored3Graph.relDensityOn_def, Colored3Graph.relDensityOn_def, card_map]
  congr 2
  have hmap : (A.filter fun x ↦ H.color (tripleSet x) = c).map (triplePerm σ).toEmbedding =
      (A.map (triplePerm σ).toEmbedding).filter fun y ↦ H.color (tripleSet y) = c := by
    ext y
    simp only [mem_map, mem_filter, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨x, ⟨hxA, hxc⟩, rfl⟩
      exact ⟨⟨x, hxA, rfl⟩, by rwa [tripleSet_triplePerm]⟩
    · rintro ⟨⟨x, hxA, rfl⟩, hyc⟩
      exact ⟨x, ⟨hxA, by rwa [tripleSet_triplePerm] at hyc⟩, rfl⟩
  exact hmap ▸ card_map _

end UnorderedTriples

namespace Polyad3

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V]

/-- A polyad is *transversal* when its three vertex cells are pairwise distinct. -/
def IsTransversal {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Prop :=
  P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂

/-- Unfolded form of `Polyad3.IsTransversal`. -/
theorem isTransversal_iff {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} :
    P.IsTransversal ↔ P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂ :=
  Iff.rfl

/-- Coarsening between skeletons with the same vertex partition preserves transversality. -/
theorem isTransversal_coarsen_iff {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart = S.vertexPart) (f : κ₂' → κ₂) (Q : Polyad3 T) :
    (Q.coarsen hV.le f).IsTransversal ↔ Q.IsTransversal := by
  have hcell : ∀ A (hA : A ∈ T.vertexPart.parts),
      (Finpartition.refinementParent hV.le ⟨A, hA⟩).val = A := fun A hA ↦
    congrArg Subtype.val
      ((Finpartition.refinementParent_eq_iff hV.le (A := ⟨A, hV ▸ hA⟩)).2 le_rfl)
  simp [IsTransversal, hcell]

/-- On the support of a transversal polyad, the unordered-triple map `tripleSet` is injective. -/
theorem injOn_tripleSet_support {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (hP : P.IsTransversal) : Set.InjOn (tripleSet (V := V)) P.support := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, P.mem_support] at hx hy
  have hrange (v : V) : (∃ i, x.1 i = v) ↔ (∃ j, y.1 j = v) := by
    simpa only [mem_tripleSet_iff] using
      (congrArg (fun s : Set.powersetCard V 3 ↦ v ∈ s.1) hxy).to_iff
  have hdisj01 := S.vertexPart.disjoint P.hc₀ P.hc₁ hP.1
  have hdisj02 := S.vertexPart.disjoint P.hc₀ P.hc₂ hP.2.1
  have hdisj12 := S.vertexPart.disjoint P.hc₁ P.hc₂ hP.2.2
  apply Subtype.ext
  ext i
  fin_cases i
  · obtain ⟨j, hj⟩ := (hrange (x.1 0)).1 ⟨0, rfl⟩
    fin_cases j
    · exact hj.symm
    · exact (Finset.disjoint_left.1 hdisj01 hx.1 (hj ▸ hy.2.1)).elim
    · exact (Finset.disjoint_left.1 hdisj02 hx.1 (hj ▸ hy.2.2.1)).elim
  · obtain ⟨j, hj⟩ := (hrange (x.1 1)).1 ⟨1, rfl⟩
    fin_cases j
    · exact (Finset.disjoint_left.1 hdisj01 hy.1 (hj.symm ▸ hx.2.1)).elim
    · exact hj.symm
    · exact (Finset.disjoint_left.1 hdisj12 hx.2.1 (hj ▸ hy.2.2.1)).elim
  · obtain ⟨j, hj⟩ := (hrange (x.1 2)).1 ⟨2, rfl⟩
    fin_cases j
    · exact (Finset.disjoint_left.1 hdisj02 hy.1 (hj.symm ▸ hx.2.2.1)).elim
    · exact (Finset.disjoint_left.1 hdisj12 hy.2.1 (hj.symm ▸ hx.2.2.1)).elim
    · exact hj.symm

open Classical in
/-- Any subset of the support of a transversal polyad has the same size as its image under
`tripleSet`. -/
theorem card_image_tripleSet_of_subset {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (hP : P.IsTransversal) {A : Finset {x : Fin 3 → V // Injective x}} (hA : A ⊆ P.support) :
    #(A.image tripleSet) = #A :=
  card_image_of_injOn ((injOn_tripleSet_support hP).mono hA)

open Classical in
/-- On any subset `A` of the support of a transversal polyad, the number of unordered triples in
`A.image tripleSet` of color `c` equals `H.relDensityOn c A * #A`. -/
theorem card_filter_image_tripleSet_eq_mul_relDensityOn [DecidableEq κ]
    (H : Colored3Graph κ V) (c : κ) {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (hP : P.IsTransversal) {A : Finset {x : Fin 3 → V // Injective x}} (hA : A ⊆ P.support) :
    (#{s ∈ A.image tripleSet | H.color s = c} : ℝ) = (H.relDensityOn c A : ℝ) * #A := by
  have himg : ({x ∈ A | H.color (tripleSet x) = c}).image tripleSet =
      {s ∈ A.image tripleSet | H.color s = c} := by
    ext s
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨x, ⟨hxA, hxc⟩, rfl⟩
      exact ⟨⟨x, hxA, rfl⟩, hxc⟩
    · rintro ⟨⟨x, hxA, rfl⟩, hxc⟩
      exact ⟨x, ⟨hxA, hxc⟩, rfl⟩
  have hcard : #{s ∈ A.image tripleSet | H.color s = c} =
      #{x ∈ A | H.color (tripleSet x) = c} := by
    rw [← himg]
    exact card_image_of_injOn ((injOn_tripleSet_support hP).mono ((filter_subset _ A).trans hA))
  rw [hcard]
  exact_mod_cast (H.relDensityOn_mul_card c A).symm

/-- A polyad is *canonical* with respect to an indexing `idx : S.vertexPart.parts ≃ Fin k` when its
three cells satisfy `idx c₀ < idx c₁ < idx c₂`. -/
def IsCanonical {S : PairSkeleton3 κ₂ V} {k : ℕ}
    (idx : S.vertexPart.parts ≃ Fin k) (P : Polyad3 S) : Prop :=
  idx ⟨P.c₀, P.hc₀⟩ < idx ⟨P.c₁, P.hc₁⟩ ∧ idx ⟨P.c₁, P.hc₁⟩ < idx ⟨P.c₂, P.hc₂⟩

/-- Unfolded form of `Polyad3.IsCanonical`. -/
theorem isCanonical_iff {S : PairSkeleton3 κ₂ V} {k : ℕ}
    {idx : S.vertexPart.parts ≃ Fin k} {P : Polyad3 S} :
    P.IsCanonical idx ↔
      idx ⟨P.c₀, P.hc₀⟩ < idx ⟨P.c₁, P.hc₁⟩ ∧ idx ⟨P.c₁, P.hc₁⟩ < idx ⟨P.c₂, P.hc₂⟩ :=
  Iff.rfl

/-- Every canonical polyad is transversal. -/
theorem IsCanonical.isTransversal {S : PairSkeleton3 κ₂ V} {k : ℕ}
    {idx : S.vertexPart.parts ≃ Fin k} {P : Polyad3 S} (h : P.IsCanonical idx) :
    P.IsTransversal := by
  refine ⟨fun h01 ↦ ?_, fun h02 ↦ ?_, fun h12 ↦ ?_⟩
  · have h' : (⟨P.c₀, P.hc₀⟩ : S.vertexPart.parts) = ⟨P.c₁, P.hc₁⟩ := Subtype.ext h01
    exact h.1.ne (congrArg idx h')
  · have h' : (⟨P.c₀, P.hc₀⟩ : S.vertexPart.parts) = ⟨P.c₂, P.hc₂⟩ := Subtype.ext h02
    exact (h.1.trans h.2).ne (congrArg idx h')
  · have h' : (⟨P.c₁, P.hc₁⟩ : S.vertexPart.parts) = ⟨P.c₂, P.hc₂⟩ := Subtype.ext h12
    exact h.2.ne (congrArg idx h')

open Classical in
/-- Distinct canonical polyads over the same skeleton have disjoint unordered-triple supports. -/
theorem disjoint_image_tripleSet_of_isCanonical {S : PairSkeleton3 κ₂ V} {k : ℕ}
    {idx : S.vertexPart.parts ≃ Fin k} {P Q : Polyad3 S}
    (hP : P.IsCanonical idx) (hQ : Q.IsCanonical idx) (hne : P ≠ Q) :
    Disjoint (P.support.image tripleSet) (Q.support.image tripleSet) := by
  refine disjoint_left.2 fun s hsP hsQ ↦ hne ?_
  obtain ⟨x, hxP, rfl⟩ := mem_image.1 hsP
  obtain ⟨y, hyQ, hxy⟩ := mem_image.1 hsQ
  have hx := (P.mem_support x).1 hxP
  have hy := (Q.mem_support y).1 hyQ
  let cellIdx (v : V) : Fin k := idx ⟨S.vertexPart.part v, S.vertexPart.part_mem.2 (mem_univ v)⟩
  have hx0 : cellIdx (x.1 0) = idx ⟨P.c₀, P.hc₀⟩ :=
    congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem P.hc₀ hx.1))
  have hx1 : cellIdx (x.1 1) = idx ⟨P.c₁, P.hc₁⟩ :=
    congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem P.hc₁ hx.2.1))
  have hx2 : cellIdx (x.1 2) = idx ⟨P.c₂, P.hc₂⟩ :=
    congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem P.hc₂ hx.2.2.1))
  have hy0 : cellIdx (y.1 0) = idx ⟨Q.c₀, Q.hc₀⟩ :=
    congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem Q.hc₀ hy.1))
  have hy1 : cellIdx (y.1 1) = idx ⟨Q.c₁, Q.hc₁⟩ :=
    congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem Q.hc₁ hy.2.1))
  have hy2 : cellIdx (y.1 2) = idx ⟨Q.c₂, Q.hc₂⟩ :=
    congrArg idx (Subtype.ext (S.vertexPart.part_eq_of_mem Q.hc₂ hy.2.2.1))
  have hx_lt01 : cellIdx (x.1 0) < cellIdx (x.1 1) := hx0.symm ▸ hx1.symm ▸ hP.1
  have hx_lt12 : cellIdx (x.1 1) < cellIdx (x.1 2) := hx1.symm ▸ hx2.symm ▸ hP.2
  have hy_lt01 : cellIdx (y.1 0) < cellIdx (y.1 1) := hy0.symm ▸ hy1.symm ▸ hQ.1
  have hy_lt12 : cellIdx (y.1 1) < cellIdx (y.1 2) := hy1.symm ▸ hy2.symm ▸ hQ.2
  have hy_mono : StrictMono (fun j : Fin 3 ↦ cellIdx (y.1 j)) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact (hab.ne rfl).elim
    · exact hy_lt01
    · exact hy_lt01.trans hy_lt12
    · exact absurd hab (by decide)
    · exact (hab.ne rfl).elim
    · exact hy_lt12
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · exact (hab.ne rfl).elim
  have hrange (v : V) : (∃ i, y.1 i = v) ↔ (∃ j, x.1 j = v) := by
    simpa only [mem_tripleSet_iff] using
      (congrArg (fun u : Set.powersetCard V 3 ↦ v ∈ u.1) hxy).to_iff
  choose σ hσ using fun i : Fin 3 ↦ (hrange (x.1 i)).2 ⟨i, rfl⟩
  have hσ01 : σ 0 < σ 1 := hy_mono.lt_iff_lt.1 (by rw [hσ 0, hσ 1]; exact hx_lt01)
  have hσ12 : σ 1 < σ 2 := hy_mono.lt_iff_lt.1 (by rw [hσ 1, hσ 2]; exact hx_lt12)
  have h0_lt := (σ 0).isLt
  have h1_lt := (σ 1).isLt
  have h2_lt := (σ 2).isLt
  have h01_val : (σ 0).val < (σ 1).val := hσ01
  have h12_val : (σ 1).val < (σ 2).val := hσ12
  have hσ0 : σ 0 = 0 := Fin.ext (by omega)
  have hσ1 : σ 1 = 1 := Fin.ext (by omega)
  have hσ2 : σ 2 = 2 := Fin.ext (by omega)
  have hxy_eq : x = y := by
    apply Subtype.ext
    ext i
    fin_cases i
    · exact (hσ0 ▸ hσ 0).symm
    · exact (hσ1 ▸ hσ 1).symm
    · exact (hσ2 ▸ hσ 2).symm
  rw [hxy_eq] at hxP
  exact (mem_support_iff_eq_ofTriple.1 hxP).trans (mem_support_iff_eq_ofTriple.1 hyQ).symm

/-- Swap roles zero and one of a polyad, reversing the `(0, 1)` pair color and exchanging the
`(0, 2)` and `(1, 2)` pair colors. -/
def swap01 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Polyad3 S :=
  ofData P.c₁ P.c₀ P.c₂ P.hc₁ P.hc₀ P.hc₂ (S.pairColors.rev P.color₀₁) P.color₁₂ P.color₀₂

/-- Swap roles one and two of a polyad, exchanging the `(0, 1)` and `(0, 2)` pair colors and
reversing the `(1, 2)` pair color. -/
def swap12 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Polyad3 S :=
  ofData P.c₀ P.c₂ P.c₁ P.hc₀ P.hc₂ P.hc₁ P.color₀₂ P.color₀₁ (S.pairColors.rev P.color₁₂)

private theorem mem_support_swap01 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S)
    (x : {x : Fin 3 → V // Injective x}) :
    x ∈ P.swap01.support ↔ triplePerm (Equiv.swap 0 1) x ∈ P.support := by
  simp only [mem_support, swap01, ofData_c₀, ofData_c₁, ofData_c₂, ofData_color₀₁,
    ofData_color₀₂, ofData_color₁₂, triplePerm, Equiv.coe_fn_mk, Function.comp_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  rw [S.pairColors.colorOfPair_swap_eq_some_iff]
  tauto

private theorem mem_support_swap12 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S)
    (x : {x : Fin 3 → V // Injective x}) :
    x ∈ P.swap12.support ↔ triplePerm (Equiv.swap 1 2) x ∈ P.support := by
  simp only [mem_support, swap12, ofData_c₀, ofData_c₁, ofData_c₂, ofData_color₀₁,
    ofData_color₀₂, ofData_color₁₂, triplePerm, Equiv.coe_fn_mk, Function.comp_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
  rw [S.pairColors.colorOfPair_swap_eq_some_iff]
  tauto

private theorem support_swap01 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    P.swap01.support = P.support.map (triplePerm (Equiv.swap 0 1)).symm.toEmbedding := by
  ext x
  rw [mem_support_swap01, mem_map_equiv]
  rfl

private theorem support_swap12 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    P.swap12.support = P.support.map (triplePerm (Equiv.swap 1 2)).symm.toEmbedding := by
  ext x
  rw [mem_support_swap12, mem_map_equiv]
  rfl

private theorem relativeDensity_swap01 [DecidableEq κ] (H : Colored3Graph κ V) (c : κ)
    {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    H.relativeDensity c P.swap01 = H.relativeDensity c P := by
  rw [Colored3Graph.relativeDensity_def, Colored3Graph.relativeDensity_def, support_swap01]
  exact relDensityOn_map_triplePerm H c (Equiv.swap 0 1).symm P.support

private theorem relativeDensity_swap12 [DecidableEq κ] (H : Colored3Graph κ V) (c : κ)
    {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    H.relativeDensity c P.swap12 = H.relativeDensity c P := by
  rw [Colored3Graph.relativeDensity_def, Colored3Graph.relativeDensity_def, support_swap12]
  exact relDensityOn_map_triplePerm H c (Equiv.swap 1 2).symm P.support

private noncomputable def subpolyadSwap01 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P.swap01) : Subpolyad3 P where
  pair₀₁ := W.pair₀₁.image pairSwap
  pair₀₂ := W.pair₁₂
  pair₁₂ := W.pair₀₂
  pair₀₁_sub := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    have hp' := (mem_pairSupport₀₁ _ p).1 (W.pair₀₁_sub hp)
    simp only [swap01, ofData_c₀, ofData_c₁, ofData_color₀₁] at hp'
    rw [mem_pairSupport₀₁]
    exact ⟨hp'.2.1, hp'.1, by
      have hrev := S.pairColors.color_rev p
      change S.pairColors.color (pairSwap p) = _ at hrev
      rw [hrev, hp'.2.2, S.pairColors.rev_rev]⟩
  pair₀₂_sub := fun p hp ↦ by
    have hp' := (mem_pairSupport₁₂ _ p).1 (W.pair₁₂_sub hp)
    simp only [swap01, ofData_c₁, ofData_c₂, ofData_color₁₂] at hp'
    exact (mem_pairSupport₀₂ _ p).2 hp'
  pair₁₂_sub := fun p hp ↦ by
    have hp' := (mem_pairSupport₀₂ _ p).1 (W.pair₀₂_sub hp)
    simp only [swap01, ofData_c₀, ofData_c₂, ofData_color₀₂] at hp'
    exact (mem_pairSupport₁₂ _ p).2 hp'

private theorem support_subpolyadSwap01 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P.swap01) :
    (subpolyadSwap01 W).support =
      W.support.map (triplePerm (Equiv.swap 0 1)).toEmbedding := by
  have hs2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  ext x
  rw [mem_map]
  constructor
  · intro hx
    rw [Subpolyad3.mem_support_iff_coordPair_mem] at hx
    refine ⟨triplePerm (Equiv.swap 0 1) x, ?_, Subtype.ext (by ext i; simp [triplePerm])⟩
    rw [Subpolyad3.mem_support_iff_coordPair_mem]
    have h01 : pairSwap (coordPair (triplePerm (Equiv.swap 0 1) x) 0 1 (by decide)) =
        coordPair x 0 1 (by decide) := Subtype.ext (by simp [pairSwap, coe_coordPair, triplePerm])
    have h02 : coordPair (triplePerm (Equiv.swap 0 1) x) 0 2 (by decide) =
        coordPair x 1 2 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs2])
    have h12 : coordPair (triplePerm (Equiv.swap 0 1) x) 1 2 (by decide) =
        coordPair x 0 2 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs2])
    obtain ⟨p, hp, hp_eq⟩ := mem_image.1 hx.1
    have hp_eq' : p = coordPair (triplePerm (Equiv.swap 0 1) x) 0 1 (by decide) :=
      pairSwap_involutive.injective (hp_eq.trans h01.symm)
    exact ⟨hp_eq' ▸ hp, h02.symm ▸ hx.2.2, h12.symm ▸ hx.2.1⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Subpolyad3.mem_support_iff_coordPair_mem] at hy ⊢
    simp only [Equiv.toEmbedding_apply]
    have h01 : coordPair (triplePerm (Equiv.swap 0 1) y) 0 1 (by decide) =
        pairSwap (coordPair y 0 1 (by decide)) :=
      Subtype.ext (by simp [pairSwap, coe_coordPair, triplePerm])
    have h02 : coordPair (triplePerm (Equiv.swap 0 1) y) 0 2 (by decide) =
        coordPair y 1 2 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs2])
    have h12 : coordPair (triplePerm (Equiv.swap 0 1) y) 1 2 (by decide) =
        coordPair y 0 2 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs2])
    exact ⟨h01 ▸ mem_image_of_mem _ hy.1, h02 ▸ hy.2.2, h12 ▸ hy.2.1⟩

private noncomputable def subpolyadSwap12 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P.swap12) : Subpolyad3 P where
  pair₀₁ := W.pair₀₂
  pair₀₂ := W.pair₀₁
  pair₁₂ := W.pair₁₂.image pairSwap
  pair₀₁_sub := fun p hp ↦ by
    have hp' := (mem_pairSupport₀₂ _ p).1 (W.pair₀₂_sub hp)
    simp only [swap12, ofData_c₀, ofData_c₂, ofData_color₀₂] at hp'
    exact (mem_pairSupport₀₁ _ p).2 hp'
  pair₀₂_sub := fun p hp ↦ by
    have hp' := (mem_pairSupport₀₁ _ p).1 (W.pair₀₁_sub hp)
    simp only [swap12, ofData_c₀, ofData_c₁, ofData_color₀₁] at hp'
    exact (mem_pairSupport₀₂ _ p).2 hp'
  pair₁₂_sub := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    have hp' := (mem_pairSupport₁₂ _ p).1 (W.pair₁₂_sub hp)
    simp only [swap12, ofData_c₁, ofData_c₂, ofData_color₁₂] at hp'
    rw [mem_pairSupport₁₂]
    exact ⟨hp'.2.1, hp'.1, by
      have hrev := S.pairColors.color_rev p
      change S.pairColors.color (pairSwap p) = _ at hrev
      rw [hrev, hp'.2.2, S.pairColors.rev_rev]⟩

private theorem support_subpolyadSwap12 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S}
    (W : Subpolyad3 P.swap12) :
    (subpolyadSwap12 W).support =
      W.support.map (triplePerm (Equiv.swap 1 2)).toEmbedding := by
  have hs0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  ext x
  rw [mem_map]
  constructor
  · intro hx
    rw [Subpolyad3.mem_support_iff_coordPair_mem] at hx
    refine ⟨triplePerm (Equiv.swap 1 2) x, ?_, Subtype.ext (by ext i; simp [triplePerm])⟩
    rw [Subpolyad3.mem_support_iff_coordPair_mem]
    have h01 : coordPair (triplePerm (Equiv.swap 1 2) x) 0 1 (by decide) =
        coordPair x 0 2 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs0])
    have h02 : coordPair (triplePerm (Equiv.swap 1 2) x) 0 2 (by decide) =
        coordPair x 0 1 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs0])
    have h12 : pairSwap (coordPair (triplePerm (Equiv.swap 1 2) x) 1 2 (by decide)) =
        coordPair x 1 2 (by decide) := Subtype.ext (by simp [pairSwap, coe_coordPair, triplePerm])
    obtain ⟨p, hp, hp_eq⟩ := mem_image.1 hx.2.2
    have hp_eq' : p = coordPair (triplePerm (Equiv.swap 1 2) x) 1 2 (by decide) :=
      pairSwap_involutive.injective (hp_eq.trans h12.symm)
    exact ⟨h01.symm ▸ hx.2.1, h02.symm ▸ hx.1, hp_eq' ▸ hp⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Subpolyad3.mem_support_iff_coordPair_mem] at hy ⊢
    simp only [Equiv.toEmbedding_apply]
    have h01 : coordPair (triplePerm (Equiv.swap 1 2) y) 0 1 (by decide) =
        coordPair y 0 2 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs0])
    have h02 : coordPair (triplePerm (Equiv.swap 1 2) y) 0 2 (by decide) =
        coordPair y 0 1 (by decide) := Subtype.ext (by simp [coe_coordPair, triplePerm, hs0])
    have h12 : coordPair (triplePerm (Equiv.swap 1 2) y) 1 2 (by decide) =
        pairSwap (coordPair y 1 2 (by decide)) :=
      Subtype.ext (by simp [pairSwap, coe_coordPair, triplePerm])
    exact ⟨h01 ▸ hy.2.1, h02 ▸ hy.1, h12 ▸ mem_image_of_mem _ hy.2.2⟩

private theorem swap01_involutive {S : PairSkeleton3 κ₂ V} :
    Involutive (swap01 (S := S)) := fun P ↦ by
  ext <;> simp [swap01]

private theorem swap12_involutive {S : PairSkeleton3 κ₂ V} :
    Involutive (swap12 (S := S)) := fun P ↦ by
  ext <;> simp [swap12]

private theorem isTopRegularOverPolyad_swap01_iff [DecidableEq κ] (H : Colored3Graph κ V)
    {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (δ : ℝ) :
    H.IsTopRegularOverPolyad P.swap01 δ 1 ↔ H.IsTopRegularOverPolyad P δ 1 := by
  have imp {Q : Polyad3 S} (h : H.IsTopRegularOverPolyad Q δ 1) :
      H.IsTopRegularOverPolyad Q.swap01 δ 1 := by
    rw [Colored3Graph.isTopRegularOverPolyad_one_iff] at h ⊢
    intro c W hW
    rw [support_swap01, card_map] at hW
    have hW' : δ * #Q.support ≤ #(subpolyadSwap01 W).support := by
      rwa [support_subpolyadSwap01, card_map]
    have hdev := h c (subpolyadSwap01 W) hW'
    rwa [support_subpolyadSwap01, relDensityOn_map_triplePerm,
      ← relativeDensity_swap01 H c Q] at hdev
  exact ⟨fun h ↦ swap01_involutive P ▸ imp h, imp⟩

private theorem isTopRegularOverPolyad_swap12_iff [DecidableEq κ] (H : Colored3Graph κ V)
    {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) (δ : ℝ) :
    H.IsTopRegularOverPolyad P.swap12 δ 1 ↔ H.IsTopRegularOverPolyad P δ 1 := by
  have imp {Q : Polyad3 S} (h : H.IsTopRegularOverPolyad Q δ 1) :
      H.IsTopRegularOverPolyad Q.swap12 δ 1 := by
    rw [Colored3Graph.isTopRegularOverPolyad_one_iff] at h ⊢
    intro c W hW
    rw [support_swap12, card_map] at hW
    have hW' : δ * #Q.support ≤ #(subpolyadSwap12 W).support := by
      rwa [support_subpolyadSwap12, card_map]
    have hdev := h c (subpolyadSwap12 W) hW'
    rwa [support_subpolyadSwap12, relDensityOn_map_triplePerm,
      ← relativeDensity_swap12 H c Q] at hdev
  exact ⟨fun h ↦ swap12_involutive P ▸ imp h, imp⟩

private theorem coarsen_swap01 {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart = S.vertexPart) {f : κ₂' → κ₂}
    (hfrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) (Q : Polyad3 T) :
    Q.swap01.coarsen hV.le f = (Q.coarsen hV.le f).swap01 := by
  ext <;> simp [swap01, hfrev]

private theorem coarsen_swap12 {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart = S.vertexPart) {f : κ₂' → κ₂}
    (hfrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c)) (Q : Polyad3 T) :
    Q.swap12.coarsen hV.le f = (Q.coarsen hV.le f).swap12 := by
  ext <;> simp [swap12, hfrev]

/-- Every transversal polyad `Q'` over `T` can be role-permuted to a canonical polyad `Q` over `T`
with the same support cardinality, the same fine and coarse relative color densities, and the same
rank-one top regularity in every colored 3-graph. -/
theorem exists_isCanonical_of_isTransversal [DecidableEq κ]
    {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V} (hV : T.vertexPart = S.vertexPart)
    {f : κ₂' → κ₂} (hfrev : ∀ c, f (T.pairColors.rev c) = S.pairColors.rev (f c))
    {k : ℕ} (idx : T.vertexPart.parts ≃ Fin k) {Q' : Polyad3 T} (hQ' : Q'.IsTransversal) :
    ∃ Q : Polyad3 T, Q.IsCanonical idx ∧ #Q.support = #Q'.support ∧
      (∀ (H : Colored3Graph κ V) (c : κ), H.relativeDensity c Q = H.relativeDensity c Q') ∧
      (∀ (H : Colored3Graph κ V) (c : κ),
        H.relativeDensity c (Q.coarsen hV.le f) = H.relativeDensity c (Q'.coarsen hV.le f)) ∧
      (∀ (H : Colored3Graph κ V) (δ : ℝ),
        H.IsTopRegularOverPolyad Q δ 1 ↔ H.IsTopRegularOverPolyad Q' δ 1) := by
  let EquivProp (A B : Polyad3 T) : Prop :=
    #A.support = #B.support ∧
      (∀ (H : Colored3Graph κ V) (c : κ), H.relativeDensity c A = H.relativeDensity c B) ∧
      (∀ (H : Colored3Graph κ V) (c : κ),
        H.relativeDensity c (A.coarsen hV.le f) = H.relativeDensity c (B.coarsen hV.le f)) ∧
      (∀ (H : Colored3Graph κ V) (δ : ℝ),
        H.IsTopRegularOverPolyad A δ 1 ↔ H.IsTopRegularOverPolyad B δ 1)
  have hrefl (A : Polyad3 T) : EquivProp A A := ⟨rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ .rfl⟩
  have htrans {A B G : Polyad3 T} (h1 : EquivProp A B) (h2 : EquivProp B G) : EquivProp A G :=
    ⟨h1.1.trans h2.1, fun H c ↦ (h1.2.1 H c).trans (h2.2.1 H c),
      fun H c ↦ (h1.2.2.1 H c).trans (h2.2.2.1 H c),
      fun H δ ↦ (h1.2.2.2 H δ).trans (h2.2.2.2 H δ)⟩
  have hswap01 (A : Polyad3 T) : EquivProp A.swap01 A :=
    ⟨by rw [support_swap01, card_map], fun H c ↦ relativeDensity_swap01 H c A,
      fun H c ↦ by rw [coarsen_swap01 hV hfrev, relativeDensity_swap01],
      fun H δ ↦ isTopRegularOverPolyad_swap01_iff H A δ⟩
  have hswap12 (A : Polyad3 T) : EquivProp A.swap12 A :=
    ⟨by rw [support_swap12, card_map], fun H c ↦ relativeDensity_swap12 H c A,
      fun H c ↦ by rw [coarsen_swap12 hV hfrev, relativeDensity_swap12],
      fun H δ ↦ isTopRegularOverPolyad_swap12_iff H A δ⟩
  set i₀ := idx ⟨Q'.c₀, Q'.hc₀⟩
  set i₁ := idx ⟨Q'.c₁, Q'.hc₁⟩
  set i₂ := idx ⟨Q'.c₂, Q'.hc₂⟩
  have hne01 : i₀.val ≠ i₁.val := fun h ↦
    hQ'.1 (congrArg Subtype.val (idx.injective (Fin.ext h)))
  have hne02 : i₀.val ≠ i₂.val := fun h ↦
    hQ'.2.1 (congrArg Subtype.val (idx.injective (Fin.ext h)))
  have hne12 : i₁.val ≠ i₂.val := fun h ↦
    hQ'.2.2 (congrArg Subtype.val (idx.injective (Fin.ext h)))
  by_cases h1 : i₀ < i₁ ∧ i₁ < i₂
  · exact ⟨Q', h1, hrefl Q'⟩
  by_cases h2 : i₁ < i₀ ∧ i₀ < i₂
  · exact ⟨Q'.swap01, by simpa [IsCanonical, swap01] using h2, hswap01 Q'⟩
  by_cases h3 : i₀ < i₂ ∧ i₂ < i₁
  · exact ⟨Q'.swap12, by simpa [IsCanonical, swap12] using h3, hswap12 Q'⟩
  by_cases h4 : i₁ < i₂ ∧ i₂ < i₀
  · exact ⟨Q'.swap01.swap12, by simpa [IsCanonical, swap01, swap12] using h4,
      htrans (hswap12 _) (hswap01 _)⟩
  by_cases h5 : i₂ < i₀ ∧ i₀ < i₁
  · exact ⟨Q'.swap12.swap01, by simpa [IsCanonical, swap01, swap12] using h5,
      htrans (hswap01 _) (hswap12 _)⟩
  have h6 : i₂ < i₁ ∧ i₁ < i₀ := by
    simp only [Fin.lt_def, not_and_or, not_lt] at h1 h2 h3 h4 h5 ⊢
    omega
  exact ⟨Q'.swap01.swap12.swap01, by simpa [IsCanonical, swap01, swap12] using h6,
    htrans (hswap01 _) (htrans (hswap12 _) (hswap01 _))⟩

end Polyad3

end TauCeti
