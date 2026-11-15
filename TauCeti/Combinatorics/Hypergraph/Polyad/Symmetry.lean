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

* `TauCeti.card_subpolyad3_le`: a polyad on `V` has at most `2 ^ (3 * |V| ^ 2)` subpolyads.
* `TauCeti.Polyad3.injOn_tripleSet_support`: `tripleSet` is injective on transversal supports.
* `TauCeti.Polyad3.disjoint_image_tripleSet_of_isCanonical`: distinct canonical polyads have
  disjoint unordered-triple supports.
* `TauCeti.Polyad3.exists_isCanonical_of_isTransversal`: canonicalization of transversal polyads.
-/

public section

open Finset Function

namespace TauCeti

/-- Every polyad on `V` has at most `2 ^ (3 * |V| ^ 2)` subpolyads. -/
theorem card_subpolyad3_le {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} (P :
    Polyad3 S) : Fintype.card (Subpolyad3 P) ≤ 2 ^ (3 * Fintype.card V ^ 2) := by
  classical
  let g : Subpolyad3 P → ↥(P.pairSupport₀₁.powerset ×ˢ P.pairSupport₀₂.powerset ×ˢ
      P.pairSupport₁₂.powerset) := fun W ↦ ⟨(W.pair₀₁, W.pair₀₂, W.pair₁₂), mem_product.2
      ⟨mem_powerset.2 W.pair₀₁_sub, mem_product.2 ⟨mem_powerset.2 W.pair₀₂_sub, mem_powerset.2
      W.pair₁₂_sub⟩⟩⟩
  have hcard := Fintype.card_le_of_injective g fun W₁ W₂ h ↦ by
    have h' := Subtype.ext_iff.1 h; simp only [g, Prod.mk.injEq] at h'
    exact Subpolyad3.ext_data h'.1 h'.2.1 h'.2.2
  have hpair (A : Finset {p : V × V // p.1 ≠ p.2}) : #A ≤ Fintype.card V ^ 2 := (card_le_univ
    A).trans ((Fintype.card_subtype_le _).trans_eq (by rw [Fintype.card_prod, sq]))
  rw [Fintype.card_coe, card_product, card_product, card_powerset, card_powerset, card_powerset, ←
    pow_add, ← pow_add] at hcard
  have := hpair P.pairSupport₀₁; have := hpair P.pairSupport₀₂; have := hpair P.pairSupport₁₂
  exact hcard.trans (Nat.pow_le_pow_right two_pos (by omega))
/-- The unordered 3-element subset of `V` determined by an injective triple `Fin 3 → V`. -/
def tripleSet {V : Type*} (x : {x : Fin 3 → V // Injective x}) : Set.powersetCard V 3 :=
  Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩
/-- `tripleSet` is `Set.powersetCard.ofFinEmb 3 V` applied to the underlying embedding. -/
theorem tripleSet_def {V : Type*} (x : {x : Fin 3 → V // Injective x}) : tripleSet x =
    Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ := (rfl)
/-- A vertex belongs to `tripleSet x` iff it is one of the three coordinates of `x`. -/
@[simp] theorem mem_tripleSet_iff {V : Type*} {x : {x : Fin 3 → V // Injective x}} {v : V} : v ∈
    (tripleSet x).1 ↔ ∃ i : Fin 3, x.1 i = v := by simp [tripleSet]
private def pairSwap {V : Type*} : {p : V × V // p.1 ≠ p.2} ≃ {p : V × V // p.1 ≠ p.2} := ⟨fun p ↦
  ⟨p.val.swap, p.property.symm⟩, fun p ↦ ⟨p.val.swap, p.property.symm⟩, fun _ ↦ Subtype.ext
  (Prod.swap_swap _), fun _ ↦ Subtype.ext (Prod.swap_swap _)⟩
private def triplePerm {V : Type*} (σ : Equiv.Perm (Fin 3)) : {x : Fin 3 → V // Injective x} ≃ {x :
    Fin 3 → V // Injective x} := ⟨fun x ↦ ⟨x.1 ∘ σ, x.2.comp σ.injective⟩, fun x ↦ ⟨x.1 ∘ σ.symm,
    x.2.comp σ.symm.injective⟩, fun _ ↦ Subtype.ext (by ext; simp), fun _ ↦ Subtype.ext
    (by ext; simp)⟩
private theorem tripleSet_triplePerm {V : Type*} (σ : Equiv.Perm (Fin 3)) (x : {x : Fin 3 → V //
    Injective x}) : tripleSet (triplePerm σ x) = tripleSet x := by
  apply Subtype.ext; ext v; simp only [tripleSet, triplePerm, Equiv.coe_fn_mk, Function.comp_apply,
    Set.powersetCard.val_ofFinEmb, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨σ i, hi⟩, fun ⟨j, hj⟩ ↦ ⟨σ.symm j, by simpa using hj⟩⟩
private theorem relDensityOn_map_triplePerm {κ V : Type*} [DecidableEq κ] (H : Colored3Graph κ V)
    (c : κ) (σ : Equiv.Perm (Fin 3)) (A : Finset {x : Fin 3 → V // Injective x}) : H.relDensityOn c
    (A.map (triplePerm σ).toEmbedding) = H.relDensityOn c A := by
  rw [Colored3Graph.relDensityOn_def, Colored3Graph.relDensityOn_def, filter_map, card_map,
    card_map]; congr 3; ext x
  simp only [Function.comp_apply, Equiv.toEmbedding_apply, ← tripleSet_def, tripleSet_triplePerm]

namespace Polyad3
variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V]
/-- A polyad is *transversal* when its three vertex cells are pairwise distinct. -/
def IsTransversal {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Prop := P.c₀ ≠ P.c₁ ∧ P.c₀ ≠ P.c₂ ∧
  P.c₁ ≠ P.c₂
/-- Unfolded form of `Polyad3.IsTransversal`. -/
theorem isTransversal_iff {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} : P.IsTransversal ↔ P.c₀ ≠ P.c₁
    ∧ P.c₀ ≠ P.c₂ ∧ P.c₁ ≠ P.c₂ := Iff.rfl
/-- Coarsening between skeletons with the same vertex partition preserves transversality. -/
theorem isTransversal_coarsen_iff {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V} (hV :
    T.vertexPart = S.vertexPart) (f : κ₂' → κ₂) (Q : Polyad3 T) : (Q.coarsen hV.le f).IsTransversal
    ↔ Q.IsTransversal := by
  have hcell (A) (hA : A ∈ T.vertexPart.parts) : (Finpartition.refinementParent hV.le ⟨A, hA⟩).val
      = A := congrArg Subtype.val ((Finpartition.refinementParent_eq_iff hV.le (A := ⟨A, hV ▸
      hA⟩)).2 le_rfl)
  simp [IsTransversal, hcell]
/-- On the support of a transversal polyad, `tripleSet` is injective. -/
theorem injOn_tripleSet_support {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (hP : P.IsTransversal) :
    Set.InjOn (tripleSet (V := V)) P.support := by
  intro x hx y hy hxy; rw [Finset.mem_coe, P.mem_support] at hx hy
  have hr (v : V) : (∃ i, x.1 i = v) ↔ (∃ j, y.1 j = v) := by
    simpa only [mem_tripleSet_iff] using (congrArg (fun s : Set.powersetCard V 3 ↦ v ∈ s.1)
      hxy).to_iff
  have hd01 := disjoint_left.1 (S.vertexPart.disjoint P.hc₀ P.hc₁ hP.1)
  have hd02 := disjoint_left.1 (S.vertexPart.disjoint P.hc₀ P.hc₂ hP.2.1)
  have hd12 := disjoint_left.1 (S.vertexPart.disjoint P.hc₁ P.hc₂ hP.2.2)
  apply Subtype.ext; ext i; fin_cases i
  · obtain ⟨j, hj⟩ := (hr (x.1 0)).1 ⟨0, rfl⟩; fin_cases j
    exacts [hj.symm, (hd01 hx.1 (hj ▸ hy.2.1)).elim, (hd02 hx.1 (hj ▸ hy.2.2.1)).elim]
  · obtain ⟨j, hj⟩ := (hr (x.1 1)).1 ⟨1, rfl⟩; fin_cases j
    exacts [(hd01 hy.1 (hj.symm ▸ hx.2.1)).elim, hj.symm, (hd12 hx.2.1 (hj ▸ hy.2.2.1)).elim]
  · obtain ⟨j, hj⟩ := (hr (x.1 2)).1 ⟨2, rfl⟩; fin_cases j
    exacts [(hd02 hy.1 (hj.symm ▸ hx.2.2.1)).elim, (hd12 hy.2.1 (hj.symm ▸ hx.2.2.1)).elim, hj.symm]
open Classical in
/-- Any subset of a transversal polyad support has the same size as its `tripleSet` image. -/
theorem card_image_tripleSet_of_subset {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (hP :
    P.IsTransversal) {A : Finset {x : Fin 3 → V // Injective x}} (hA : A ⊆ P.support) : #(A.image
    tripleSet) = #A := card_image_of_injOn ((injOn_tripleSet_support hP).mono hA)
open Classical in
/-- On a subset `A` of a transversal polyad support, the `c`-colored `tripleSet` image count equals
`H.relDensityOn c A * #A`. -/
theorem card_filter_image_tripleSet_eq_mul_relDensityOn [DecidableEq κ] (H : Colored3Graph κ V) (c
    : κ) {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (hP : P.IsTransversal) {A : Finset {x : Fin 3 → V
    // Injective x}} (hA : A ⊆ P.support) : (#{s ∈ A.image tripleSet | H.color s = c} : ℝ) =
    (H.relDensityOn c A : ℝ) * #A := by
  rw [← show ({x ∈ A | H.color (tripleSet x) = c}).image tripleSet = {s ∈ A.image tripleSet |
      H.color s = c} by
    ext s; simp only [mem_image, mem_filter]
    exact ⟨fun ⟨x, ⟨hx, hc⟩, hxs⟩ ↦ ⟨⟨x, hx, hxs⟩, hxs ▸ hc⟩, fun ⟨⟨x, hx, hxs⟩, hc⟩ ↦ ⟨x, ⟨hx,
      hxs.symm ▸ hc⟩, hxs⟩⟩,
    card_image_of_injOn ((injOn_tripleSet_support hP).mono ((filter_subset _ A).trans hA))]
  exact_mod_cast (H.relDensityOn_mul_card c A).symm
/-- A polyad is *canonical* with respect to `idx` when `idx c₀ < idx c₁ < idx c₂`. -/
def IsCanonical {S : PairSkeleton3 κ₂ V} {k : ℕ} (idx : S.vertexPart.parts ≃ Fin k) (P : Polyad3 S)
    : Prop := idx ⟨P.c₀, P.hc₀⟩ < idx ⟨P.c₁, P.hc₁⟩ ∧ idx ⟨P.c₁, P.hc₁⟩ < idx ⟨P.c₂, P.hc₂⟩
/-- Unfolded form of `Polyad3.IsCanonical`. -/
theorem isCanonical_iff {S : PairSkeleton3 κ₂ V} {k : ℕ} {idx : S.vertexPart.parts ≃ Fin k} {P :
    Polyad3 S} : P.IsCanonical idx ↔ idx ⟨P.c₀, P.hc₀⟩ < idx ⟨P.c₁, P.hc₁⟩ ∧ idx ⟨P.c₁, P.hc₁⟩ <
    idx ⟨P.c₂, P.hc₂⟩ := Iff.rfl
/-- Every canonical polyad is transversal. -/
theorem IsCanonical.isTransversal {S : PairSkeleton3 κ₂ V} {k : ℕ} {idx : S.vertexPart.parts ≃ Fin
    k} {P : Polyad3 S} (h : P.IsCanonical idx) : P.IsTransversal := ⟨fun e ↦ h.1.ne (congrArg idx
    (Subtype.ext e)), fun e ↦ (h.1.trans h.2).ne (congrArg idx (Subtype.ext e)), fun e ↦ h.2.ne
    (congrArg idx (Subtype.ext e))⟩
open Classical in
/-- Distinct canonical polyads over the same skeleton have disjoint unordered-triple supports. -/
theorem disjoint_image_tripleSet_of_isCanonical {S : PairSkeleton3 κ₂ V} {k : ℕ} {idx :
    S.vertexPart.parts ≃ Fin k} {P Q : Polyad3 S} (hP : P.IsCanonical idx) (hQ : Q.IsCanonical idx)
    (hne : P ≠ Q) : Disjoint (P.support.image tripleSet) (Q.support.image tripleSet) := by
  let ci (v : V) : Fin k := idx ⟨S.vertexPart.part v, S.vertexPart.part_mem.2 (mem_univ v)⟩
  have hmono {R : Polyad3 S} (hR : R.IsCanonical idx) {x} (hx : x ∈ R.support) : StrictMono fun i :
      Fin 3 ↦ ci (x.1 i) := by
    rw [R.mem_support] at hx
    have h0 : ci (x.1 0) = idx ⟨R.c₀, R.hc₀⟩ := congrArg idx (Subtype.ext
      (S.vertexPart.part_eq_of_mem R.hc₀ hx.1))
    have h1 : ci (x.1 1) = idx ⟨R.c₁, R.hc₁⟩ := congrArg idx (Subtype.ext
      (S.vertexPart.part_eq_of_mem R.hc₁ hx.2.1))
    have h2 : ci (x.1 2) = idx ⟨R.c₂, R.hc₂⟩ := congrArg idx (Subtype.ext
      (S.vertexPart.part_eq_of_mem R.hc₂ hx.2.2.1))
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [hR.1, hR.2, hR.1.trans hR.2]
  refine disjoint_left.2 fun s hsP hsQ ↦ hne ?_
  obtain ⟨x, hxP, rfl⟩ := mem_image.1 hsP; obtain ⟨y, hyQ, hxy⟩ := mem_image.1 hsQ
  have hx_m := hmono hP hxP; have hy_m := hmono hQ hyQ
  have hr (v : V) : (∃ i, y.1 i = v) ↔ (∃ j, x.1 j = v) := by
    simpa only [mem_tripleSet_iff] using (congrArg (fun u : Set.powersetCard V 3 ↦ v ∈ u.1)
      hxy).to_iff
  choose σ hσ using fun i : Fin 3 ↦ (hr (x.1 i)).2 ⟨i, rfl⟩
  have hσ_m : StrictMono σ := fun a b hab ↦ hy_m.lt_iff_lt.1 (by rw [hσ a, hσ b]; exact hx_m hab)
  have := hσ_m (by decide : (0 : Fin 3) < 1); have := hσ_m (by decide : (1 : Fin 3) < 2)
  have := (σ 0).isLt; have := (σ 1).isLt; have := (σ 2).isLt
  have hσ0 : σ 0 = 0 := Fin.ext (by omega); have hσ1 : σ 1 = 1 := Fin.ext (by omega)
  have hσ2 : σ 2 = 2 := Fin.ext (by omega)
  have hxy_eq : x = y := Subtype.ext <| funext fun i ↦ by
    fin_cases i; exacts [(hσ0 ▸ hσ 0).symm, (hσ1 ▸ hσ 1).symm, (hσ2 ▸ hσ 2).symm]
  exact (mem_support_iff_eq_ofTriple.1 (hxy_eq ▸ hxP)).trans (mem_support_iff_eq_ofTriple.1
    hyQ).symm
/-- Swap roles `0` and `1` of a polyad, updating the three directed pair colors. -/
def swap01 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Polyad3 S := ofData P.c₁ P.c₀ P.c₂ P.hc₁
  P.hc₀ P.hc₂ (S.pairColors.rev P.color₀₁) P.color₁₂ P.color₀₂
/-- Swap roles `1` and `2` of a polyad, updating the three directed pair colors. -/
def swap12 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : Polyad3 S := ofData P.c₀ P.c₂ P.c₁ P.hc₀
  P.hc₂ P.hc₁ P.color₀₂ P.color₀₁ (S.pairColors.rev P.color₁₂)
private theorem support_swap01 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : P.swap01.support =
    P.support.map (triplePerm (Equiv.swap 0 1)).toEmbedding := by
  ext x; rw [mem_map_equiv, show (triplePerm (Equiv.swap 0 1)).symm x = triplePerm (Equiv.swap 0 1)
    x from Subtype.ext (by ext; simp [triplePerm])]
  simp only [mem_support, swap01, ofData_c₀, ofData_c₁, ofData_c₂, ofData_color₀₁, ofData_color₀₂,
    ofData_color₁₂, triplePerm, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
    (by decide : (2 : Fin 3) ≠ 1)]
  rw [S.pairColors.colorOfPair_swap_eq_some_iff]; tauto
private theorem support_swap12 {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) : P.swap12.support =
    P.support.map (triplePerm (Equiv.swap 1 2)).toEmbedding := by
  ext x; rw [mem_map_equiv, show (triplePerm (Equiv.swap 1 2)).symm x = triplePerm (Equiv.swap 1 2)
    x from Subtype.ext (by ext; simp [triplePerm])]
  simp only [mem_support, swap12, ofData_c₀, ofData_c₁, ofData_c₂, ofData_color₀₁, ofData_color₀₂,
    ofData_color₁₂, triplePerm, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2)]
  rw [S.pairColors.colorOfPair_swap_eq_some_iff]; tauto
private def subpolyadSwap01 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (W : Subpolyad3 P.swap01) :
    Subpolyad3 P := ⟨W.pair₀₁.map pairSwap.toEmbedding, W.pair₁₂, W.pair₀₂, fun q hq ↦ by
      obtain ⟨p, hp, rfl⟩ := mem_map.1 hq; have hp' := (mem_pairSupport₀₁ _ p).1 (W.pair₀₁_sub hp)
      simp only [swap01, ofData_c₀, ofData_c₁, ofData_color₀₁] at hp'
      exact (mem_pairSupport₀₁ _ _).2 ⟨hp'.2.1, hp'.1,
        by simpa [pairSwap, S.pairColors.color_rev] using congrArg S.pairColors.rev hp'.2.2⟩,
    fun p hp ↦ by simpa [mem_pairSupport₀₂, mem_pairSupport₁₂, swap01] using W.pair₁₂_sub hp,
    fun p hp ↦ by simpa [mem_pairSupport₁₂, mem_pairSupport₀₂, swap01] using W.pair₀₂_sub hp⟩
private theorem support_subpolyadSwap01 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (W : Subpolyad3
    P.swap01) : (subpolyadSwap01 W).support = W.support.map (triplePerm (Equiv.swap 0
    1)).toEmbedding := by
  have h2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := (by decide)
  ext x; simp only [mem_map_equiv, Subpolyad3.mem_support_iff_coordPair_mem, subpolyadSwap01, show
    (triplePerm (Equiv.swap 0 1)).symm x = triplePerm (Equiv.swap 0 1) x from Subtype.ext
    (by ext; simp [triplePerm]), show pairSwap.symm (coordPair x 0 1 (by decide)) = coordPair
    (triplePerm (Equiv.swap 0 1) x) 0 1 (by decide) from Subtype.ext
    (by simp [pairSwap, coe_coordPair, triplePerm]), show coordPair (triplePerm (Equiv.swap 0 1) x)
    0 2 (by decide) = coordPair x 1 2 (by decide) from Subtype.ext
    (by simp [coe_coordPair, triplePerm, h2]), show coordPair (triplePerm (Equiv.swap 0 1) x) 1 2
    (by decide) = coordPair x 0 2 (by decide) from Subtype.ext
    (by simp [coe_coordPair, triplePerm, h2])]
  tauto
private def subpolyadSwap12 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (W : Subpolyad3 P.swap12) :
    Subpolyad3 P := ⟨W.pair₀₂, W.pair₀₁, W.pair₁₂.map pairSwap.toEmbedding, fun p hp ↦
    by simpa [mem_pairSupport₀₁, mem_pairSupport₀₂, swap12] using W.pair₀₂_sub hp, fun p hp ↦ by
        simpa [mem_pairSupport₀₂, mem_pairSupport₀₁, swap12] using W.pair₀₁_sub hp, fun q hq ↦ by
      obtain ⟨p, hp, rfl⟩ := mem_map.1 hq; have hp' := (mem_pairSupport₁₂ _ p).1 (W.pair₁₂_sub hp)
      simp only [swap12, ofData_c₁, ofData_c₂, ofData_color₁₂] at hp'
      exact (mem_pairSupport₁₂ _ _).2 ⟨hp'.2.1, hp'.1,
        by simpa [pairSwap, S.pairColors.color_rev] using congrArg S.pairColors.rev hp'.2.2⟩⟩
private theorem support_subpolyadSwap12 {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} (W : Subpolyad3
    P.swap12) : (subpolyadSwap12 W).support = W.support.map (triplePerm (Equiv.swap 1
    2)).toEmbedding := by
  have h0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := (by decide)
  ext x; simp only [mem_map_equiv, Subpolyad3.mem_support_iff_coordPair_mem, subpolyadSwap12, show
    (triplePerm (Equiv.swap 1 2)).symm x = triplePerm (Equiv.swap 1 2) x from Subtype.ext
    (by ext; simp [triplePerm]), show coordPair (triplePerm (Equiv.swap 1 2) x) 0 1 (by decide) =
    coordPair x 0 2 (by decide) from Subtype.ext (by simp [coe_coordPair, triplePerm, h0]), show
    coordPair (triplePerm (Equiv.swap 1 2) x) 0 2 (by decide) = coordPair x 0 1 (by decide) from
    Subtype.ext (by simp [coe_coordPair, triplePerm, h0]), show pairSwap.symm (coordPair x 1 2
    (by decide)) = coordPair (triplePerm (Equiv.swap 1 2) x) 1 2 (by decide) from Subtype.ext
    (by simp [pairSwap, coe_coordPair, triplePerm])]
  tauto
private theorem isTopRegularOverPolyad_of_inv {S : PairSkeleton3 κ₂ V} [DecidableEq κ] (H :
    Colored3Graph κ V) {φ : Polyad3 S → Polyad3 S} (hinv : Involutive φ) (σ : Equiv.Perm (Fin 3))
    (hsup : ∀ Q, (φ Q).support = Q.support.map (triplePerm σ).toEmbedding) (hsub : ∀ {Q} (W :
    Subpolyad3 (φ Q)), ∃ W' : Subpolyad3 Q, W'.support = W.support.map (triplePerm σ).toEmbedding)
    (P : Polyad3 S) (δ : ℝ) : H.IsTopRegularOverPolyad (φ P) δ 1 ↔ H.IsTopRegularOverPolyad P δ 1
    := by
  have imp {Q : Polyad3 S} (h : H.IsTopRegularOverPolyad Q δ 1) : H.IsTopRegularOverPolyad (φ Q) δ
      1 := by
    rw [Colored3Graph.isTopRegularOverPolyad_one_iff] at h ⊢
    intro c W hW; obtain ⟨W', hW'⟩ := hsub W; rw [hsup, card_map] at hW
    have hdev := h c W' (by rwa [hW', card_map])
    rw [Colored3Graph.relativeDensity_def, hsup Q, relDensityOn_map_triplePerm, ←
      Colored3Graph.relativeDensity_def]
    rwa [hW', relDensityOn_map_triplePerm] at hdev
  exact ⟨fun h ↦ hinv P ▸ imp h, imp⟩
private theorem relativeDensity_of_support_map [DecidableEq κ] {α : Type*} {U : PairSkeleton3 α V}
    {A B : Polyad3 U} {σ} (hs : A.support = B.support.map (triplePerm σ).toEmbedding) (H :
    Colored3Graph κ V) (c : κ) : H.relativeDensity c A = H.relativeDensity c B := by
  rw [Colored3Graph.relativeDensity_def, Colored3Graph.relativeDensity_def, hs,
    relDensityOn_map_triplePerm]
/-- Every transversal polyad `Q'` over `T` is role-equivalent to a canonical polyad `Q` over `T`. -/
theorem exists_isCanonical_of_isTransversal [DecidableEq κ] {S : PairSkeleton3 κ₂ V} {T :
    PairSkeleton3 κ₂' V} (hV : T.vertexPart = S.vertexPart) {f : κ₂' → κ₂} (hfrev : ∀ c, f
    (T.pairColors.rev c) = S.pairColors.rev (f c)) {k : ℕ} (idx : T.vertexPart.parts ≃ Fin k) {Q' :
    Polyad3 T} (hQ' : Q'.IsTransversal) : ∃ Q : Polyad3 T, Q.IsCanonical idx ∧ #Q.support =
    #Q'.support ∧ (∀ (H : Colored3Graph κ V) (c : κ), H.relativeDensity c Q = H.relativeDensity c
    Q') ∧ (∀ (H : Colored3Graph κ V) (c : κ), H.relativeDensity c (Q.coarsen hV.le f) =
    H.relativeDensity c (Q'.coarsen hV.le f)) ∧ (∀ (H : Colored3Graph κ V) (δ : ℝ),
    H.IsTopRegularOverPolyad Q δ 1 ↔ H.IsTopRegularOverPolyad Q' δ 1) := by
  let EquivProp (A B : Polyad3 T) : Prop := #A.support = #B.support ∧ (∀ (H : Colored3Graph κ V) (c
    : κ), H.relativeDensity c A = H.relativeDensity c B) ∧ (∀ (H : Colored3Graph κ V) (c : κ),
    H.relativeDensity c (A.coarsen hV.le f) = H.relativeDensity c (B.coarsen hV.le f)) ∧ ∀ (H :
    Colored3Graph κ V) (δ : ℝ), H.IsTopRegularOverPolyad A δ 1 ↔ H.IsTopRegularOverPolyad B δ 1
  have htrans {A B G : Polyad3 T} (h1 : EquivProp A B) (h2 : EquivProp B G) : EquivProp A G :=
    ⟨h1.1.trans h2.1, fun H c ↦ (h1.2.1 H c).trans (h2.2.1 H c), fun H c ↦ (h1.2.2.1 H c).trans
    (h2.2.2.1 H c), fun H δ ↦ (h1.2.2.2 H δ).trans (h2.2.2.2 H δ)⟩
  have hswap01 (A : Polyad3 T) : EquivProp A.swap01 A :=
    ⟨by rw [support_swap01, card_map], relativeDensity_of_support_map (support_swap01 A), fun H c ↦
        by rw [show A.swap01.coarsen hV.le f = (A.coarsen hV.le f).swap01 by
        ext <;> simp [swap01, hfrev]]; exact relativeDensity_of_support_map (support_swap01 _) H c,
      fun H δ ↦ isTopRegularOverPolyad_of_inv H (fun P ↦ by ext <;> simp [swap01]) (Equiv.swap 0 1)
        support_swap01 (fun W ↦ ⟨subpolyadSwap01 W, support_subpolyadSwap01 W⟩) A δ⟩
  have hswap12 (A : Polyad3 T) : EquivProp A.swap12 A :=
    ⟨by rw [support_swap12, card_map], relativeDensity_of_support_map (support_swap12 A), fun H c ↦
        by rw [show A.swap12.coarsen hV.le f = (A.coarsen hV.le f).swap12 by
        ext <;> simp [swap12, hfrev]]; exact relativeDensity_of_support_map (support_swap12 _) H c,
      fun H δ ↦ isTopRegularOverPolyad_of_inv H (fun P ↦ by ext <;> simp [swap12]) (Equiv.swap 1 2)
        support_swap12 (fun W ↦ ⟨subpolyadSwap12 W, support_subpolyadSwap12 W⟩) A δ⟩
  set i₀ := idx ⟨Q'.c₀, Q'.hc₀⟩; set i₁ := idx ⟨Q'.c₁, Q'.hc₁⟩; set i₂ := idx ⟨Q'.c₂, Q'.hc₂⟩
  have h01 : i₀.val ≠ i₁.val := fun h ↦ hQ'.1 (congrArg Subtype.val (idx.injective (Fin.ext h)))
  have h02 : i₀.val ≠ i₂.val := fun h ↦ hQ'.2.1 (congrArg Subtype.val (idx.injective (Fin.ext h)))
  have h12 : i₁.val ≠ i₂.val := fun h ↦ hQ'.2.2 (congrArg Subtype.val (idx.injective (Fin.ext h)))
  by_cases h1 : i₀ < i₁ ∧ i₁ < i₂
  · exact ⟨Q', h1, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ .rfl⟩
  by_cases h2 : i₁ < i₀ ∧ i₀ < i₂
  · exact ⟨Q'.swap01, by simpa [IsCanonical, swap01] using h2, hswap01 Q'⟩
  by_cases h3 : i₀ < i₂ ∧ i₂ < i₁
  · exact ⟨Q'.swap12, by simpa [IsCanonical, swap12] using h3, hswap12 Q'⟩
  by_cases h4 : i₁ < i₂ ∧ i₂ < i₀
  · exact ⟨Q'.swap01.swap12,
      by simpa [IsCanonical, swap01, swap12] using h4, htrans (hswap12 _) (hswap01 _)⟩
  by_cases h5 : i₂ < i₀ ∧ i₀ < i₁
  · exact ⟨Q'.swap12.swap01,
      by simpa [IsCanonical, swap01, swap12] using h5, htrans (hswap01 _) (hswap12 _)⟩
  have h6 : i₂ < i₁ ∧ i₁ < i₀ := by
    simp only [Fin.lt_def, not_and_or, not_lt] at h1 h2 h3 h4 h5 ⊢; omega
  exact ⟨Q'.swap01.swap12.swap01,
    by simpa [IsCanonical, swap01, swap12] using h6, htrans (hswap01 _) (htrans (hswap12 _)
        (hswap01 _))⟩
end Polyad3
end TauCeti
