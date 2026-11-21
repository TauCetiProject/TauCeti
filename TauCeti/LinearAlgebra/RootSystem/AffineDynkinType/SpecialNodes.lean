/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
import TauCeti.Combinatorics.SimpleGraph.CycleGraph
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.IntegralNullVector

/-!
# Automorphisms and special nodes of affine simply-laced diagrams

A node of an affine Dynkin diagram whose mark equals `1` is a **special node** in the sense of
Bourbaki. Every graph automorphism of an affine simply-laced diagram preserves both its
generalized Cartan matrix (`TauCeti.AffineDynkinType.cartanMatrix_graph_iso_apply`) and its marks
(`TauCeti.AffineDynkinType.marks_graph_iso_apply`), `Ã₁` included. Conversely, on a valid diagram
the automorphism group acts transitively on the special nodes: every node of mark `1` can be moved
to `TauCeti.AffineDynkinType.affineNode` by a graph automorphism
(`TauCeti.AffineDynkinType.exists_graph_iso_apply_eq_affineNode`).

## Main results

* `TauCeti.AffineDynkinType.cartanMatrix_graph_iso_apply` and
  `TauCeti.AffineDynkinType.cartanMatrix_submatrix_graph_iso`: every graph automorphism preserves
  the generalized Cartan matrix, `Ã₁` included.
* `TauCeti.AffineDynkinType.marks_graph_iso_apply` and
  `TauCeti.AffineDynkinType.marks_comp_graph_iso`: every graph automorphism preserves the marks.
* `TauCeti.AffineDynkinType.exists_graph_iso_apply_eq_affineNode` and
  `TauCeti.AffineDynkinType.exists_graph_iso_apply_eq`: on a valid diagram, graph automorphisms
  act transitively on nodes of mark `1`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VI, §2, n° 3 and Planches I–IX.
* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Table Aff 1.
-/

public section

open Finset SimpleGraph

namespace TauCeti.AffineDynkinType

/-- **Every graph automorphism of an affine simply-laced diagram preserves its generalized Cartan
matrix**, `Ã₁` included. -/
@[simp]
theorem cartanMatrix_graph_iso_apply {t : AffineDynkinType} (σ : t.graph ≃g t.graph)
    (i j : Fin t.nodes) : t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j := by
  by_cases h : t = A 1
  · subst h
    simp only [cartanMatrix_A_one_apply, σ.injective.eq_iff]
  · have hg : t.IsGraphical := isGraphical_iff_ne_A_one.mpr h
    simp only [cartanMatrix_apply hg, σ.injective.eq_iff, σ.map_adj_iff]

/-- Reindexing the generalized Cartan matrix along a graph automorphism leaves it unchanged. -/
@[simp]
theorem cartanMatrix_submatrix_graph_iso {t : AffineDynkinType} (σ : t.graph ≃g t.graph) :
    t.cartanMatrix.submatrix σ σ = t.cartanMatrix :=
  Matrix.ext (cartanMatrix_graph_iso_apply σ)

/-- **Every graph automorphism of an affine simply-laced diagram preserves its marks.** -/
@[simp]
theorem marks_graph_iso_apply {t : AffineDynkinType} (σ : t.graph ≃g t.graph)
    (i : Fin t.nodes) : t.marks (σ i) = t.marks i := by
  by_cases ht : t.Valid
  · by_cases hg : t.IsGraphical
    · let a : Fin t.nodes → ℕ := fun k ↦ (t.marks k).toNat
      have ha_coe (k : Fin t.nodes) : (a k : ℤ) = t.marks k :=
        Int.toNat_of_nonneg (t.marks_pos k).le
      have ha_sum (k : Fin t.nodes) : ∑ j ∈ t.graph.neighborFinset k, a j = 2 * a k := by
        have hs := sum_marks_neighborFinset_eq_two_mul ht hg k
        simp_rw [← ha_coe] at hs
        exact_mod_cast hs
      have h1 : a t.affineNode = 1 := by
        exact_mod_cast (ha_coe t.affineNode).trans t.marks_affineNode
      have hgcd : univ.gcd a = 1 :=
        Nat.dvd_one.mp (h1 ▸ univ.gcd_dvd (f := a) (mem_univ t.affineNode))
      have heq := congrFun (σ.eq_gcd_smul_marks_comp ht hg ha_sum) i
      simpa only [hgcd, Nat.cast_one, one_smul, Function.comp_apply, ha_coe] using heq.symm
    · rw [isGraphical_iff_ne_A_one, not_not] at hg
      subst hg
      exact (marks_A_apply 1 (σ i)).trans (marks_A_apply 1 i).symm
  · cases t with
    | A n => exact (marks_A_apply n (σ i)).trans (marks_A_apply n i).symm
    | D n =>
        rw [valid_D, not_le] at ht
        have hn : n - 3 = 0 := by omega
        rw [marks_D_apply, marks_D_apply, hn]
        split_ifs <;> omega
    | E6 => exact (ht valid_E6).elim
    | E7 => exact (ht valid_E7).elim
    | E8 => exact (ht valid_E8).elim

/-- Composing the marks with a graph automorphism leaves them unchanged. -/
@[simp]
theorem marks_comp_graph_iso {t : AffineDynkinType} (σ : t.graph ≃g t.graph) :
    t.marks ∘ σ = t.marks :=
  funext (marks_graph_iso_apply σ)

/-- Translation by `-i` as an automorphism of `(A n).graph`, sending `i` to `0`. -/
private def isoSubRightA (n : ℕ) (i : Fin (A n).nodes) : (A n).graph ≃g (A n).graph where
  toEquiv := Equiv.subRight i
  map_rel_iff' {u v} := by rw [graph_A]; exact TauCeti.cycleGraph_sub_adj_iff i u v

private lemma dSwap_adj {n : ℕ} (hn : 4 ≤ n) {a b : Fin (D n).nodes}
    (h : (D n).graph.Adj a b) :
    (D n).graph.Adj
      (Equiv.swap (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩ a)
      (Equiv.swap (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩ b) := by
  have ha : (a : ℕ) < n + 1 := by simpa [nodes_D] using a.isLt
  have hb : (b : ℕ) < n + 1 := by simpa [nodes_D] using b.isLt
  have hs (x : Fin (D n).nodes) :
      ((Equiv.swap (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩ x :
          Fin (D n).nodes) : ℕ) =
        if (x : ℕ) = 0 then n - 1 else if (x : ℕ) = n - 1 then 0 else (x : ℕ) := by
    have hx0 : (x = 0) ↔ (x : ℕ) = 0 := by rw [Fin.ext_iff, Fin.val_zero]
    have hxn1 : (x = ⟨n - 1, by rw [nodes_D]; omega⟩) ↔ (x : ℕ) = n - 1 := Fin.ext_iff
    simp only [Equiv.swap_apply_def, hx0, hxn1]; split_ifs <;> simp
  have hadj_D (x y : Fin (D n).nodes) := graph_D_adj hn (i := x) (j := y)
  rw [hadj_D] at h ⊢
  rw [hs a, hs b]
  rcases h with h | h | h | h | h | h <;> (split_ifs <;> omega)

/-- Swapping the two leaves `0` and `n - 1` attached to node `1` of affine `Dₙ`. -/
private def dSwapLeft {n : ℕ} (hn : 4 ≤ n) : (D n).graph ≃g (D n).graph where
  toEquiv := Equiv.swap (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩
  map_rel_iff' := ⟨fun h ↦ by
    have h' := dSwap_adj hn h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_self] at h', dSwap_adj hn⟩

private def dRevVal (n k : ℕ) : ℕ :=
  if k ≤ n - 2 then n - 2 - k else if k = n - 1 then n else n - 1

private lemma dRevVal_lt {n k : ℕ} (hn : 4 ≤ n) (hk : k < (D n).nodes) :
    dRevVal n k < (D n).nodes := by
  rw [nodes_D] at hk ⊢; unfold dRevVal; split_ifs <;> omega

private lemma dRevVal_involutive {n k : ℕ} (hn : 4 ≤ n) (hk : k < (D n).nodes) :
    dRevVal n (dRevVal n k) = k := by
  rw [nodes_D] at hk; unfold dRevVal; split_ifs <;> omega

private lemma dRevFn_involutive {n : ℕ} (hn : 4 ≤ n) :
    Function.Involutive (fun k : Fin (D n).nodes ↦ ⟨dRevVal n k, dRevVal_lt hn k.isLt⟩) :=
  fun k ↦ Fin.ext (dRevVal_involutive hn k.isLt)

private def dRevEquiv {n : ℕ} (hn : 4 ≤ n) : Equiv.Perm (Fin (D n).nodes) :=
  (dRevFn_involutive hn).toPerm

private lemma coe_dRevEquiv {n : ℕ} (hn : 4 ≤ n) (k : Fin (D n).nodes) :
    ((dRevEquiv hn k : Fin (D n).nodes) : ℕ) = dRevVal n k :=
  congrArg Fin.val (congrFun (dRevFn_involutive hn).coe_toPerm k)

private lemma dRevEquiv_self {n : ℕ} (hn : 4 ≤ n) (k : Fin (D n).nodes) :
    dRevEquiv hn (dRevEquiv hn k) = k :=
  (dRevFn_involutive hn).toPerm_involutive k

private lemma dRevEquiv_adj {n : ℕ} (hn : 4 ≤ n) {a b : Fin (D n).nodes}
    (h : (D n).graph.Adj a b) :
    (D n).graph.Adj (dRevEquiv hn a) (dRevEquiv hn b) := by
  have ha : (a : ℕ) < n + 1 := by simpa [nodes_D] using a.isLt
  have hb : (b : ℕ) < n + 1 := by simpa [nodes_D] using b.isLt
  have hadj_D (x y : Fin (D n).nodes) := graph_D_adj hn (i := x) (j := y)
  rw [hadj_D] at h ⊢
  rw [coe_dRevEquiv, coe_dRevEquiv]
  rcases h with h | h | h | h | h | h <;> (dsimp only [dRevVal]; split_ifs <;> omega)

/-- Reversing the spine `0 - 1 - ⋯ - (n - 2)` of affine `Dₙ` while exchanging `n - 1` and `n`. -/
private def dReverse {n : ℕ} (hn : 4 ≤ n) : (D n).graph ≃g (D n).graph where
  toEquiv := dRevEquiv hn
  map_rel_iff' := ⟨fun h ↦ by
    have h' := dRevEquiv_adj hn h
    rwa [dRevEquiv_self, dRevEquiv_self] at h', dRevEquiv_adj hn⟩

private lemma coe_dReverse {n : ℕ} (hn : 4 ≤ n) (k : Fin (D n).nodes) :
    ((dReverse hn k : Fin (D n).nodes) : ℕ) = dRevVal n k :=
  coe_dRevEquiv hn k

private def e6SwapArm4 : E6.graph ≃g E6.graph where
  toEquiv := Equiv.swap (1 : Fin E6.nodes) 3 * Equiv.swap 2 4
  map_rel_iff' := @fun u v ↦ by revert u v; simp only [graph_E6_adj]; simp only [nodes_E6]; decide

private def e6SwapArm6 : E6.graph ≃g E6.graph where
  toEquiv := Equiv.swap (1 : Fin E6.nodes) 5 * Equiv.swap 2 6
  map_rel_iff' := @fun u v ↦ by revert u v; simp only [graph_E6_adj]; simp only [nodes_E6]; decide

private def e7SwapArms : E7.graph ≃g E7.graph where
  toEquiv := Equiv.swap (2 : Fin E7.nodes) 5 * Equiv.swap 3 6 * Equiv.swap 4 7
  map_rel_iff' := @fun u v ↦ by revert u v; simp only [graph_E7_adj]; simp only [nodes_E7]; decide

/-- **Transitivity on special nodes.** For every valid affine simply-laced diagram `t` and every
node `i` of mark `1`, there is a graph automorphism sending `i` to `t.affineNode`. -/
theorem exists_graph_iso_apply_eq_affineNode {t : AffineDynkinType} (ht : t.Valid)
    {i : Fin t.nodes} (hi : t.marks i = 1) :
    ∃ σ : t.graph ≃g t.graph, σ i = t.affineNode := by
  cases t with
  | A n => exact ⟨isoSubRightA n i, by rw [affineNode_A]; exact sub_self i⟩
  | D n =>
      rw [valid_D] at ht; rw [marks_D_apply] at hi; rw [affineNode_D]
      have hi_lt : (i : ℕ) < n + 1 := by simpa [nodes_D] using i.isLt
      have hleaf : (i : ℕ) = 0 ∨ (i : ℕ) = n - 2 ∨ (i : ℕ) = n - 1 ∨ (i : ℕ) = n := by
        split_ifs at hi <;> omega
      rcases hleaf with h0 | hn2 | hn1 | hn
      · exact ⟨SimpleGraph.Iso.refl, Fin.ext (h0.trans (Fin.val_zero _).symm)⟩
      · refine ⟨dReverse ht, Fin.ext ?_⟩
        rw [coe_dReverse, Fin.val_zero]; dsimp [dRevVal]; split_ifs <;> omega
      · refine ⟨dSwapLeft ht, ?_⟩
        rw [show i = ⟨n - 1, by rw [nodes_D]; omega⟩ from Fin.ext hn1]
        exact Equiv.swap_apply_right _ _
      · refine ⟨(dReverse ht).trans (dSwapLeft ht), ?_⟩
        rw [RelIso.trans_apply, show dReverse ht i = ⟨n - 1, by rw [nodes_D]; omega⟩ from
          Fin.ext (by rw [coe_dReverse]; dsimp [dRevVal]; split_ifs <;> omega)]
        exact Equiv.swap_apply_right _ _
  | E6 =>
      rw [marks_E6] at hi; rw [affineNode_E6]
      fin_cases i <;> simp at hi
      · exact ⟨SimpleGraph.Iso.refl, rfl⟩
      · exact ⟨e6SwapArm4, by decide⟩
      · exact ⟨e6SwapArm6, by decide⟩
  | E7 =>
      rw [marks_E7] at hi; rw [affineNode_E7]
      fin_cases i <;> simp at hi
      · exact ⟨SimpleGraph.Iso.refl, rfl⟩
      · exact ⟨e7SwapArms, by decide⟩
  | E8 =>
      rw [marks_E8] at hi; rw [affineNode_E8]
      fin_cases i <;> simp at hi
      exact ⟨SimpleGraph.Iso.refl, rfl⟩

/-- **Any two special nodes of a valid affine simply-laced diagram are related by a graph
automorphism.** -/
theorem exists_graph_iso_apply_eq {t : AffineDynkinType} (ht : t.Valid)
    {i j : Fin t.nodes} (hi : t.marks i = 1) (hj : t.marks j = 1) :
    ∃ σ : t.graph ≃g t.graph, σ i = j := by
  obtain ⟨σ₁, hσ₁⟩ := exists_graph_iso_apply_eq_affineNode ht hi
  obtain ⟨σ₂, hσ₂⟩ := exists_graph_iso_apply_eq_affineNode ht hj
  exact ⟨σ₁.trans σ₂.symm, by rw [RelIso.trans_apply, hσ₁, ← hσ₂, RelIso.symm_apply_apply]⟩

end TauCeti.AffineDynkinType
