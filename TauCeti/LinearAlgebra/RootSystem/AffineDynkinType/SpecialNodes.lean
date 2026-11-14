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
(`TauCeti.AffineDynkinType.marks_graph_iso_apply`), including at `Ã₁`. Conversely, on a valid
diagram the automorphism group acts transitively on the special nodes: every node of mark `1` can
be moved to `TauCeti.AffineDynkinType.affineNode` by a graph automorphism
(`TauCeti.AffineDynkinType.exists_graph_iso_apply_eq_affineNode`).

Concretely, the special nodes and the automorphisms realizing them are:

* all `n + 1` nodes of `Ãₙ`, permuted cyclically by translation in `Fin (n + 1)`;
* the four leaves `0`, `n - 2`, `n - 1` and `n` of affine `Dₙ` (`n ≥ 4`), related by swapping the
  two leaves `0` and `n - 1` on one fork and reversing the spine together with its forks;
* the three arm tips `2`, `4` and `6` of affine `E₆`, related by permuting its three arms of length
  two;
* the two long-arm tips `4` and `7` of affine `E₇`, related by swapping its two arms of length
  three;
* the unique special node `8` of affine `E₈`.

Consequently, any isomorphism onto the graph of a valid affine diagram that sends a chosen vertex
to a node of mark `1` can be renormalized by a diagram automorphism so as to send that vertex to
the affine node while preserving the marks and the generalized Cartan matrix.

## Main results

* `TauCeti.AffineDynkinType.cartanMatrix_graph_iso_apply` and
  `TauCeti.AffineDynkinType.cartanMatrix_submatrix_graph_iso`: every graph automorphism preserves
  the generalized Cartan matrix, `Ã₁` included.
* `TauCeti.AffineDynkinType.marks_graph_iso_apply` and
  `TauCeti.AffineDynkinType.marks_comp_graph_iso`: every graph automorphism preserves the marks.
* `TauCeti.AffineDynkinType.exists_graph_iso_apply_eq_affineNode`: on a valid diagram, every node
  of mark `1` is carried to `affineNode` by a graph automorphism.
* `TauCeti.AffineDynkinType.exists_graph_iso_apply_eq`: on a valid diagram, any two nodes of mark
  `1` are related by a graph automorphism.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VI, §2, n° 3 and Planches I–IX.
* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Table Aff 1.
-/

public section

open Finset SimpleGraph

namespace TauCeti.AffineDynkinType

/-! ### Invariance of the Cartan matrix and the marks under diagram automorphisms -/

/-- **Every graph automorphism of an affine simply-laced diagram preserves its generalized Cartan
matrix**, `Ã₁` included: away from `Ã₁` the matrix is `2I - A`, while at `Ã₁` it depends only on
equality of nodes. -/
@[simp]
theorem cartanMatrix_graph_iso_apply {t : AffineDynkinType} (σ : t.graph ≃g t.graph)
    (i j : Fin t.nodes) : t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j := by
  by_cases h : t = A 1
  · subst h
    rw [cartanMatrix_A_one_apply, cartanMatrix_A_one_apply]
    simp only [σ.injective.eq_iff]
  · have hg : t.IsGraphical := isGraphical_iff_ne_A_one.mpr h
    rw [cartanMatrix_apply hg, cartanMatrix_apply hg]
    simp only [σ.injective.eq_iff, σ.map_adj_iff]

/-- Reindexing the generalized Cartan matrix along a graph automorphism leaves it unchanged. -/
@[simp]
theorem cartanMatrix_submatrix_graph_iso {t : AffineDynkinType} (σ : t.graph ≃g t.graph) :
    t.cartanMatrix.submatrix σ σ = t.cartanMatrix := by
  ext i j
  exact cartanMatrix_graph_iso_apply σ i j

/-- **Every graph automorphism of an affine simply-laced diagram preserves its marks.** On a valid
graphical diagram the marks are the unique positive primitive null vector of `2I - A`
(`SimpleGraph.Iso.eq_gcd_smul_marks_comp`), while at `Ã₁` and outside the valid range the marks are
constant equal to `1`. -/
@[simp]
theorem marks_graph_iso_apply {t : AffineDynkinType} (σ : t.graph ≃g t.graph)
    (i : Fin t.nodes) : t.marks (σ i) = t.marks i := by
  by_cases ht : t.Valid
  · by_cases hg : t.IsGraphical
    · have heq := congrFun (σ.eq_gcd_smul_marks_comp ht hg
        (sum_natMarks_neighborFinset_eq_two_mul ht hg)) i
      simpa only [gcd_natMarks, Nat.cast_one, one_smul, Function.comp_apply, coe_natMarks] using
        heq.symm
    · rw [isGraphical_iff_ne_A_one, not_not] at hg
      subst hg
      exact (marks_A_apply 1 (σ i)).trans (marks_A_apply 1 i).symm
  · -- Outside `Valid` the diagram is `A 0` or `D n` with `n < 4`, where all marks equal `1`.
    cases t with
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
    t.marks ∘ σ = t.marks := by
  ext i
  exact marks_graph_iso_apply σ i

/-! ### Explicit automorphisms moving special nodes to the affine node -/

/-- Translation by `-i` as an automorphism of `(A n).graph`, sending `i` to `0`. -/
private def isoSubRightA (n : ℕ) (i : Fin (A n).nodes) : (A n).graph ≃g (A n).graph where
  toFun u := u - i
  invFun u := u + i
  left_inv u := sub_add_cancel u i
  right_inv u := add_sub_cancel_right u i
  map_rel_iff' {u v} := by
    rw [graph_A]
    exact TauCeti.cycleGraph_sub_adj_iff i u v

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
    have h0 : ((0 : Fin (D n).nodes) : ℕ) = 0 := Fin.val_zero _
    have hx0 : (x = 0) ↔ (x : ℕ) = 0 := by rw [Fin.ext_iff, h0]
    have hxn1 : (x = ⟨n - 1, by rw [nodes_D]; omega⟩) ↔ (x : ℕ) = n - 1 := Fin.ext_iff
    simp only [Equiv.swap_apply_def, hx0, hxn1]
    split_ifs <;> simp
  have hadj_D (x y : Fin (D n).nodes) := graph_D_adj hn (i := x) (j := y)
  rw [hadj_D] at h ⊢
  rw [hs a, hs b]
  rcases h with h | h | h | h | h | h <;> (split_ifs <;> omega)

/-- Swapping the two leaves `0` and `n - 1` attached to node `1` of affine `Dₙ`. -/
private def dSwapLeft {n : ℕ} (hn : 4 ≤ n) : (D n).graph ≃g (D n).graph where
  toEquiv := Equiv.swap (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩
  map_rel_iff' {u v} :=
    ⟨fun h ↦ by
      have h' := dSwap_adj hn h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_self] at h',
     dSwap_adj hn⟩

/-- Node-number formula for reversing the spine `0 - 1 - ⋯ - (n - 2)` of affine `Dₙ` while
exchanging the leaves `n - 1` and `n`. -/
private def dRevVal (n k : ℕ) : ℕ :=
  if k ≤ n - 2 then n - 2 - k else if k = n - 1 then n else n - 1

private lemma dRevVal_lt {n k : ℕ} (hn : 4 ≤ n) (hk : k < (D n).nodes) :
    dRevVal n k < (D n).nodes := by
  rw [nodes_D] at hk ⊢
  unfold dRevVal
  split_ifs <;> omega

private lemma dRevVal_involutive {n k : ℕ} (hn : 4 ≤ n) (hk : k < (D n).nodes) :
    dRevVal n (dRevVal n k) = k := by
  rw [nodes_D] at hk
  unfold dRevVal
  split_ifs <;> omega

private def dRevEquiv {n : ℕ} (hn : 4 ≤ n) : Fin (D n).nodes ≃ Fin (D n).nodes where
  toFun k := ⟨dRevVal n k, dRevVal_lt hn k.isLt⟩
  invFun k := ⟨dRevVal n k, dRevVal_lt hn k.isLt⟩
  left_inv k := Fin.ext (dRevVal_involutive hn k.isLt)
  right_inv k := Fin.ext (dRevVal_involutive hn k.isLt)

private lemma coe_dRevEquiv {n : ℕ} (hn : 4 ≤ n) (k : Fin (D n).nodes) :
    ((dRevEquiv hn k : Fin (n + 1)) : ℕ) = dRevVal n k := rfl

private lemma dRevEquiv_adj {n : ℕ} (hn : 4 ≤ n) {a b : Fin (D n).nodes}
    (h : (D n).graph.Adj a b) :
    (D n).graph.Adj (dRevEquiv hn a) (dRevEquiv hn b) := by
  have ha : (a : ℕ) < n + 1 := by simpa [nodes_D] using a.isLt
  have hb : (b : ℕ) < n + 1 := by simpa [nodes_D] using b.isLt
  have hadj_D (x y : Fin (D n).nodes) := graph_D_adj hn (i := x) (j := y)
  rw [hadj_D] at h ⊢
  rw [coe_dRevEquiv, coe_dRevEquiv]
  rcases h with h | h | h | h | h | h <;>
    (dsimp only [dRevVal]; split_ifs <;> omega)

private lemma dRevEquiv_self {n : ℕ} (hn : 4 ≤ n) (k : Fin (D n).nodes) :
    dRevEquiv hn (dRevEquiv hn k) = k :=
  (dRevEquiv hn).left_inv k

/-- Reversing the spine `0 - 1 - ⋯ - (n - 2)` of affine `Dₙ` while exchanging the leaves `n - 1`
and `n`. -/
private def dReverse {n : ℕ} (hn : 4 ≤ n) : (D n).graph ≃g (D n).graph where
  toEquiv := dRevEquiv hn
  map_rel_iff' {u v} :=
    ⟨fun h ↦ by
      have h' := dRevEquiv_adj hn h
      rwa [dRevEquiv_self, dRevEquiv_self] at h',
     dRevEquiv_adj hn⟩

private lemma coe_dReverse {n : ℕ} (hn : 4 ≤ n) (k : Fin (D n).nodes) :
    ((dReverse hn k : Fin (D n).nodes) : ℕ) = dRevVal n k := rfl

/-- Swapping the arms `0 - 1 - 2` and `0 - 3 - 4` of affine `E₆`, sending `4` to `2`. -/
private def e6SwapArm4 : E6.graph ≃g E6.graph where
  toEquiv := Equiv.swap (1 : Fin E6.nodes) 3 * Equiv.swap 2 4
  map_rel_iff' := @fun u v ↦ by
    revert u v
    simp only [graph_E6_adj]
    simp only [nodes_E6]
    decide

/-- Swapping the arms `0 - 1 - 2` and `0 - 5 - 6` of affine `E₆`, sending `6` to `2`. -/
private def e6SwapArm6 : E6.graph ≃g E6.graph where
  toEquiv := Equiv.swap (1 : Fin E6.nodes) 5 * Equiv.swap 2 6
  map_rel_iff' := @fun u v ↦ by
    revert u v
    simp only [graph_E6_adj]
    simp only [nodes_E6]
    decide

/-- Swapping the two long arms `1 - 2 - 3 - 4` and `1 - 5 - 6 - 7` of affine `E₇`, sending `7` to
`4`. -/
private def e7SwapArms : E7.graph ≃g E7.graph where
  toEquiv := Equiv.swap (2 : Fin E7.nodes) 5 * Equiv.swap 3 6 * Equiv.swap 4 7
  map_rel_iff' := @fun u v ↦ by
    revert u v
    simp only [graph_E7_adj]
    simp only [nodes_E7]
    decide

/-- **Transitivity on special nodes.** For every valid affine simply-laced diagram `t` and every
node `i` of mark `1`, there is a graph automorphism sending `i` to `t.affineNode`.

Validity is needed: at the degenerate `D 2`, all three nodes have mark `1`, while node `1` is
isolated and node `0 = (D 2).affineNode` lies on the single edge `0 - 2`. -/
theorem exists_graph_iso_apply_eq_affineNode {t : AffineDynkinType} (ht : t.Valid)
    {i : Fin t.nodes} (hi : t.marks i = 1) :
    ∃ σ : t.graph ≃g t.graph, σ i = t.affineNode := by
  cases t with
  | A n =>
      refine ⟨isoSubRightA n i, ?_⟩
      rw [affineNode_A]
      exact sub_self i
  | D n =>
      rw [valid_D] at ht
      rw [marks_D_apply] at hi
      rw [affineNode_D]
      have hi_lt : (i : ℕ) < n + 1 := by simpa [nodes_D] using i.isLt
      have hleaf : (i : ℕ) = 0 ∨ (i : ℕ) = n - 2 ∨ (i : ℕ) = n - 1 ∨ (i : ℕ) = n := by
        split_ifs at hi <;> omega
      have h0_val : ((0 : Fin (D n).nodes) : ℕ) = 0 := Fin.val_zero _
      rcases hleaf with h0 | hn2 | hn1 | hn
      · exact ⟨SimpleGraph.Iso.refl, Fin.ext (h0.trans h0_val.symm)⟩
      · refine ⟨dReverse ht, Fin.ext ?_⟩
        rw [coe_dReverse, h0_val]
        dsimp only [dRevVal]
        split_ifs <;> omega
      · refine ⟨dSwapLeft ht, ?_⟩
        have hi' : i = ⟨n - 1, by rw [nodes_D]; omega⟩ := Fin.ext hn1
        rw [hi']
        exact Equiv.swap_apply_right (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩
      · refine ⟨(dReverse ht).trans (dSwapLeft ht), ?_⟩
        rw [RelIso.trans_apply]
        have hrev : dReverse ht i = ⟨n - 1, by rw [nodes_D]; omega⟩ := by
          apply Fin.ext
          rw [coe_dReverse]
          dsimp only [dRevVal]
          split_ifs <;> omega
        rw [hrev]
        exact Equiv.swap_apply_right (0 : Fin (D n).nodes) ⟨n - 1, by rw [nodes_D]; omega⟩
  | E6 =>
      rw [marks_E6] at hi
      rw [affineNode_E6]
      fin_cases i <;> simp at hi
      · exact ⟨SimpleGraph.Iso.refl, rfl⟩
      · exact ⟨e6SwapArm4, by decide⟩
      · exact ⟨e6SwapArm6, by decide⟩
  | E7 =>
      rw [marks_E7] at hi
      rw [affineNode_E7]
      fin_cases i <;> simp at hi
      · exact ⟨SimpleGraph.Iso.refl, rfl⟩
      · exact ⟨e7SwapArms, by decide⟩
  | E8 =>
      rw [marks_E8] at hi
      rw [affineNode_E8]
      fin_cases i <;> simp at hi
      exact ⟨SimpleGraph.Iso.refl, rfl⟩

/-- **Any two special nodes of a valid affine simply-laced diagram are related by a graph
automorphism.** -/
theorem exists_graph_iso_apply_eq {t : AffineDynkinType} (ht : t.Valid)
    {i j : Fin t.nodes} (hi : t.marks i = 1) (hj : t.marks j = 1) :
    ∃ σ : t.graph ≃g t.graph, σ i = j := by
  obtain ⟨σ₁, hσ₁⟩ := exists_graph_iso_apply_eq_affineNode ht hi
  obtain ⟨σ₂, hσ₂⟩ := exists_graph_iso_apply_eq_affineNode ht hj
  refine ⟨σ₁.trans σ₂.symm, ?_⟩
  rw [RelIso.trans_apply, hσ₁, ← hσ₂, RelIso.symm_apply_apply]

end TauCeti.AffineDynkinType
