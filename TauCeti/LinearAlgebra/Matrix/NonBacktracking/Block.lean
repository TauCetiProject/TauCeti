/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import TauCeti.Combinatorics.TraceWord.Bipartite.Basic
public import TauCeti.Data.Fin.Tuple.Basic
public import TauCeti.LinearAlgebra.Matrix.NonBacktracking
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Blocks of bipartite non-backtracking walk matrices

An alternating path through a block matrix uses only its off-diagonal weights. When the
diagonal blocks vanish, the even-length non-backtracking walk matrix restricted to row
vertices sums the weights of these alternating paths with no immediate reversals.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
-/

public section

open Finset TauCeti

namespace Matrix

variable {p n R : Type*}

/-- The weight of an alternating path is the product of its pairs of off-diagonal
steps. -/
theorem prod_fromBlocks_bipartitePath [CommMonoid R] {k : ℕ}
    (C : Matrix p p R) (A : Matrix p n R) (B : Matrix n p R) (D : Matrix n n R)
    (u : Fin (k + 1) → p) (v : Fin k → n) :
    (∏ t : Fin (2 * k), fromBlocks C A B D (bipartitePath u v t.castSucc)
        (bipartitePath u v t.succ)) =
      ∏ t : Fin k, A (u t.castSucc) (v t) * B (v t) (u t.succ) := by
  rw [← (finSumFinInterleaveEquiv k).prod_comp, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  congr 1 <;> (apply Finset.prod_congr rfl; intro t _)
  · have he : (finSumFinInterleaveEquiv k (.inl t)).castSucc =
        ⟨2 * (t.castSucc : ℕ), by omega⟩ := Fin.ext (by simp)
    have ho : (finSumFinInterleaveEquiv k (.inl t)).succ =
        ⟨2 * t + 1, by omega⟩ := Fin.ext (by simp)
    simp only [he, ho, bipartitePath_even, bipartitePath_odd, fromBlocks_apply₁₂]
  · have ho : (finSumFinInterleaveEquiv k (.inr t)).castSucc =
        ⟨2 * t + 1, by omega⟩ := Fin.ext (by simp)
    have he : (finSumFinInterleaveEquiv k (.inr t)).succ =
        ⟨2 * (t.succ : ℕ), by omega⟩ := Fin.ext (by simp; omega)
    simp only [he, ho, bipartitePath_even, bipartitePath_odd, fromBlocks_apply₂₁]

variable [CommSemiring R] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]

/-- The row block of the non-backtracking walk matrix of even length for an off-diagonal
block matrix is a sum over alternating paths. Consecutive row vertices and consecutive
column vertices are distinct. -/
theorem toBlocks₁₁_nonbacktrackingPow_apply (A : Matrix p n R) (B : Matrix n p R)
    (k : ℕ) (i j : p) :
    (nonbacktrackingPow (fromBlocks 0 A B 0) (2 * k)).toBlocks₁₁ i j =
      ∑ uv : (Fin (k + 1) → p) × (Fin k → n) with uv.1 0 = i ∧ uv.1 (Fin.last k) = j ∧
          (∀ t : Fin k, uv.1 t.castSucc ≠ uv.1 t.succ) ∧
          (∀ s t : Fin k, (s : ℕ) + 1 = t → uv.2 s ≠ uv.2 t),
        ∏ t : Fin k, A (uv.1 t.castSucc) (uv.2 t) * B (uv.2 t) (uv.1 t.succ) := by
  classical
  rw [toBlocks₁₁_eq_submatrix, submatrix_apply, nonbacktrackingPow_apply]
  let W : Finset (Fin (2 * k + 1) → p ⊕ n) := univ.filter fun w ↦
    w 0 = .inl i ∧ w (Fin.last (2 * k)) = .inl j ∧
      ∀ s t : Fin (2 * k + 1), (s : ℕ) + 2 = t → w s ≠ w t
  let P (w : Fin (2 * k + 1) → p ⊕ n) :=
    ∏ t : Fin (2 * k), fromBlocks 0 A B 0 (w t.castSucc) (w t.succ)
  have hfilter : (∑ w ∈ W.filter (fun w ↦ ∃ u v, bipartitePath u v = w), P w) =
      ∑ w ∈ W, P w := by
    refine sum_filter_of_ne fun w hw hn ↦ ?_
    have hi := (mem_filter.mp hw).2.1
    exact (exists_eq_bipartitePath_iff w).2
      (isLeft_eq_of_prod_fromBlocks_ne_zero A B (by simp [hi]) hn)
  rw [← hfilter]
  have hmem (uv : (Fin (k + 1) → p) × (Fin k → n)) :
      bipartitePath uv.1 uv.2 ∈ W.filter (fun w ↦ ∃ u v, bipartitePath u v = w) ↔
        uv.1 0 = i ∧ uv.1 (Fin.last k) = j ∧
          (∀ t : Fin k, uv.1 t.castSucc ≠ uv.1 t.succ) ∧
          (∀ s t : Fin k, (s : ℕ) + 1 = t → uv.2 s ≠ uv.2 t) := by
    simp [W]
  symm
  refine Finset.sum_nbij (fun uv ↦ bipartitePath uv.1 uv.2) (fun uv h ↦ (hmem uv).2 ?_)
    bipartitePath_injective.injOn ?_
    (fun uv _ ↦ (prod_fromBlocks_bipartitePath 0 A B 0 uv.1 uv.2).symm)
  · exact (mem_filter.mp h).2
  · intro w hw
    obtain ⟨u, v, rfl⟩ := (mem_filter.mp hw).2
    exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, (hmem (u, v)).1 hw⟩, rfl⟩

/-- The row block entry for a positive even walk length sums over the interior row vertices
and all column vertices. The two row endpoints are inserted by `Fin.fixedEndpointsEquiv`. -/
theorem toBlocks₁₁_nonbacktrackingPow_apply_succ
    (A : Matrix p n R) (B : Matrix n p R) (k : ℕ) (i j : p) :
    let rows (u : Fin k → p) := (Fin.fixedEndpointsEquiv i j u).val
    (nonbacktrackingPow (fromBlocks 0 A B 0) (2 * (k + 1))).toBlocks₁₁ i j =
      ∑ uv : (Fin k → p) × (Fin (k + 1) → n) with
          (∀ t : Fin (k + 1), rows uv.1 t.castSucc ≠ rows uv.1 t.succ) ∧
          (∀ t : Fin k, uv.2 t.castSucc ≠ uv.2 t.succ),
        ∏ t : Fin (k + 1), A (rows uv.1 t.castSucc) (uv.2 t) * B (uv.2 t) (rows uv.1 t.succ) := by
  dsimp only
  rw [toBlocks₁₁_nonbacktrackingPow_apply]
  symm
  let e := Fin.fixedEndpointsEquiv (k := k) i j
  refine sum_nbij (fun uv ↦ ((e uv.1).val, uv.2)) (fun uv huv ↦ ?_)
    (fun a _ b _ hab ↦ ?_) (fun uv huv ↦ ?_) (fun _ _ ↦ rfl)
  · simpa [e, Fin.forall_val_add_one_eq_iff] using huv
  · obtain ⟨hrows, hcols⟩ := Prod.mk.inj hab
    exact Prod.ext (e.injective (Subtype.ext hrows)) hcols
  · have h := (mem_filter.mp huv).2
    let u := e.symm ⟨uv.1, h.1, h.2.1⟩
    have he : (Fin.fixedEndpointsEquiv i j u).val = uv.1 :=
      congrArg Subtype.val (e.apply_symm_apply _)
    refine ⟨(u, uv.2), mem_filter.mpr ⟨mem_univ _, ?_⟩, Prod.ext he rfl⟩
    rw [he]
    exact ⟨h.2.2.1, (Fin.forall_val_add_one_eq_iff _).1 h.2.2.2⟩

end Matrix
