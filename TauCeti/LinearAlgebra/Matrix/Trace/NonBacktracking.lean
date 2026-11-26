/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Basic
public import TauCeti.LinearAlgebra.Matrix.NonBacktracking.Block
public import TauCeti.LinearAlgebra.Matrix.Trace.Pow
import TauCeti.Data.Fin.Rotate

/-!
# Trace words of bipartite non-backtracking walk matrices

For an off-diagonal block matrix, a non-backtracking walk with both endpoints in the row
index type alternates between row and column indices. Powers of the row block of the
walk matrix concatenate walks of equal length. The trace closes the resulting bipartite
word, with reversals forbidden within each constituent walk and allowed at their joins.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
-/

public section

open Finset TauCeti

namespace Matrix

variable {p n R : Type*}

variable [CommSemiring R] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]

open Classical in
/-- The trace of the rth power of the row block of the bipartite non-backtracking walk matrix
of length 2(k + 1) is the sum over closed bipartite words with r(k + 1) row visits.
All consecutive row vertices must differ. Consecutive column vertices must differ within
each constituent walk, with no restriction at the joins of successive walks. -/
theorem trace_pow_toBlocks₁₁_nonbacktrackingPow (A : Matrix p n R) (B : Matrix n p R)
    {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    let m := r * (k + 1)
    (((nonbacktrackingPow (fromBlocks 0 A B 0) (2 * (k + 1))).toBlocks₁₁) ^ r).trace =
      ∑ uv : (Fin m → p) × (Fin m → n) with BipartiteNonbacktracking k uv.1 uv.2,
        ∏ t : Fin m, A (uv.1 t) (uv.2 t) * B (uv.2 t) (uv.1 (finRotate m t)) := by
  classical
  dsimp only
  simp_rw [trace_pow_eq_sum_prod _ hr, toBlocks₁₁_nonbacktrackingPow_apply_succ,
    Finset.sum_filter, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  -- Group the choices of vertices by their roles within each walk.
  simp_rw [← (Equiv.arrowProdEquivProdArrow (Fin r) (fun _ ↦ Fin k → p)
    (fun _ ↦ Fin (k + 1) → n)).symm.sum_comp, Fintype.sum_prod_type]
  conv_lhs => rw [← Fintype.sum_prod_type', ← (Fin.blockHeadTailEquiv r k).sum_comp]
  let e : (Fin (r * (k + 1)) → n) ≃ (Fin r → Fin (k + 1) → n) :=
    (finProdFinEquiv.symm.arrowCongr (Equiv.refl n)).trans
      (Equiv.curry (Fin r) (Fin (k + 1)) n)
  refine sum_congr rfl fun u _ ↦ ?_
  rw [← e.sum_comp]
  refine sum_congr rfl fun v _ ↦ ?_
  simp only [Equiv.arrowProdEquivProdArrow_symm_apply]
  have hu (a : Fin r) :
      Fin.cons (α := fun _ ↦ p) ((Fin.blockHeadTailEquiv r k u).1 a)
        ((Fin.blockHeadTailEquiv r k u).2 a) = fun t ↦ u (finProdFinEquiv (a, t)) :=
    funext (Fin.cons_blockHeadTailEquiv u a)
  simp_rw [Fin.fixedEndpointsEquiv_apply, hu, Fin.blockHeadTailEquiv_apply_fst,
    Fin.snoc_castSucc, Fin.snoc_finProdFinEquiv_succ]
  have hv (a : Fin r) (t : Fin (k + 1)) : e v a t = v (finProdFinEquiv (a, t)) := rfl
  simp only [hv, Finset.prod_ite_zero]
  let f (t : Fin (r * (k + 1))) :=
    A (u t) (v t) * B (v t) (u (finRotate (r * (k + 1)) t))
  have hprod : (∏ a : Fin r, ∏ b : Fin (k + 1), f (finProdFinEquiv (a, b))) = ∏ t, f t := by
    simpa only [Fintype.prod_prod_type] using
      (finProdFinEquiv (m := r) (n := k + 1)).prod_comp f
  rw [hprod]
  refine ite_congr (propext ?_) (fun _ ↦ rfl) (fun _ ↦ rfl)
  simp only [bipartiteNonbacktracking_iff_blocks, Fin.snoc_castSucc,
    Fin.snoc_finProdFinEquiv_succ, mem_univ, true_implies]

end Matrix
