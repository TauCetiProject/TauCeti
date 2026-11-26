/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.NonBacktracking.Block
public import TauCeti.LinearAlgebra.Matrix.Trace.Pow
import TauCeti.Data.Fin.Basic
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

open Finset

namespace Matrix

variable {p n R : Type*}

variable [CommSemiring R] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]

/-- Append the terminal row to the starting row and the interior rows of one walk. -/
private abbrev walkRows {k : ℕ} (i j : p) (u : Fin k → p) : Fin (k + 2) → p :=
  Fin.snoc (Fin.cons i u) j

private theorem toBlocks₁₁_nonbacktrackingPow_apply_succ
    (A : Matrix p n R) (B : Matrix n p R) (k : ℕ) (i j : p) :
    (nonbacktrackingPow (fromBlocks 0 A B 0) (2 * (k + 1))).toBlocks₁₁ i j =
      ∑ uv : (Fin k → p) × (Fin (k + 1) → n) with
          (∀ t : Fin (k + 1), walkRows i j uv.1 t.castSucc ≠ walkRows i j uv.1 t.succ) ∧
          (∀ t : Fin k, uv.2 t.castSucc ≠ uv.2 t.succ),
        ∏ t : Fin (k + 1), A (walkRows i j uv.1 t.castSucc) (uv.2 t) *
          B (uv.2 t) (walkRows i j uv.1 t.succ) := by
  rw [toBlocks₁₁_nonbacktrackingPow_apply]
  symm
  refine sum_nbij (fun uv ↦ (walkRows i j uv.1, uv.2)) (fun uv huv ↦ ?_)
    (fun a _ b _ hab ↦ ?_) (fun uv huv ↦ ?_) (fun _ _ ↦ rfl)
  · simpa [walkRows, Fin.forall_val_add_one_eq_iff] using huv
  · have h₁ : walkRows i j a.1 = walkRows i j b.1 := congrArg Prod.fst hab
    have h₂ : a.2 = b.2 := congrArg (fun q : (Fin (k + 2) → p) × (Fin (k + 1) → n) ↦ q.2) hab
    exact Prod.ext (Fin.cons_right_injective (α := fun _ ↦ p) i
      (Fin.snoc_left_injective (α := fun _ ↦ p) j h₁)) h₂
  · have h := (mem_filter.mp huv).2
    let u : Fin k → p := Fin.tail (Fin.init uv.1)
    have he : walkRows i j u = uv.1 := by
      rw [walkRows, ← h.1, ← h.2.1]
      exact (Fin.cons_self_tail (Fin.init uv.1)).symm ▸ Fin.snoc_init_self uv.1
    refine ⟨(u, uv.2), mem_filter.mpr ⟨mem_univ _, ?_⟩, Prod.ext he rfl⟩
    rw [he]
    exact ⟨h.2.2.1, (Fin.forall_val_add_one_eq_iff _).1 h.2.2.2⟩

/-- The trace of the rth power of the row block of the bipartite non-backtracking walk matrix
of length 2(k + 1) is the sum over closed bipartite words with r(k + 1) row visits.
All consecutive row vertices must differ. Consecutive column vertices must differ within
each constituent walk, with no restriction at the joins of successive walks. -/
theorem trace_pow_toBlocks₁₁_nonbacktrackingPow (A : Matrix p n R) (B : Matrix n p R)
    {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    let m := r * (k + 1)
    (((nonbacktrackingPow (fromBlocks 0 A B 0) (2 * (k + 1))).toBlocks₁₁) ^ r).trace =
      ∑ uv : (Fin m → p) × (Fin m → n) with
          ∀ t : Fin m, uv.1 t ≠ uv.1 (finRotate m t) ∧
            (t.modNat ≠ Fin.last k → uv.2 t ≠ uv.2 (finRotate m t)),
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
  simp_rw [walkRows, Fin.snoc_cons_blockHeadTailEquiv_succ, Fin.snoc_castSucc,
    Fin.cons_blockHeadTailEquiv]
  have hv (a : Fin r) (t : Fin (k + 1)) : e v a t = v (finProdFinEquiv (a, t)) := rfl
  simp only [hv, Finset.prod_ite_zero]
  let f (t : Fin (r * (k + 1))) :=
    A (u t) (v t) * B (v t) (u (finRotate (r * (k + 1)) t))
  have hprod : (∏ a : Fin r, ∏ b : Fin (k + 1), f (finProdFinEquiv (a, b))) = ∏ t, f t := by
    simpa only [Fintype.prod_prod_type] using
      (finProdFinEquiv (m := r) (n := k + 1)).prod_comp f
  rw [hprod]
  refine ite_congr (propext ?_) (fun _ ↦ rfl) (fun _ ↦ rfl)
  -- Each column except the last has a successor within the same walk.
  refine ⟨fun h t ↦ ?_, fun h a _ ↦ ?_⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective t
    refine ⟨(h a (mem_univ a)).1 b, fun hb ↦ ?_⟩
    rw [Fin.modNat_finProdFinEquiv] at hb
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hb
    simpa only [Fin.finRotate_finProdFinEquiv_castSucc] using (h a (mem_univ a)).2 j
  · exact ⟨fun b ↦ (h (finProdFinEquiv (a, b))).1, fun j ↦ by
      rw [← Fin.finRotate_finProdFinEquiv_castSucc]
      refine (h (finProdFinEquiv (a, j.castSucc))).2 ?_
      simpa only [Fin.modNat_finProdFinEquiv] using Fin.castSucc_ne_last j⟩

end Matrix
