/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.NonBacktracking
public import TauCeti.LinearAlgebra.Matrix.Trace.Pow
import TauCeti.Combinatorics.TraceWord.Bipartite.Basic
import TauCeti.Data.Fin.Rotate
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Block

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

/-- Interleave the row and column vertices and append the final row vertex. -/
private def bipartitePath {k : ℕ} (u : Fin (k + 1) → p) (v : Fin k → n) :
    Fin (2 * k + 1) → p ⊕ n :=
  Fin.snoc (bipartiteWord (u ∘ Fin.castSucc) v) (.inl (u (Fin.last k)))

private theorem bipartitePath_even {k : ℕ} (u : Fin (k + 1) → p) (v : Fin k → n)
    (t : Fin (k + 1)) :
    bipartitePath u v ⟨2 * t, by omega⟩ = .inl (u t) := by
  induction t using Fin.lastCases with
  | last =>
    have h : (⟨2 * (Fin.last k : ℕ), by simp⟩ : Fin (2 * k + 1)) = Fin.last (2 * k) := by
      ext
      simp
    rw [h]
    simp [bipartitePath]
  | cast t =>
    have h : (⟨2 * (t : ℕ), by omega⟩ : Fin (2 * k + 1)) =
        (finSumFinInterleaveEquiv k (.inl t)).castSucc := by ext; simp
    simp [bipartitePath, h]

private theorem bipartitePath_odd {k : ℕ} (u : Fin (k + 1) → p) (v : Fin k → n) (t : Fin k) :
    bipartitePath u v ⟨2 * t + 1, by omega⟩ = .inr (v t) := by
  have h : (⟨2 * (t : ℕ) + 1, by omega⟩ : Fin (2 * k + 1)) =
      (finSumFinInterleaveEquiv k (.inr t)).castSucc := by ext; simp
  simp [bipartitePath, h]

private theorem bipartitePath_injective {k : ℕ} :
    Function.Injective (fun uv : (Fin (k + 1) → p) × (Fin k → n) ↦
      bipartitePath uv.1 uv.2) := by
  intro u v huv
  refine Prod.ext (funext fun t ↦ ?_) (funext fun t ↦ ?_)
  · simpa only [bipartitePath_even, Sum.inl.injEq] using congrFun huv ⟨2 * t, by omega⟩
  · simpa only [bipartitePath_odd, Sum.inr.injEq] using congrFun huv ⟨2 * t + 1, by omega⟩

private theorem exists_eq_bipartitePath {k : ℕ} (w : Fin (2 * k + 1) → p ⊕ n)
    (h : ∀ t, (w t).isLeft = decide ((t : ℕ) % 2 = 0)) :
    ∃ (u : Fin (k + 1) → p) (v : Fin k → n), bipartitePath u v = w := by
  let u (t : Fin (k + 1)) := (w ⟨2 * t, by omega⟩).getLeft (by
    rw [h]
    exact decide_eq_true (by simp))
  let v (t : Fin k) := (w ⟨2 * t + 1, by omega⟩).getRight (by
    rw [← Sum.not_isLeft, h]
    simp)
  refine ⟨u, v, funext fun t ↦ ?_⟩
  by_cases ht : (t : ℕ) % 2 = 0
  · let j : Fin (k + 1) := ⟨t / 2, by omega⟩
    have hEq : t = ⟨2 * j, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hEq, bipartitePath_even]
    exact Sum.inl_getLeft _ _
  · let j : Fin k := ⟨t / 2, by omega⟩
    have hEq : t = ⟨2 * j + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hEq, bipartitePath_odd]
    exact Sum.inr_getRight _ _

variable [CommSemiring R]

private theorem bipartitePath_nonbacktracking_iff {k : ℕ} (u : Fin (k + 1) → p)
    (v : Fin k → n) :
    (∀ s t : Fin (2 * k + 1), (s : ℕ) + 2 = t → bipartitePath u v s ≠ bipartitePath u v t) ↔
      (∀ t : Fin k, u t.castSucc ≠ u t.succ) ∧
        ∀ s t : Fin k, (s : ℕ) + 1 = t → v s ≠ v t := by
  constructor
  · intro h
    constructor
    · intro t
      simpa only [bipartitePath_even, ne_eq, Sum.inl.injEq] using
        h ⟨2 * (t.castSucc : ℕ), by omega⟩ ⟨2 * (t.succ : ℕ), by omega⟩ (by simp; omega)
    · intro s t hst
      simpa only [bipartitePath_odd, ne_eq, Sum.inr.injEq] using
        h ⟨2 * s + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ (by dsimp; omega)
  · rintro ⟨hu, hv⟩ s t hst
    by_cases hs : (s : ℕ) % 2 = 0
    · let j : Fin k := ⟨s / 2, by omega⟩
      have hs' : s = ⟨2 * (j.castSucc : ℕ), by omega⟩ := Fin.ext (by dsimp [j]; omega)
      have ht' : t = ⟨2 * (j.succ : ℕ), by omega⟩ := Fin.ext (by dsimp [j]; omega)
      simpa only [hs', ht', bipartitePath_even, ne_eq, Sum.inl.injEq] using hu j
    · let j : Fin k := ⟨s / 2, by omega⟩
      let j' : Fin k := ⟨t / 2, by omega⟩
      have hs' : s = ⟨2 * j + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      have ht' : t = ⟨2 * j' + 1, by omega⟩ := Fin.ext (by dsimp [j']; omega)
      simpa only [hs', ht', bipartitePath_odd, ne_eq, Sum.inr.injEq] using
        hv j j' (by dsimp [j, j']; omega)

private theorem prod_fromBlocks_bipartitePath {k : ℕ}
    (A : Matrix p n R) (B : Matrix n p R) (u : Fin (k + 1) → p) (v : Fin k → n) :
    (∏ t : Fin (2 * k), fromBlocks 0 A B 0 ((bipartitePath u v) t.castSucc)
        ((bipartitePath u v) t.succ)) =
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

variable [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]

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
    exact exists_eq_bipartitePath w (isLeft_eq_of_prod_fromBlocks_ne_zero A B (by simp [hi]) hn)
  rw [← hfilter]
  have hmem (uv : (Fin (k + 1) → p) × (Fin k → n)) :
      bipartitePath uv.1 uv.2 ∈ W.filter (fun w ↦ ∃ u v, bipartitePath u v = w) ↔
        uv.1 0 = i ∧ uv.1 (Fin.last k) = j ∧
          (∀ t : Fin k, uv.1 t.castSucc ≠ uv.1 t.succ) ∧
          (∀ s t : Fin k, (s : ℕ) + 1 = t → uv.2 s ≠ uv.2 t) := by
    have hstart : bipartitePath uv.1 uv.2 0 = .inl (uv.1 0) :=
      bipartitePath_even _ _ 0
    have hend : bipartitePath uv.1 uv.2 (Fin.last (2 * k)) = .inl (uv.1 (Fin.last k)) :=
      bipartitePath_even _ _ (Fin.last k)
    have hpath : ∃ u v, bipartitePath u v = bipartitePath uv.1 uv.2 := ⟨uv.1, uv.2, rfl⟩
    simp [W, hstart, hend, bipartitePath_nonbacktracking_iff, hpath]
  symm
  refine Finset.sum_nbij (fun uv ↦ bipartitePath uv.1 uv.2) (fun uv h ↦ (hmem uv).2 ?_)
    bipartitePath_injective.injOn ?_ (fun uv _ ↦ (prod_fromBlocks_bipartitePath A B uv.1 uv.2).symm)
  · exact (mem_filter.mp h).2
  · intro w hw
    obtain ⟨u, v, rfl⟩ := (mem_filter.mp hw).2
    exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, (hmem (u, v)).1 hw⟩, rfl⟩

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
  have hcol (v : Fin (k + 1) → n) :
      (∀ s t : Fin (k + 1), (s : ℕ) + 1 = t → v s ≠ v t) ↔
        ∀ t : Fin k, v t.castSucc ≠ v t.succ := by
    refine ⟨fun h t ↦ h t.castSucc t.succ rfl, fun h s t hst ↦ ?_⟩
    let a : Fin k := ⟨s, by omega⟩
    exact (Fin.ext (rfl : a.val = s.val) : a.castSucc = s) ▸
      (Fin.ext hst : a.succ = t) ▸ h a
  symm
  refine sum_nbij (fun uv ↦ (walkRows i j uv.1, uv.2)) (fun uv huv ↦ ?_)
    (fun a _ b _ hab ↦ ?_) (fun uv huv ↦ ?_) (fun _ _ ↦ rfl)
  · simpa [walkRows, hcol] using huv
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
    exact ⟨h.2.2.1, (hcol _).1 h.2.2.2⟩

omit [Fintype p] [DecidableEq p] in
private theorem walkRows_blockHeadTailEquiv_succ {r k : ℕ} (u : Fin (r * (k + 1)) → p)
    (a : Fin r) (t : Fin (k + 1)) :
    walkRows ((Fin.blockHeadTailEquiv r k u).1 a) ((Fin.blockHeadTailEquiv r k u).1 (finRotate r a))
      ((Fin.blockHeadTailEquiv r k u).2 a) t.succ =
      u (finRotate (r * (k + 1)) (finProdFinEquiv (a, t))) := by
  induction t using Fin.lastCases with
  | last =>
    rw [Fin.finRotate_finProdFinEquiv_last, Fin.succ_last, walkRows, Fin.snoc_last]
    exact Fin.blockHeadTailEquiv_apply_fst u (finRotate r a)
  | cast t =>
    rw [Fin.finRotate_finProdFinEquiv_castSucc, walkRows, Fin.succ_castSucc, Fin.snoc_castSucc,
      Fin.cons_succ]
    exact Fin.blockHeadTailEquiv_apply_snd u a t

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
  simp_rw [walkRows_blockHeadTailEquiv_succ, Fin.snoc_castSucc, Fin.cons_blockHeadTailEquiv]
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
    have hmod : (finProdFinEquiv (a, b)).modNat = b :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, b))
    rw [hmod] at hb
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hb
    simpa only [Fin.finRotate_finProdFinEquiv_castSucc] using (h a (mem_univ a)).2 j
  · exact ⟨fun b ↦ (h (finProdFinEquiv (a, b))).1, fun j ↦ by
      rw [← Fin.finRotate_finProdFinEquiv_castSucc]
      refine (h (finProdFinEquiv (a, j.castSucc))).2 ?_
      have hm : (finProdFinEquiv (a, j.castSucc)).modNat = j.castSucc :=
        congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, j.castSucc))
      rw [hm]
      exact Fin.castSucc_ne_last j⟩

end Matrix
