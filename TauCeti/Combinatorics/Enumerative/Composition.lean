/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Head-tail decomposition and prefix sums of integer compositions

Splitting off the first block of a non-single integer composition turns first-cut recursions—such
as tensor-coalgebra block words and coalgebra morphisms—into closed-form sums over `Composition n`,
while prefix-sum identities align `Composition.embedding` with `finSigmaFinEquiv` leaf-flattening
at planar-tree vertices.

## Main definitions and results

* `Composition.blocksFun_eq_getElem`, `Composition.cast_length`, `Composition.cast_blocksFun`, and
  `Composition.cast_sizeUpTo`: `c.blocksFun i` agrees with `c.blocks[i]`, and `Composition.cast`
  preserves `length`, `blocksFun`, and `sizeUpTo`.
* `Composition.sizeUpTo_eq_sum_blocksFun` and `Composition.coe_embedding_eq_finSigmaFinEquiv`:
  `c.sizeUpTo i` is the `Fin`-indexed sum of `c.blocksFun`, matching `finSigmaFinEquiv`.
* `Composition.cons` and `Composition.neSingleSuccEquiv`: prepending a positive first block
  identifies `(k : Fin b) × Composition (b - k)` with non-single compositions of `b + 1`, with
  inverse projections `Composition.val_fst_neSingleSuccEquiv_symm` and
  `Composition.snd_neSingleSuccEquiv_symm_blocks`.
-/

public section

open scoped BigOperators

namespace Composition

/-- Evaluating `blocksFun` at `i : Fin c.length` reads `c.blocks[i]`. -/
theorem blocksFun_eq_getElem {n : ℕ} (c : Composition n) (i : Fin c.length) :
    c.blocksFun i = c.blocks[i.1] :=
  Nat.add_left_cancel ((c.sizeUpTo_succ' i).symm.trans (c.sizeUpTo_succ i.2))

@[simp] theorem cast_length {m n : ℕ} (c : Composition m) (h : m = n) :
    (c.cast h).length = c.length := by
  rw [← blocks_length, cast_blocks, blocks_length]

@[simp] theorem cast_blocksFun {m n : ℕ} (c : Composition m) (h : m = n)
    (i : Fin (c.cast h).length) :
    (c.cast h).blocksFun i = c.blocksFun (i.cast (c.cast_length h)) := by
  simp [blocksFun_eq_getElem]

@[simp] theorem cast_sizeUpTo {m n : ℕ} (c : Composition m) (h : m = n) (i : ℕ) :
    (c.cast h).sizeUpTo i = c.sizeUpTo i := by
  simp [sizeUpTo]

/-- The prefix sum `c.sizeUpTo i` is the sum of the first `i` values of `c.blocksFun`. -/
theorem sizeUpTo_eq_sum_blocksFun {n : ℕ} (c : Composition n) {i : ℕ} (hi : i ≤ c.length) :
    c.sizeUpTo i = ∑ a : Fin i, c.blocksFun (Fin.castLE hi a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [c.sizeUpTo_succ' ⟨i, hi⟩, ih (Nat.le_of_succ_le hi), Fin.sum_univ_castSucc]
    rfl

/-- The `i`-th block embedding of `c` has the same underlying natural index as `finSigmaFinEquiv`
applied to `c.blocksFun`. -/
theorem coe_embedding_eq_finSigmaFinEquiv {n : ℕ} (c : Composition n) (i : Fin c.length)
    (j : Fin (c.blocksFun i)) :
    (c.embedding i j : ℕ) = (finSigmaFinEquiv (n := c.blocksFun) ⟨i, j⟩ : ℕ) := by
  rw [c.coe_embedding, finSigmaFinEquiv_apply, c.sizeUpTo_eq_sum_blocksFun i.2.le]

/-- A composition of a positive integer has at least two blocks if and only if it is not the
single-block composition. -/
theorem two_le_length_iff_ne_single {n : ℕ} (hn : 0 < n) (c : Composition n) :
    2 ≤ c.length ↔ c ≠ single n hn := by
  have := c.length_pos_of_pos hn
  rw [ne_eq, eq_single_iff_length hn]
  omega

/-- Prepend a positive first block of size `k` to a composition of `n`, producing a composition of
`k + n`. -/
def cons {k n : ℕ} (hk : 0 < k) (c : Composition n) : Composition (k + n) where
  blocks := k :: c.blocks
  blocks_pos {m} hm := by
    rcases List.mem_cons.mp hm with rfl | hm
    exacts [hk, c.blocks_pos hm]
  blocks_sum := by
    rw [List.sum_cons, c.blocks_sum]

@[simp] theorem cons_blocks {k n : ℕ} (hk : 0 < k) (c : Composition n) :
    (cons hk c).blocks = k :: c.blocks := (rfl)

@[simp] theorem cons_length {k n : ℕ} (hk : 0 < k) (c : Composition n) :
    (cons hk c).length = c.length + 1 := by
  rw [← blocks_length, cons_blocks, List.length_cons, blocks_length]

/-- Prepending a positive block via `cons` to a composition of a positive integer yields a
composition of length at least two. -/
theorem two_le_cons_length {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (c : Composition n) :
    2 ≤ (cons hk c).length := by
  have := c.length_pos_of_pos hn
  rw [cons_length]
  omega

/-- A composition formed by prepending a positive block to a composition of a positive integer is
never the single-block composition. -/
theorem cons_ne_single {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (c : Composition n) :
    cons hk c ≠ single (k + n) (Nat.add_pos_left hk n) :=
  (two_le_length_iff_ne_single (Nat.add_pos_left hk n) (cons hk c)).mp
    (two_le_cons_length hk hn c)

@[simp] theorem cons_blocksFun_zero {k n : ℕ} (hk : 0 < k) (c : Composition n) :
    (cons hk c).blocksFun ⟨0, by rw [cons_length]; omega⟩ = k := by
  simp [blocksFun_eq_getElem]

@[simp] theorem cons_blocksFun_succ {k n : ℕ} (hk : 0 < k) (c : Composition n)
    (j : Fin c.length) :
    (cons hk c).blocksFun ⟨j.1 + 1, by rw [cons_length]; omega⟩ = c.blocksFun j := by
  simp [blocksFun_eq_getElem]

@[simp] theorem cons_sizeUpTo_succ {k n : ℕ} (hk : 0 < k) (c : Composition n) (m : ℕ) :
    (cons hk c).sizeUpTo (m + 1) = k + c.sizeUpTo m := by
  simp [sizeUpTo]

private theorem cons_blocksFun_zero_tail {n : ℕ} (c : Composition n) (h : 0 < c.length) :
    c.blocksFun ⟨0, h⟩ :: c.blocks.tail = c.blocks := by
  rw [blocksFun_eq_getElem]
  dsimp only
  rw [List.getElem_zero]
  exact List.cons_head_tail _

private def neSingleSuccInv {b : ℕ} (c : Composition (b + 1))
    (hc : c ≠ single (b + 1) (Nat.succ_pos b)) :
    Σ k : Fin b, Composition (b - k.1) :=
  have hlen : 0 < c.length := c.length_pos_of_pos (Nat.succ_pos b)
  let d := c.blocksFun ⟨0, hlen⟩
  have hd1 : 1 ≤ d := c.one_le_blocksFun ⟨0, hlen⟩
  have hdb : d < b + 1 := (ne_single_iff (Nat.succ_pos b)).mp hc ⟨0, hlen⟩
  ⟨⟨d - 1, by omega⟩,
    { blocks := c.blocks.tail
      blocks_pos := fun hm ↦ c.blocks_pos (List.mem_of_mem_tail hm)
      blocks_sum := by
        dsimp only [d]
        have hsum : (c.blocksFun ⟨0, hlen⟩ :: c.blocks.tail).sum = b + 1 :=
          (cons_blocksFun_zero_tail c hlen) ▸ c.blocks_sum
        rw [List.sum_cons] at hsum
        omega }⟩

/-- Splitting off the first block identifies `(k : Fin b) × Composition (b - k)` with the
compositions of `b + 1` distinct from `Composition.single (b + 1) _`. -/
def neSingleSuccEquiv (b : ℕ) :
    (Σ k : Fin b, Composition (b - k.1)) ≃
      {c : Composition (b + 1) // c ≠ single (b + 1) (Nat.succ_pos b)} where
  toFun p :=
    ⟨(cons (k := p.1.1 + 1) (Nat.zero_lt_succ _) p.2).cast (by have := p.1.2; omega),
      (two_le_length_iff_ne_single (Nat.succ_pos b) _).mp <| by
        rw [cast_length]
        exact two_le_cons_length (Nat.zero_lt_succ _) (by have := p.1.2; omega) p.2⟩
  invFun q := neSingleSuccInv q.1 q.2
  left_inv := fun ⟨k, c⟩ ↦ by
    dsimp only
    rcases hq : neSingleSuccInv
      ((cons (k := k.1 + 1) (Nat.zero_lt_succ _) c).cast (by have := k.2; omega)) _ with ⟨k', c'⟩
    have hk' : k' = k := Fin.ext <| by
      simpa [neSingleSuccInv] using
        congrArg (fun p : Σ j : Fin b, Composition (b - j.1) ↦ p.1.1) hq.symm
    subst hk'
    refine congrArg (Sigma.mk k') (Composition.ext ?_)
    simpa [neSingleSuccInv] using
      (congrArg (fun p : Σ j : Fin b, Composition (b - j.1) ↦ p.2.blocks) hq).symm
  right_inv := fun ⟨c, hc⟩ ↦ by
    apply Subtype.ext
    apply Composition.ext
    rw [cast_blocks, cons_blocks]
    dsimp only [neSingleSuccInv]
    have hlen : 0 < c.length := c.length_pos_of_pos (Nat.succ_pos b)
    rw [Nat.sub_add_cancel (c.one_le_blocksFun ⟨0, hlen⟩)]
    exact cons_blocksFun_zero_tail c hlen

@[simp] theorem coe_neSingleSuccEquiv_apply (b : ℕ) (p : Σ k : Fin b, Composition (b - k.1)) :
    (neSingleSuccEquiv b p).1 =
      (cons (k := p.1.1 + 1) (Nat.zero_lt_succ _) p.2).cast (by have := p.1.2; omega) := (rfl)

@[simp] theorem val_fst_neSingleSuccEquiv_symm (b : ℕ)
    (q : {c : Composition (b + 1) // c ≠ single (b + 1) (Nat.succ_pos b)}) :
    (((neSingleSuccEquiv b).symm q).1 : ℕ) =
      q.1.blocksFun ⟨0, q.1.length_pos_of_pos (Nat.succ_pos b)⟩ - 1 := (rfl)

@[simp] theorem snd_neSingleSuccEquiv_symm_blocks (b : ℕ)
    (q : {c : Composition (b + 1) // c ≠ single (b + 1) (Nat.succ_pos b)}) :
    ((neSingleSuccEquiv b).symm q).2.blocks = q.1.blocks.tail := (rfl)

end Composition
