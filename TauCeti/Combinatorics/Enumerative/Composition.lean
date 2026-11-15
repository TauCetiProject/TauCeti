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

This file provides combinatorial lemmas for `Composition` supplementing
`Mathlib.Combinatorics.Enumerative.Composition`:

* `Composition.blocksFun_eq_getElem`, `Composition.cast_length`, and `Composition.cast_blocksFun`:
  `c.blocksFun i` agrees with `c.blocks[i]`, and `Composition.cast` preserves `length` and
  `blocksFun`.
* `Composition.sizeUpTo_eq_sum_blocksFun` and `Composition.coe_embedding_eq_finSigmaFinEquiv`:
  the prefix sum `c.sizeUpTo i` is the `Fin`-indexed sum of `c.blocksFun`, so the block embedding
  `c.embedding` agrees on `ℕ` with `finSigmaFinEquiv`.
* `Composition.two_le_length_iff_ne_single`: a composition of a positive integer has at least two
  blocks if and only if it is not `Composition.single`.
* `Composition.cons` and `Composition.neSingleSuccEquiv`: prepending a first block of size `k + 1`
  identifies `(k : Fin b) × Composition (b - k)` with the compositions of `b + 1` distinct from
  `Composition.single (b + 1) _`.
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
  rw [blocksFun_eq_getElem, blocksFun_eq_getElem]
  simp only [cast_blocks, Fin.val_cast]

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
  rw [ne_eq, eq_single_iff_length hn]
  have hpos : 0 < c.length := c.length_pos_of_pos hn
  omega

/-- Prepend a first block of size `k + 1` (with `k < b`) to a composition of `b - k`, producing a
composition of `b + 1`. -/
def cons {b k : ℕ} (hk : k < b) (c : Composition (b - k)) : Composition (b + 1) where
  blocks := (k + 1) :: c.blocks
  blocks_pos := by
    rintro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Nat.succ_pos k
    · exact c.blocks_pos hm
  blocks_sum := by
    rw [List.sum_cons, c.blocks_sum]
    omega

@[simp] theorem cons_blocks {b k : ℕ} (hk : k < b) (c : Composition (b - k)) :
    (cons hk c).blocks = (k + 1) :: c.blocks := (rfl)

@[simp] theorem cons_length {b k : ℕ} (hk : k < b) (c : Composition (b - k)) :
    (cons hk c).length = c.length + 1 := by
  rw [← blocks_length, cons_blocks, List.length_cons, blocks_length]

/-- Prepending a block via `cons` always yields a composition of length at least two. -/
theorem two_le_cons_length {b k : ℕ} (hk : k < b) (c : Composition (b - k)) :
    2 ≤ (cons hk c).length := by
  have hc : 0 < c.length := c.length_pos_of_pos (by omega)
  rw [cons_length]
  omega

/-- A composition formed by `cons` is never the single-block composition. -/
theorem cons_ne_single {b k : ℕ} (hk : k < b) (c : Composition (b - k)) :
    cons hk c ≠ single (b + 1) (Nat.succ_pos b) :=
  (two_le_length_iff_ne_single (Nat.succ_pos b) (cons hk c)).mp (two_le_cons_length hk c)

@[simp] theorem cons_blocksFun_zero {b k : ℕ} (hk : k < b) (c : Composition (b - k)) :
    (cons hk c).blocksFun ⟨0, by rw [cons_length]; omega⟩ = k + 1 := by
  rw [blocksFun_eq_getElem]
  simp

@[simp] theorem cons_blocksFun_succ {b k : ℕ} (hk : k < b) (c : Composition (b - k))
    (j : Fin c.length) :
    (cons hk c).blocksFun ⟨j.1 + 1, by rw [cons_length]; omega⟩ = c.blocksFun j := by
  rw [blocksFun_eq_getElem, blocksFun_eq_getElem]
  simp

@[simp] theorem cons_sizeUpTo_succ {b k : ℕ} (hk : k < b) (c : Composition (b - k))
    {m : ℕ} (hm : m ≤ c.length) :
    (cons hk c).sizeUpTo (m + 1) = k + 1 + c.sizeUpTo m := by
  induction m with
  | zero =>
    rw [(cons hk c).sizeUpTo_succ (by rw [cons_length]; omega), sizeUpTo_zero, sizeUpTo_zero]
    simp
  | succ m ih =>
    rw [(cons hk c).sizeUpTo_succ (by rw [cons_length]; omega), ih (Nat.le_of_succ_le hm),
      c.sizeUpTo_succ hm]
    simp [add_assoc]

/-- Head-tail inverse map for `neSingleSuccEquiv`, splitting off the first block `d` as
`⟨d - 1, tail⟩`. -/
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
        have hcons : c.blocksFun ⟨0, hlen⟩ :: c.blocks.tail = c.blocks := by
          rw [blocksFun_eq_getElem]
          change c.blocks[0] :: c.blocks.tail = c.blocks
          rw [List.getElem_zero]
          exact List.cons_head_tail _
        have hsum : (c.blocksFun ⟨0, hlen⟩ :: c.blocks.tail).sum = b + 1 := hcons ▸ c.blocks_sum
        rw [List.sum_cons] at hsum
        omega }⟩

/-- Splitting off the first block identifies `(k : Fin b) × Composition (b - k)` with the
compositions of `b + 1` distinct from `Composition.single (b + 1) _`. -/
def neSingleSuccEquiv (b : ℕ) :
    (Σ k : Fin b, Composition (b - k.1)) ≃
      {c : Composition (b + 1) // c ≠ single (b + 1) (Nat.succ_pos b)} where
  toFun p := ⟨cons p.1.2 p.2, cons_ne_single p.1.2 p.2⟩
  invFun q := neSingleSuccInv q.1 q.2
  left_inv := fun ⟨k, c⟩ ↦ by
    change neSingleSuccInv (cons k.2 c) (cons_ne_single k.2 c) = ⟨k, c⟩
    rcases hq : neSingleSuccInv (cons k.2 c) (cons_ne_single k.2 c) with ⟨k', c'⟩
    have hk' : k' = k := Fin.ext <| by
      have h1 := congrArg (fun p : Σ j : Fin b, Composition (b - j.1) ↦ p.1.1) hq.symm
      simpa [neSingleSuccInv] using h1
    subst hk'
    refine congrArg (Sigma.mk k') (Composition.ext ?_)
    have hb := congrArg (fun p : Σ j : Fin b, Composition (b - j.1) ↦ p.2.blocks) hq
    rw [← hb]
    simp [neSingleSuccInv]
  right_inv := fun ⟨c, hc⟩ ↦ by
    apply Subtype.ext
    apply Composition.ext
    rw [cons_blocks]
    dsimp only [neSingleSuccInv]
    have hlen : 0 < c.length := c.length_pos_of_pos (Nat.succ_pos b)
    have hd1 : 1 ≤ c.blocksFun ⟨0, hlen⟩ := c.one_le_blocksFun ⟨0, hlen⟩
    rw [Nat.sub_add_cancel hd1, blocksFun_eq_getElem]
    change c.blocks[0] :: c.blocks.tail = c.blocks
    rw [List.getElem_zero]
    exact List.cons_head_tail _

@[simp] theorem coe_neSingleSuccEquiv_apply (b : ℕ) (p : Σ k : Fin b, Composition (b - k.1)) :
    (neSingleSuccEquiv b p).1 = cons p.1.2 p.2 := (rfl)

end Composition
