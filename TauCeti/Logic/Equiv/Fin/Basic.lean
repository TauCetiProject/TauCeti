/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring
import TauCeti.Data.Fin.Basic

/-!
# Equivalences for finite indices and consecutive blocks of natural numbers

The equivalence omitting the last finite index embeds preceding indices by `Fin.castSucc`.
The quotient-remainder equivalence identifies a natural number with a block number and a
position inside that block. This file records the induced block permutations and compatibility
of nested blocks with the finite-product indexing equivalence.
It also concatenates two finite blocks with the second block read in reverse order, and splits
the first pair off a doubly indexed family listed pair by pair through `finProdFinEquiv`, and
splits `Fin n` as `Fin (n - r) ⊕ Fin r` with the initial block of `r` indices moved to the end. The
index `finProdFinEquiv (i, c)` of `Fin (l * n)` lies among the first `k * n` exactly when `i < k`,
and is then the index `finProdFinEquiv (i, c)` of `Fin (k * n)`.

It also concatenates two finite blocks with the second block read in reverse order. For two
blocks of equal length, laid out as the bottom and the top row of a rectangle and read
counterclockwise around it, exchanging the two blocks reverses the concatenated order, and
reversing each block is reversing the concatenated order followed by a rotation by one block.
It also records transitivity of `finCongr` (`TauCeti.finCongr_trans`).
Finally, `TauCeti.apply_comp_finCycle` iterates a single-step rotation rule (`Fin.cons` to
`Fin.snoc`) along `finCycle`, and `TauCeti.apply_comp_finCycle_of_anticyclic` specializes it to
anticyclic functions.
`TauCeti.homotopyIndexEquiv` splits `Fin (n + 1) × Fin (n + 2)` into off-diagonal, diagonal, and
superdiagonal pairs.
-/

public section

namespace TauCeti

/-- Composing two `finCongr` equivalences gives the `finCongr` of the composed equality. -/
@[simp]
theorem finCongr_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) :
    (finCongr h₁).trans (finCongr h₂) = finCongr (h₁.trans h₂) := by
  ext; simp

/-- Omitting the last index embeds each preceding index by `Fin.castSucc`. -/
@[simp]
theorem finSuccAboveEquiv_last_apply (n : ℕ) (i : Fin n) :
    finSuccAboveEquiv (Fin.last n) i = ⟨i.castSucc, Fin.castSucc_ne_last i⟩ :=
  (finSuccAboveEquiv_apply (Fin.last n) i).trans
    (by apply Subtype.ext; exact Fin.succAbove_last_apply i)

/-- Concatenate two finite blocks, keeping the first in order and reversing the second. -/
def finSumFinRevEquiv (p q n : ℕ) (hpq : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  ((Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv).trans (finCongr hpq)

/-- The first block keeps its original index. -/
@[simp]
theorem finSumFinRevEquiv_inl_val (p q n : ℕ) (hpq : p + q = n) (i : Fin p) :
    (finSumFinRevEquiv p q n hpq (Sum.inl i) : ℕ) = i := by
  simp [finSumFinRevEquiv]

/-- The second block follows the first in reverse order. -/
@[simp]
theorem finSumFinRevEquiv_inr_val (p q n : ℕ) (hpq : p + q = n) (i : Fin q) :
    (finSumFinRevEquiv p q n hpq (Sum.inr i) : ℕ) = p + (q - 1 - i) := by
  simp [finSumFinRevEquiv, Fin.rev]
  omega

/-- Every index of the first block precedes every index of the second. -/
@[simp]
theorem finSumFinRevEquiv_inl_lt_inr (p q n : ℕ) (hpq : p + q = n) (i : Fin p) (j : Fin q) :
    finSumFinRevEquiv p q n hpq (Sum.inl i) < finSumFinRevEquiv p q n hpq (Sum.inr j) := by
  have := i.isLt
  rw [Fin.lt_def, finSumFinRevEquiv_inl_val, finSumFinRevEquiv_inr_val]
  omega

/-- No index of the second block precedes an index of the first. -/
@[simp]
theorem not_finSumFinRevEquiv_inr_lt_inl (p q n : ℕ) (hpq : p + q = n) (i : Fin p) (j : Fin q) :
    ¬finSumFinRevEquiv p q n hpq (Sum.inr j) < finSumFinRevEquiv p q n hpq (Sum.inl i) :=
  (finSumFinRevEquiv_inl_lt_inr p q n hpq i j).not_gt

/-- The first block is kept in order. -/
@[simp]
theorem finSumFinRevEquiv_inl_lt_inl_iff (p q n : ℕ) (hpq : p + q = n) {i i' : Fin p} :
    finSumFinRevEquiv p q n hpq (Sum.inl i) < finSumFinRevEquiv p q n hpq (Sum.inl i') ↔
      i < i' := by
  rw [Fin.lt_def, finSumFinRevEquiv_inl_val, finSumFinRevEquiv_inl_val, Fin.lt_def]

/-- The second block is read in reverse order. -/
@[simp]
theorem finSumFinRevEquiv_inr_lt_inr_iff (p q n : ℕ) (hpq : p + q = n) {j j' : Fin q} :
    finSumFinRevEquiv p q n hpq (Sum.inr j) < finSumFinRevEquiv p q n hpq (Sum.inr j') ↔
      j' < j := by
  have := j.isLt
  have := j'.isLt
  rw [Fin.lt_def, finSumFinRevEquiv_inr_val, finSumFinRevEquiv_inr_val, Fin.lt_def]
  omega

/-- The family `(b (0, 0), b (0, 1), b (1, 0), b (1, 1), …)` of a doubly indexed family, listed
pair by pair through `finProdFinEquiv`, splits off its first pair. -/
theorem comp_finProdFinEquiv_symm_succ {α : Type*} {m : ℕ} (b : Fin (m + 1) × Fin 2 → α) :
    (fun r : Fin (2 * (m + 1)) ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 (m + 1)) r))) =
      Matrix.vecCons (b (0, 0)) (Matrix.vecCons (b (0, 1))
        (fun r : Fin (2 * m) ↦
          (b ∘ Prod.map Fin.succ id) (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 m) r)))) := by
  ext r
  refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun r ↦ ?_) r) r
  · congr 1
    ext <;> simp [Fin.coe_divNat, Fin.coe_modNat]
  · congr 1
    ext <;> simp [Fin.coe_divNat, Fin.coe_modNat, fun k ↦ Nat.lt_succ_of_le (Nat.mod_le 1 k)]
  · simp only [Matrix.cons_val_succ]
    congr 1
    ext <;> simp [Fin.coe_divNat, Fin.coe_modNat] <;> omega

/-- The index `c + n * i` of `Fin (l * n)` is among the first `k * n` exactly when `i < k`. -/
theorem finProdFinEquiv_lt_mul_iff {k l n : ℕ} (i : Fin l) (c : Fin n) :
    (finProdFinEquiv (i, c) : ℕ) < k * n ↔ (i : ℕ) < k := by
  rw [← Nat.div_lt_iff_lt_mul c.pos, finProdFinEquiv_apply_val, Nat.add_mul_div_left _ _ c.pos,
    Nat.div_eq_of_lt c.isLt, zero_add]

/-- Reading the index `c + n * i` of `Fin (l * n)` with `i < k` in `Fin (k * n)` gives the index
`finProdFinEquiv (i, c)` of `Fin (k * n)`. -/
theorem mk_finProdFinEquiv {k l n : ℕ} {i : Fin l} (c : Fin n) (hi : (i : ℕ) < k) :
    (⟨finProdFinEquiv (i, c), (finProdFinEquiv_lt_mul_iff i c).2 hi⟩ : Fin (k * n)) =
      finProdFinEquiv (⟨i, hi⟩, c) :=
  Fin.ext (by simp [finProdFinEquiv_apply_val])

/-- For two blocks of equal length, exchanging the blocks reverses the concatenated order. -/
theorem finSumFinRevEquiv_swap {k n : ℕ} (h : k + k = n) (x : Fin k ⊕ Fin k) :
    finSumFinRevEquiv k k n h x.swap = (finSumFinRevEquiv k k n h x).rev := by
  subst h
  rcases x with i | j <;>
  · ext
    simp only [Sum.swap_inl, Sum.swap_inr, finSumFinRevEquiv_inl_val, finSumFinRevEquiv_inr_val,
      Fin.val_rev]
    omega

/-- For two blocks of equal length, reversing each block is reversing the concatenated order and
then rotating by the length of one block. -/
theorem finSumFinRevEquiv_map_rev {k n : ℕ} (h : k + k = n) (x : Fin k ⊕ Fin k) :
    finSumFinRevEquiv k k n h (Sum.map Fin.rev Fin.rev x) =
      (finRotate n ^ k) (finSumFinRevEquiv k k n h x).rev := by
  subst h
  ext
  rcases x with i | j
  · have := i.isLt
    simp only [Sum.map_inl, finSumFinRevEquiv_inl_val, Fin.coe_finRotate_pow, Fin.val_rev]
    rw [show k + k - (i + 1) + k = (k - (i + 1)) + (k + k) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · have := j.isLt
    simp only [Sum.map_inr, finSumFinRevEquiv_inr_val, Fin.coe_finRotate_pow, Fin.val_rev]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Shifting a tuple of length `n + 1` cyclically by `r` steps applies `f` `r` times whenever
moving the first entry to the end (`Fin.cons` to `Fin.snoc`) applies `f`. -/
theorem apply_comp_finCycle {α β : Type*} {n : ℕ} {a : (Fin (n + 1) → α) → β} {f : β → β}
    (hrot : ∀ (u : Fin n → α) (e : α), a (Fin.snoc u e) = f (a (Fin.cons e u)))
    (r : Fin (n + 1)) (w : Fin (n + 1) → α) :
    a (w ∘ finCycle r) = f^[r.val] (a w) := by
  have h1 (v : Fin (n + 1) → α) : a (v ∘ finRotate (n + 1)) = f (a v) := by
    have hv : v ∘ finRotate (n + 1) = Fin.snoc (Fin.tail v) (v 0) :=
      funext fun i ↦ by rw [Function.comp_apply, Fin.snoc_eq_cons_rotate, Fin.cons_self_tail]
    rw [hv, hrot, Fin.cons_self_tail]
  have hiter : ∀ (m : ℕ) (v : Fin (n + 1) → α), a (v ∘ (finRotate (n + 1))^[m]) = f^[m] (a v) := by
    intro m
    induction m with
    | zero => intro v; simp [Function.comp_id]
    | succ m ih =>
      intro v
      rw [Function.iterate_succ', ← Function.comp_assoc, ih, h1, ← Function.iterate_succ_apply]
  rw [finCycle_eq_finRotate_iterate]
  exact hiter r.val w

/-- Rotating an anticyclic function `a` on tuples by `finCycle r` multiplies it by
`(-1) ^ r.val`. -/
theorem apply_comp_finCycle_of_anticyclic {α β : Type*} [Monoid β] [HasDistribNeg β] {n : ℕ}
    {a : (Fin (n + 1) → α) → β}
    (hrot : ∀ (u : Fin n → α) (e : α), a (Fin.snoc u e) = -a (Fin.cons e u))
    (r : Fin (n + 1)) (w : Fin (n + 1) → α) :
    a (w ∘ finCycle r) = (-1 : β) ^ r.val * a w := by
  simpa only [mul_left_iterate_apply] using
    apply_comp_finCycle (f := ((-1 : β) * ·)) (fun u e ↦ by simpa using hrot u e) r w

/-- The equivalence `Fin n ≃ Fin (n - r) ⊕ Fin r` sending the first `r` indices to the second
summand and the last `n - r` indices to the first summand, both in order. It moves an initial
block of `r` indices to the end. -/
def finSubSumEquiv {r n : ℕ} (h : r ≤ n) : Fin n ≃ Fin (n - r) ⊕ Fin r :=
  (finCongr (Nat.add_sub_cancel' h).symm).trans (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))

/-- The equivalence `Fin n ≃ Fin (n - r) ⊕ Fin r` sends the index `j < r` to `inr j`. -/
@[simp]
theorem finSubSumEquiv_symm_inr {r n : ℕ} (h : r ≤ n) (j : Fin r) :
    (finSubSumEquiv h).symm (Sum.inr j) = Fin.castLE h j := by
  ext
  simp [finSubSumEquiv]

/-- The equivalence `Fin n ≃ Fin (n - r) ⊕ Fin r` sends the index `r + i` to `inl i`. -/
@[simp]
theorem coe_finSubSumEquiv_symm_inl {r n : ℕ} (h : r ≤ n) (i : Fin (n - r)) :
    ((finSubSumEquiv h).symm (Sum.inl i) : ℕ) = r + i := by
  simp [finSubSumEquiv]

/-- The equivalence `Fin n ≃ Fin (n - r) ⊕ Fin r` sends the index `j < r` to `inr j`. -/
@[simp]
theorem finSubSumEquiv_castLE {r n : ℕ} (h : r ≤ n) (j : Fin r) :
    finSubSumEquiv h (Fin.castLE h j) = Sum.inr j :=
  (finSubSumEquiv h).eq_symm_apply.1 (finSubSumEquiv_symm_inr h j).symm

/-- The equivalence `Fin n ≃ Fin (n - r) ⊕ Fin r` sends an index `i ≥ r` to `inl (i - r)`. -/
theorem finSubSumEquiv_apply_of_le {r n : ℕ} (h : r ≤ n) {i : Fin n} (hi : r ≤ i) :
    finSubSumEquiv h i = Sum.inl ⟨i - r, by omega⟩ := by
  rw [← Equiv.eq_symm_apply]
  ext
  simp only [coe_finSubSumEquiv_symm_inl]
  omega

/-- Reindexing equivalence splitting `Fin (n + 1) × Fin (n + 2)` into off-diagonal pairs
`(m, k') ∈ Fin (n + 1) × Fin n` and the diagonal and superdiagonal copies of `Fin (n + 1)`. -/
def homotopyIndexEquiv (n : ℕ) :
    (Fin (n + 1) × Fin n) ⊕ (Fin (n + 1) ⊕ Fin (n + 1)) ≃ Fin (n + 1) × Fin (n + 2) where
  toFun
    | .inl (m, k') => if (m : ℕ) ≤ (k' : ℕ) then (k'.succ, m.castSucc) else (k'.castSucc, m.succ)
    | .inr (.inl k) => (k, k.castSucc)
    | .inr (.inr k) => (k, k.succ)
  invFun x :=
    if _ : (x.2 : ℕ) < (x.1 : ℕ) then .inl (⟨x.2, by omega⟩, ⟨x.1 - 1, by omega⟩)
    else if _ : (x.2 : ℕ) = (x.1 : ℕ) then .inr (.inl x.1)
    else if _ : (x.2 : ℕ) = (x.1 : ℕ) + 1 then .inr (.inr x.1)
    else .inl (⟨x.2 - 1, by omega⟩, ⟨x.1, by omega⟩)
  left_inv := by
    rintro (⟨m, k'⟩ | k | k)
    · by_cases hmk : (m : ℕ) ≤ (k' : ℕ)
      · simp [hmk, show (m : ℕ) < (k' : ℕ) + 1 by omega]
      · simp [hmk, show ¬(m : ℕ) + 1 < k' by omega, show ¬(m : ℕ) + 1 = k' by omega,
          show ¬(m : ℕ) = k' by omega]
    · simp
    · simp [show ¬(k : ℕ) + 1 < k by omega]
  right_inv := by
    rintro ⟨k, i⟩; simp only; split_ifs with h1 h2 h3
    · simp [show (i : ℕ) ≤ (k : ℕ) - 1 by omega, Fin.ext_iff]; omega
    · ext <;> simp [h2]
    · ext <;> simp [h3]
    · simp [show ¬(i : ℕ) - 1 ≤ k by omega, Fin.ext_iff]; omega

/-- Off-diagonal action of `homotopyIndexEquiv`. -/
@[simp] theorem homotopyIndexEquiv_inl (n : ℕ) (m : Fin (n + 1)) (k' : Fin n) :
    homotopyIndexEquiv n (.inl (m, k')) =
      if (m : ℕ) ≤ (k' : ℕ) then (k'.succ, m.castSucc) else (k'.castSucc, m.succ) := (rfl)
/-- Diagonal action of `homotopyIndexEquiv`. -/
@[simp] theorem homotopyIndexEquiv_inr_inl (n : ℕ) (k : Fin (n + 1)) :
    homotopyIndexEquiv n (.inr (.inl k)) = (k, k.castSucc) := (rfl)
/-- Superdiagonal action of `homotopyIndexEquiv`. -/
@[simp] theorem homotopyIndexEquiv_inr_inr (n : ℕ) (k : Fin (n + 1)) :
    homotopyIndexEquiv n (.inr (.inr k)) = (k, k.succ) := (rfl)

end TauCeti

/-- The permutation of path coordinates that permutes the consecutive blocks of width `m` by `τ`
and preserves the position inside each block. -/
def _root_.Nat.blockPerm (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) : Equiv.Perm ℕ :=
  (Nat.divModEquiv m).symm.permCongr (Equiv.prodCongr τ (Equiv.refl (Fin m)))

/-- The block permutation moves position `j` of block `i` to position `j` of block `τ i`. -/
@[simp]
theorem _root_.Nat.blockPerm_mul_add (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) (i : ℕ) (j : Fin m) :
    Nat.blockPerm m τ (i * m + j) = τ i * m + j := by
  have h (k : ℕ) : k * m + (j : ℕ) = (Nat.divModEquiv m).symm (k, j) :=
    (Nat.divModEquiv_symm_apply m (k, j)).symm
  -- Keep the indices in `divModEquiv` form so that `simp` cancels the equivalence.
  rw [h, h]
  simp [Nat.blockPerm, -Nat.divModEquiv_symm_apply]

/-- Flattening nested finite blocks agrees with the quotient-remainder inverse. -/
theorem Nat.divModEquiv_symm_finProdFinEquiv (m n : ℕ) [NeZero m] [NeZero n]
    (i : ℕ) (r : Fin n) (j : Fin m) :
    (Nat.divModEquiv (n * m)).symm (i, finProdFinEquiv (r, j)) =
      (Nat.divModEquiv m).symm (i * n + r, j) := by
  -- Evaluate the inverse quotient-remainder maps and the underlying natural number of the
  -- finite-product index by definition; this leaves a polynomial identity for `ring`.
  change i * (n * m) + (j + m * r) = (i * n + r) * m + j
  ring
