/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Data.Finset.Inversions

import TauCeti.Data.Fin.Basic

/-!
# Signs of permutations, inversions, and signed-sum reindexing

An *inversion* of `σ : Equiv.Perm (Fin n)` is a pair of indices `i < j` with `σ j < σ i`. The
sign of `σ` is `(-1)` raised to the number of inversions. Mathlib exposes the sign as the product
`Equiv.Perm.sign_eq_prod_prod_Ioi`; this file turns that product into the cardinality of the
finite set of inversions, which is the form met by combinatorial permutation counts. It also
counts the inversions created by inserting a value at the first position and records the sign of a
shuffle of two ordered blocks, and that of a permutation reordering any number of consecutive
blocks. Finally, it uses the sign of a block swap to reindex signed sums over permutations when
rotating index blocks.

## Main results

* `Equiv.Perm.card_inversion_decomposeFin'Symm`: inserting `i` at the first position adds `i`
  inversions.
* `TauCeti.sign_eq_neg_one_pow_card_inversion`: the sign of a permutation `σ` of `Fin n` is
  `(-1)` to the number of its inversions `Finset.univ.inversions σ`.
* `Fin.sign_revPerm`: reversing `Fin n` has sign `(-1) ^ n.choose 2`.
* `TauCeti.sign_shuffle`: the sign of a shuffle permutation is a power of `-1`.
* `TauCeti.sign_finAddFlip_trans_finCongr`: the block swap of `Fin (m + n)`, which exchanges the
  first `m` indices with the last `n`, has sign `(-1) ^ (m * n)`.
* `Equiv.Perm.blockPerm` and `Equiv.Perm.sign_blockPerm`: the permutation of consecutive blocks of
  sizes `d i` that lists them in the order of a permutation `σ`, and its sign
  `(-1) ^ ∑ d (σ i) * d (σ j)` over the pairs `i < j` inverted by `σ`; it is even when all the
  sizes are even (`Equiv.Perm.sign_blockPerm_of_even`).
* `TauCeti.sum_sign_smul_permCongr_mul`: reindexing a signed sum over permutations along an
  equivalence followed by right multiplication.
* `TauCeti.sum_sign_smul_rotate_blocks`: reindexing a signed sum over permutations along a
  block swap moves the last block of `k` indices in front of the other `l + m` at the cost of
  the sign `(-1) ^ (k * (l + m))`; graded identities for iterated wedge products reorder their
  factors this way.

The sign of the block swap was first proved on the earlier Tau Ceti split branch at commit
`05c2722248` and is adapted here to current `main`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.3 and 1.5.
-/

public section

namespace Equiv.Perm

open _root_.Finset

/-- Inserting `i` at the first position creates exactly `i` additional inversions. -/
@[simp]
theorem card_inversion_decomposeFin'Symm {n : ℕ} (σ : Perm (Fin (n + 1)))
    (i : Fin (n + 2)) :
    (univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
      p.1 < p.2 ∧ decomposeFin'Symm i σ p.2 < decomposeFin'Symm i σ p.1).card =
      i.val + (univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
        p.1 < p.2 ∧ σ p.2 < σ p.1).card := by
  have hcount : (univ.filter fun j : Fin (n + 1) => j.castSucc < i).card = i.val := by
    simp only [Fin.lt_def, Fin.val_castSucc]
    rw [Fin.card_filter_val_lt, Nat.min_eq_right (by omega)]
  have hfirst : (∑ j : Fin (n + 1), if i.succAbove (σ j) < i then 1 else 0) = i.val := by
    simp only [Fin.succAbove_lt_iff]
    rw [Equiv.sum_comp σ (fun j => if j.castSucc < i then (1 : ℕ) else 0), sum_boole]
    exact hcount
  have h := card_univ_inversions_eq_comp_succAbove (decomposeFin'Symm i σ) 0
  simp only [inversions_univ, card_filter] at h
  simp only [Function.comp_apply, Fin.zero_succAbove, decomposeFin'Symm_succ,
    decomposeFin'Symm_zero, Fin.succAbove_lt_succAbove_iff, Fin.not_lt_zero, false_and,
    ite_false, sum_const_zero, add_zero] at h
  rw [Fin.sum_univ_succ] at h
  simpa only [card_filter, lt_self_iff_false, false_and, ite_false, zero_add, add_zero,
    Fin.succ_pos, true_and, decomposeFin'Symm_succ, hfirst, add_comm] using h

end Equiv.Perm

namespace TauCeti

variable {n : ℕ}

/-- The sign of a permutation of `Fin n` is `(-1)` raised to the number of its inversions
`Finset.univ.inversions σ`, the pairs of columns `i < j` whose values are in the opposite order. -/
theorem sign_eq_neg_one_pow_card_inversion (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Finset.univ.inversions σ).card := by
  classical
  rw [Finset.inversions_univ]
  have hIoi : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter fun j : Fin n => i < j := by
    intro i
    ext j
    simp
  have hprod :
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1)) =
        ∏ p ∈ Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2,
          (if σ p.1 < σ p.2 then (1 : ℤˣ) else -1) := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => by rw [hIoi i, Finset.prod_filter]
  have hinv :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
          (fun p => ¬ σ p.1 < σ p.2) =
        Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1 := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun p _ => ?_
    constructor
    · rintro ⟨hlt, hnot⟩
      have hne : σ p.1 ≠ σ p.2 := fun h => (ne_of_lt hlt) (σ.injective h)
      exact ⟨hlt, lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne)⟩
    · rintro ⟨hlt, hgt⟩
      exact ⟨hlt, not_lt.mpr (le_of_lt hgt)⟩
  rw [σ.sign_eq_prod_prod_Ioi, hprod, Finset.prod_ite]
  simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
  rw [hinv]

/-- Reversing the order of `Fin n` has sign `(-1) ^ n.choose 2`: every pair of indices is an
inversion. -/
@[simp]
theorem _root_.Fin.sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1) ^ n.choose 2 := by
  have h : (Finset.univ.filter fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ Fin.revPerm p.2 < Fin.revPerm p.1) =
      Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 :=
    Finset.filter_congr fun p _ => by simp
  rw [sign_eq_neg_one_pow_card_inversion, Finset.inversions_univ, h,
    Fintype.card_product_filter_lt, Fintype.card_fin]

private lemma card_inversion_finAddFlip_trans_finCongr (m n : ℕ) :
    (Finset.univ.filter fun p : Fin (m + n) × Fin (m + n) =>
      p.1 < p.2 ∧
        (finAddFlip.trans (finCongr (add_comm n m))) p.2 <
          (finAddFlip.trans (finCongr (add_comm n m))) p.1).card = m * n := by
  classical
  let e := Equiv.prodCongr
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  let f : Fin m × Fin n ↪ (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) :=
    ⟨Prod.map Sum.inl Sum.inr, Sum.inl_injective.prodMap Sum.inr_injective⟩
  calc
    _ = ((Finset.univ.filter fun p : (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) =>
        (e p).1 < (e p).2 ∧
          (finAddFlip.trans (finCongr (add_comm n m))) (e p).2 <
            (finAddFlip.trans (finCongr (add_comm n m))) (e p).1).map e.toEmbedding).card := by
      congr 1
      ext p
      simp [e]
    _ = m * n := by
      rw [Finset.card_map]
      have hfilter :
          (Finset.univ.filter fun p : (Fin m ⊕ Fin n) × (Fin m ⊕ Fin n) =>
            (e p).1 < (e p).2 ∧
              (finAddFlip.trans (finCongr (add_comm n m))) (e p).2 <
                (finAddFlip.trans (finCongr (add_comm n m))) (e p).1) =
            Finset.univ.map f := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, e, f,
          Equiv.prodCongr_apply, Function.Embedding.coeFn_mk, Prod.map_apply, Prod.exists,
          Prod.mk.injEq]
        rcases a with a | a <;> rcases b with b | b <;>
          simp [finAddFlip, Fin.ext_iff, ← Fin.val_fin_lt, Fin.val_castAdd, Fin.val_natAdd,
            Fin.val_addNat] <;> omega
      rw [hfilter, Finset.card_map, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]

/-- The block swap of `Fin (m + n)`, exchanging the first `m` indices with the last `n` while
preserving the order within each block, has sign `(-1) ^ (m * n)`: its inversions are exactly the
`m * n` pairs taken from different blocks. -/
theorem sign_finAddFlip_trans_finCongr (m n : ℕ) :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m))) = (-1) ^ (m * n) := by
  rw [sign_eq_neg_one_pow_card_inversion, Finset.inversions_univ,
    card_inversion_finAddFlip_trans_finCongr]

section

open _root_.Finset

variable {k : ℕ}

/-- The sign of a shuffle permutation.  Let `e : Fin k ⊕ Fin m ≃ Fin n` be increasing on each
summand, so that the images of `Sum.inl` form a `k`-element set `I` and the images of `Sum.inr`
form its complement.  Then the sign of the shuffle, viewed as a permutation of `Fin n`, is
`(-1)` raised to the sum of the elements of `I` plus the sum of the positions in the first
summand.

Mathlib records the same sign for the `k`-subset `I` as `Set.powersetCard.sign I`, and
`Set.powersetCard.sign_eq_permOfDisjoint_sign` identifies that with the shuffle sign below; the
present form is the one met by determinants reindexed along `finSumEquivOfFinset`. -/
theorem sign_shuffle {m : ℕ} (h : k + m = n) (e : Fin k ⊕ Fin m ≃ Fin n)
    (hl : StrictMono (e ∘ Sum.inl)) (hr : StrictMono (e ∘ Sum.inr)) :
    Equiv.Perm.sign ((finSumFinEquiv.trans (finCongr h)).symm.trans e) =
      (-1) ^ (∑ a, (e (.inl a) : ℕ) + ∑ a : Fin k, (a : ℕ)) := by
  have hl' (a b) : e (.inl a) < e (.inl b) ↔ a < b := hl.lt_iff_lt
  have hr' (a b) : e (.inr a) < e (.inr b) ↔ a < b := hr.lt_iff_lt
  have h₁ (a b : Fin k) : Fin.castAdd m a < Fin.castAdd m b ↔ a < b := Iff.rfl
  have h₂ (a : Fin k) (b : Fin m) : Fin.castAdd m a < Fin.natAdd k b := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h₃ {α : Type} [Preorder α] (a b : α) : ¬(a < b ∧ b < a) := fun h ↦ lt_asymm h.1 h.2
  -- The only inversions are pairs `(inl a, inr b)` with `e (inr b) < e (inl a)`.
  -- For each `a`, the number of such `b` is the position of `e (inl a)` minus `a`.
  have hcount (a : Fin k) : #{b | e (.inr b) < e (.inl a)} + a = (e (.inl a) : ℕ) := by
    rw [← Fin.card_Iio, ← Fin.card_Iio (e _), ← filter_gt_eq_Iio, ← filter_gt_eq_Iio]
    simp only [card_filter, ← e.sum_comp (fun _ ↦ ite _ _ _), Fintype.sum_sum_type, hl']
    ring
  -- Mathlib's product formula for the sign, with the interval `Iio` written as a filter, so that
  -- the double product can be reindexed along `E`.
  have hsign (τ : Equiv.Perm (Fin n)) :
      Equiv.Perm.sign τ = ∏ y, ∏ x, if x < y ∧ τ y < τ x then (-1 : ℤˣ) else 1 := by
    rw [τ.sign_eq_prod_prod_Iio]
    refine prod_congr rfl fun y _ ↦ ?_
    rw [← filter_gt_eq_Iio, prod_filter]
    refine prod_congr rfl fun x _ ↦ ?_
    split_ifs <;> grind [EmbeddingLike.apply_eq_iff_eq]
  set E := finSumFinEquiv.trans (finCongr h)
  rw [hsign, ← E.prod_comp]
  simp_rw [← E.prod_comp (fun _ ↦ ite _ _ _)]
  have hprod :
      (∏ x : Fin k ⊕ Fin m, ∏ i : Fin k ⊕ Fin m,
          if E i < E x ∧ (E.symm.trans e) (E x) < (E.symm.trans e) (E i) then (-1 : ℤˣ) else 1) =
        ∏ x : Fin m, ∏ y : Fin k,
          if e (Sum.inr x) < e (Sum.inl y) then (-1 : ℤˣ) else 1 := by
    simp [Fintype.prod_sum_type, E, hl', hr', h₁, h₂, (h₂ _ _).not_gt, h₃]
  rw [hprod, prod_comm, ← sum_congr rfl fun a _ ↦ hcount a, sum_add_distrib, add_assoc,
    ← two_mul, pow_add, pow_mul]
  simp [prod_ite, prod_pow_eq_pow_sum]

end

/-- Reindexing a signed sum over permutations by `τ ↦ c.permCongr τ * B` contributes the sign of
`B`. -/
theorem sum_sign_smul_permCongr_mul {a b : ℕ} {M : Type*} [AddCommGroup M]
    (c : Fin a ≃ Fin b) (B : Equiv.Perm (Fin b)) (f : Equiv.Perm (Fin b) → M) :
    ∑ τ : Equiv.Perm (Fin a), Equiv.Perm.sign τ • f (c.permCongr τ * B) =
      Equiv.Perm.sign B • ∑ σ : Equiv.Perm (Fin b), Equiv.Perm.sign σ • f σ := by
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (c.permCongr.trans (Equiv.mulRight B)) _ _ fun τ => ?_
  have hsign : Equiv.Perm.sign τ =
      Equiv.Perm.sign B * Equiv.Perm.sign (c.permCongr τ * B) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_permCongr, mul_comm, mul_assoc, ← sq]
    simp [Int.units_sq]
  simp only [Equiv.trans_apply, Equiv.coe_mulRight, hsign, mul_smul]

open Equiv in
/-- Rotating three blocks of indices in a signed sum over permutations: a summand reading its three
arguments off the blocks of sizes `l`, `m` and `k` of `Fin (l + m + k)`, in the order last, first,
second, sums to `(-1) ^ (k * (l + m))` times the same summand reading them off the blocks of sizes
`k`, `l` and `m` of `Fin (k + l + m)` in order. This is the reindexing along the block swap moving
the last `k` indices to the front. -/
theorem sum_sign_smul_rotate_blocks {γ M : Type*} [AddCommGroup M] {k l m : ℕ}
    (g : (Fin k → γ) → (Fin l → γ) → (Fin m → γ) → M) (v : Fin (k + l + m) → γ) :
    ∑ τ : Perm (Fin (l + m + k)), Perm.sign τ •
        g (fun i => v (Fin.cast (show l + m + k = k + l + m by omega)
            (τ (Fin.natAdd (l + m) i))))
          (fun j => v (Fin.cast (show l + m + k = k + l + m by omega)
            (τ (Fin.castAdd k (Fin.castAdd m j)))))
          (fun r => v (Fin.cast (show l + m + k = k + l + m by omega)
            (τ (Fin.castAdd k (Fin.natAdd l r))))) =
      (-1 : ℤˣ) ^ (k * (l + m)) • ∑ σ : Perm (Fin (k + l + m)), Perm.sign σ •
        g (fun i => v (σ (Fin.castAdd m (Fin.castAdd l i))))
          (fun j => v (σ (Fin.castAdd m (Fin.natAdd k j))))
          (fun r => v (σ (Fin.natAdd (k + l) r))) := by
  -- Reindex by `τ ↦ c τ c⁻¹ * B`, where `c` is the cast and `B` moves the last block of `k`
  -- indices to the front; `B` is the block swap of `Fin (k + (l + m))`, of sign
  -- `(-1) ^ (k * (l + m))`, conjugated by the associativity cast.
  set c : Fin (l + m + k) ≃ Fin (k + l + m) := finCongr (show l + m + k = k + l + m by omega)
  set d : Fin (k + (l + m)) ≃ Fin (k + l + m) := finCongr (Nat.add_assoc k l m).symm
  set B : Perm (Fin (k + l + m)) :=
    d.permCongr (finAddFlip.trans (finCongr (Nat.add_comm (l + m) k)))
  have hB : Perm.sign B = (-1) ^ (k * (l + m)) := by
    rw [Perm.sign_permCongr, sign_finAddFlip_trans_finCongr]
  have h₁ (i : Fin k) : B (Fin.castAdd m (Fin.castAdd l i)) = c (Fin.natAdd (l + m) i) := by
    have : d.symm (Fin.castAdd m (Fin.castAdd l i)) = Fin.castAdd (l + m) i := Fin.ext rfl
    simp only [B, Equiv.permCongr_apply, this, Equiv.trans_apply, finAddFlip_apply_castAdd]
    exact Fin.ext rfl
  have h₂ (j : Fin l) : B (Fin.castAdd m (Fin.natAdd k j)) =
      c (Fin.castAdd k (Fin.castAdd m j)) := by
    have : d.symm (Fin.castAdd m (Fin.natAdd k j)) = Fin.natAdd k (Fin.castAdd m j) := Fin.ext rfl
    simp only [B, Equiv.permCongr_apply, this, Equiv.trans_apply, finAddFlip_apply_natAdd]
    exact Fin.ext rfl
  have h₃ (r : Fin m) : B (Fin.natAdd (k + l) r) = c (Fin.castAdd k (Fin.natAdd l r)) := by
    have : d.symm (Fin.natAdd (k + l) r) = Fin.natAdd k (Fin.natAdd l r) :=
      Fin.ext (Nat.add_assoc k l r)
    simp only [B, Equiv.permCongr_apply, this, Equiv.trans_apply, finAddFlip_apply_natAdd]
    exact Fin.ext rfl
  let f : Perm (Fin (k + l + m)) → M := fun σ =>
    g (fun i => v (σ (Fin.castAdd m (Fin.castAdd l i))))
      (fun j => v (σ (Fin.castAdd m (Fin.natAdd k j))))
      (fun r => v (σ (Fin.natAdd (k + l) r)))
  calc
    _ = ∑ τ : Perm (Fin (l + m + k)), Perm.sign τ • f (c.permCongr τ * B) := by
      apply Finset.sum_congr rfl
      intro τ _
      simp only [f, Perm.mul_apply, h₁, h₂, h₃, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
      simp only [c, finCongr_apply]
    _ = _ := (sum_sign_smul_permCongr_mul c B f).trans (by rw [hB])

end TauCeti

/-! ### Permutations of consecutive blocks -/

namespace Equiv.Perm

open _root_.Finset TauCeti

variable {k : ℕ}

/-- The permutation of `Fin (∑ i, d i)` comparing two listings of consecutive blocks of sizes
`d i`. Block `i` of the listing in the order `σ 0, σ 1, …`, which has size `d (σ i)`, is sent to
block `σ i` of the listing in the order `0, 1, …`, preserving the order within each block
(`Equiv.Perm.blockPerm_apply`). -/
def blockPerm (σ : Equiv.Perm (Fin k)) (d : Fin k → ℕ) : Equiv.Perm (Fin (∑ i, d i)) :=
  (finCongr (Equiv.sum_comp σ d).symm).trans
    (finSigmaFinEquiv.symm.trans ((Equiv.sigmaCongrLeft σ).trans finSigmaFinEquiv))

/-- `blockPerm σ d` sends entry `a` of block `i` of the listing in the order of `σ` to entry `a` of
block `σ i` of the listing in the natural order. -/
@[simp]
theorem blockPerm_apply (σ : Equiv.Perm (Fin k)) (d : Fin k → ℕ) (i : Fin k) (a : Fin (d (σ i))) :
    blockPerm σ d (Fin.cast (Equiv.sum_comp σ d) (finSigmaFinEquiv ⟨i, a⟩)) =
      finSigmaFinEquiv ⟨σ i, a⟩ := by
  simp [blockPerm]

/-- The sign of a permutation of consecutive blocks. Each pair of blocks whose order `σ`
reverses contributes the sign `(-1) ^ (d (σ i) * d (σ j))`: the inversions of `blockPerm σ d`
are exactly the pairs of entries taken from such a pair of blocks. -/
theorem sign_blockPerm (σ : Equiv.Perm (Fin k)) (d : Fin k → ℕ) :
    Equiv.Perm.sign (blockPerm σ d) =
      (-1) ^ ∑ p ∈ univ.inversions σ, d (σ p.1) * d (σ p.2) := by
  rw [sign_eq_neg_one_pow_card_inversion, inversions_univ]
  congr 1
  -- Positions in the listing in the order of `σ`, and their images under `blockPerm σ d`.
  set ψ : ((i : Fin k) × Fin (d (σ i))) ≃ Fin (∑ i, d i) :=
    finSigmaFinEquiv.trans (finCongr (Equiv.sum_comp σ d))
  have hψ (x y) : ψ x < ψ y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ (x.2 : ℕ) < y.2 := by
    rw [← finSigmaFinEquiv_lt_finSigmaFinEquiv_iff]
    simp [ψ, Fin.lt_def]
  have hτ (x) : blockPerm σ d (ψ x) = finSigmaFinEquiv ⟨σ x.1, x.2⟩ := by
    obtain ⟨i, a⟩ := x
    simp [ψ]
  -- The inversions of `blockPerm σ d` are the pairs of entries of two blocks inverted by `σ`.
  have hinv (x y) : (ψ x < ψ y ∧ blockPerm σ d (ψ y) < blockPerm σ d (ψ x)) ↔
      x.1 < y.1 ∧ σ y.1 < σ x.1 := by
    rw [hψ, hτ, hτ, finSigmaFinEquiv_lt_finSigmaFinEquiv_iff]
    constructor
    · rintro ⟨h | ⟨h, h'⟩, h₂ | ⟨h₂, h₂'⟩⟩
      · exact ⟨h, h₂⟩
      · exact absurd h₂ (σ.injective.ne h.ne')
      · simp only at h₂
        rw [h] at h₂
        exact absurd h₂ (lt_irrefl _)
      · simp only at h₂'
        omega
    · rintro ⟨h, h₂⟩
      exact ⟨Or.inl h, Or.inl h₂⟩
  have hcard : ∑ p ∈ univ.inversions σ, d (σ p.1) * d (σ p.2) =
      #((univ.inversions σ).sigma fun p ↦ (univ : Finset (Fin (d (σ p.1)) × Fin (d (σ p.2))))) := by
    simp [card_sigma]
  rw [hcard]
  -- Pairs of entries correspond to pairs of blocks together with a position in each.
  let g (xy : ((i : Fin k) × Fin (d (σ i))) × ((i : Fin k) × Fin (d (σ i)))) :
      (p : Fin k × Fin k) × (Fin (d (σ p.1)) × Fin (d (σ p.2))) :=
    ⟨(xy.1.1, xy.2.1), (xy.1.2, xy.2.2)⟩
  refine card_nbij' (fun pq ↦ g (ψ.symm pq.1, ψ.symm pq.2))
    (fun x ↦ (ψ ⟨x.1.1, x.2.1⟩, ψ ⟨x.1.2, x.2.2⟩)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ h
    obtain ⟨x, rfl⟩ := ψ.surjective p
    obtain ⟨y, rfl⟩ := ψ.surjective q
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    simpa [g, mem_inversions] using (hinv x y).1 h
  · rintro ⟨⟨i, j⟩, a, c⟩ h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_inversions, mem_univ, true_and] at h
    simpa using (hinv ⟨i, a⟩ ⟨j, c⟩).2 h.1
  · rintro ⟨p, q⟩ -
    simp [g]
  · rintro ⟨⟨i, j⟩, a, c⟩ -
    simp only [Equiv.symm_apply_apply]
    rfl

/-- A permutation of consecutive blocks of even sizes is even. -/
theorem sign_blockPerm_of_even (σ : Equiv.Perm (Fin k)) {d : Fin k → ℕ} (hd : ∀ i, Even (d i)) :
    Equiv.Perm.sign (blockPerm σ d) = 1 := by
  rw [sign_blockPerm]
  exact Even.neg_one_pow (even_sum _ fun p _ ↦ (hd _).mul_right _)

end Equiv.Perm
