/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Sort
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Signs of permutations, inversions, and signed-sum reindexing

An *inversion* of `σ : Equiv.Perm (Fin n)` is a pair of indices `i < j` with `σ j < σ i`. The
sign of `σ` is `(-1)` raised to the number of inversions. Mathlib exposes the sign as the product
`Equiv.Perm.sign_eq_prod_prod_Ioi`; this file turns that product into the cardinality of the
finite set of inversions, which is the form met by combinatorial permutation counts. It also
records the sign of a shuffle and the sign of the shuffle that lists a finset followed by its
complement. Finally, it uses the sign of a block swap to reindex signed sums over permutations
when rotating index blocks.

## Main results

* `TauCeti.sign_eq_neg_one_pow_card_inversion`: the sign of a permutation of `Fin n` is
  `(-1)` to the number of its inversions.
* `TauCeti.sign_shuffle`: the sign of a shuffle permutation is a power of `-1`.
* `TauCeti.sign_finSumEquivOfFinset`: the sign of the shuffle listing a finset followed by
  its complement.
* `TauCeti.sign_finAddFlip_trans_finCongr`: the block swap of `Fin (m + n)`, which exchanges the
  first `m` indices with the last `n`, has sign `(-1) ^ (m * n)`.
* `TauCeti.sum_sign_smul_permCongr_mul`: reindexing a signed sum over permutations along an
  equivalence followed by right multiplication.
* `TauCeti.sum_sign_smul_rotate_blocks`: reindexing a signed sum over permutations along a
  block swap moves the last block of `k` indices in front of the other `l + m` at the cost of
  the sign `(-1) ^ (k * (l + m))`; graded identities for iterated wedge products reorder their
  factors this way.

The sign of the block swap was first proved on the earlier Tau Ceti split branch at commit
`05c2722248` and is adapted here to current `main`.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- The sign of a permutation of `Fin n` is `(-1)` raised to the number of its inversions, the
pairs of columns `i < j` whose values are in the opposite order. -/
theorem sign_eq_neg_one_pow_card_inversion (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ σ p.2 < σ p.1).card := by
  classical
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
  rw [sign_eq_neg_one_pow_card_inversion, card_inversion_finAddFlip_trans_finCongr]

section

open _root_.Finset

variable {k : ℕ}

/-- The sign of a permutation of `Fin n`, written as a product over its inversions. -/
private theorem sign_eq_prod_ite (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = ∏ y, ∏ x, if x < y ∧ σ y < σ x then -1 else 1 := by
  rw [σ.sign_eq_prod_prod_Iio]
  refine prod_congr rfl fun y _ ↦ ?_
  rw [← filter_gt_eq_Iio, prod_filter]
  refine prod_congr rfl fun x _ ↦ ?_
  split_ifs <;> grind [EmbeddingLike.apply_eq_iff_eq]

/-- The sign of a shuffle permutation.  Let `e : Fin k ⊕ Fin m ≃ Fin n` be increasing on each
summand, so that the images of `Sum.inl` form a `k`-element set `I` and the images of `Sum.inr`
form its complement.  Then the sign of the shuffle, viewed as a permutation of `Fin n`, is
`(-1)` raised to the sum of the elements of `I` plus the sum of the positions in the first
summand. -/
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
    simp only [card_filter, ← e.sum_comp (fun x ↦ ite _ _ _), Fintype.sum_sum_type, hl']
    ring
  set E := finSumFinEquiv.trans (finCongr h)
  rw [sign_eq_prod_ite, ← E.prod_comp]
  simp_rw [← E.prod_comp (fun x ↦ ite _ _ _)]
  have hprod :
      (∏ x : Fin k ⊕ Fin m, ∏ i : Fin k ⊕ Fin m,
          if E i < E x ∧ (E.symm.trans e) (E x) < (E.symm.trans e) (E i) then (-1 : ℤˣ) else 1) =
        ∏ x : Fin m, ∏ y : Fin k,
          if e (Sum.inr x) < e (Sum.inl y) then (-1 : ℤˣ) else 1 := by
    simp [Fintype.prod_sum_type, E, hl', hr', h₁, h₂, (h₂ _ _).not_gt, h₃]
  rw [hprod, prod_comm, ← sum_congr rfl fun a _ ↦ hcount a, sum_add_distrib, add_assoc,
    ← two_mul, pow_add, pow_mul]
  simp [prod_ite, prod_pow_eq_pow_sum]

/-- The sign of the shuffle that lists `I` followed by its complement. -/
theorem sign_finSumEquivOfFinset (I : Finset (Fin n)) (hI : #I = k)
    (hI' : #Iᶜ = n - k := (card_compl I).trans (by rw [Fintype.card_fin, hI]))
    (h : k + (n - k) = n :=
      Nat.add_sub_of_le (hI ▸ (I.card_le_univ.trans (le_of_eq (Fintype.card_fin n))))) :
    Equiv.Perm.sign ((finSumFinEquiv.trans (finCongr h)).symm.trans (finSumEquivOfFinset hI hI')) =
      (-1) ^ (∑ i ∈ I, (i : ℕ) + ∑ a : Fin k, (a : ℕ)) := by
  rw [sign_shuffle h (finSumEquivOfFinset hI hI') (I.orderEmbOfFin hI).strictMono
    (Iᶜ.orderEmbOfFin hI').strictMono]
  simp only [finSumEquivOfFinset_inl]
  conv_rhs => rw [← I.map_orderEmbOfFin_univ hI, sum_map]
  rfl

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
