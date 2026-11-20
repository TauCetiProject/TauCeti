/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.GroupTheory.Perm.Inversion

/-!
# Block and interleaved orders of a basis of pairs

A basis `B` indexed by `Fin n × Fin 2` consists of `n` pairs `(B (i, 0), B (i, 1))`. It can be
listed in two natural orders:

* the **interleaved** order `(B (0, 0), B (0, 1), B (1, 0), B (1, 1), …)`, the reindexing of `B`
  along `finProdFinEquiv`;
* the **block** order `(B (0, 0), …, B (n - 1, 0), B (0, 1), …, B (n - 1, 1))`, all first members
  before all second members.

The two orders differ by the shuffle placing the first block at the even positions and the second
block at the odd positions. Its inversions are the pairs `(B (i, 1), B (j, 0))` with `i < j`, so
there are `n.choose 2 = n (n - 1) / 2` of them, and the two orientations differ by
`(-1) ^ n.choose 2` (`Module.Basis.orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex`).

For a complex vector space and a real basis `(v₁, …, vₙ)` of a maximal totally real subspace, the
interleaved order `(v₁, i v₁, …, vₙ, i vₙ)` gives the complex orientation, while the block order
`(v₁, …, vₙ, i v₁, …, i vₙ)` is the orientation of the subspace followed by its `i`-image. So the
identification of a totally real subspace with its normal space by the complex structure changes
the induced orientation by `(-1) ^ n.choose 2`: it preserves it for `n = 1` and reverses it for
`n = 2`. This is the sign behind the self-intersection `-2` of a Lagrangian sphere in a symplectic
four-manifold.

## Main results

* `Module.Basis.orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex`: a basis listing
  the pairs of `B` in block order has the orientation `(-1) ^ n.choose 2` times that of `B`
  listed in interleaved order.
-/

public section

open Module

namespace Module.Basis

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] {n : ℕ}

/-- The interleaving of two copies of `Fin n` into `Fin (n + n)`: the first copy goes to the even
positions and the second copy to the odd positions, `inl i ↦ 2 i` and `inr i ↦ 2 i + 1`. -/
private def interleave (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (n + n) where
  toFun := Sum.elim (fun i ↦ ⟨2 * i, by omega⟩) (fun i ↦ ⟨2 * i + 1, by omega⟩)
  invFun j := if (j : ℕ) % 2 = 0 then Sum.inl ⟨j / 2, by omega⟩ else Sum.inr ⟨j / 2, by omega⟩
  left_inv := by
    rintro (i | i)
    · simp
    · simp only [Sum.elim_inr, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.one_mod,
        Nat.one_ne_zero, ↓reduceIte, Sum.inr.injEq]
      ext
      simp only
      omega
  right_inv j := by
    by_cases h : (j : ℕ) % 2 = 0
    · simp only [h, ↓reduceIte, Sum.elim_inl]
      ext
      simp only
      omega
    · simp only [h, ↓reduceIte, Sum.elim_inr]
      ext
      simp only
      omega

/-- The sum of the positions `0, 1, …, n - 1` is `n.choose 2`. -/
private theorem sum_val_eq_choose_two (n : ℕ) : ∑ a : Fin n, (a : ℕ) = n.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ i) n, Finset.sum_range_id, Nat.choose_two_right]

/-- The shuffle sending the `i`-th index of the first block of `Fin (n + n)` to position `2 i` and
the `i`-th index of the second block to position `2 i + 1` has sign `(-1) ^ n.choose 2`. -/
private theorem sign_interleave (n : ℕ) :
    Equiv.Perm.sign (finSumFinEquiv.symm.trans (interleave n)) = (-1) ^ n.choose 2 := by
  have h := TauCeti.sign_shuffle (k := n) (m := n) (n := n + n) rfl (interleave n)
    (fun i j hij ↦ by
      have : (i : ℕ) < j := hij
      simp only [Function.comp_apply, interleave, Equiv.coe_fn_mk, Sum.elim_inl, Fin.mk_lt_mk]
      omega)
    (fun i j hij ↦ by
      have : (i : ℕ) < j := hij
      simp only [Function.comp_apply, interleave, Equiv.coe_fn_mk, Sum.elim_inr, Fin.mk_lt_mk]
      omega)
  simp only [finCongr_refl, Equiv.trans_refl] at h
  rw [h]
  simp only [interleave, Equiv.coe_fn_mk, Sum.elim_inl, ← Finset.mul_sum, sum_val_eq_choose_two]
  -- `(-1) ^ (2 s + s) = ((-1) ^ 3) ^ s = (-1) ^ s`.
  rw [← add_one_mul, pow_mul, Odd.neg_one_pow (by decide)]

/-- **Block versus interleaved order.** Let `B` be a basis indexed by `Fin n × Fin 2`, and let `c`
be the basis listing the pairs of `B` in block order: first `B (0, 0), …, B (n - 1, 0)`, then
`B (0, 1), …, B (n - 1, 1)`. Its orientation is `(-1) ^ n.choose 2` times that of the interleaved
listing `B (0, 0), B (0, 1), B (1, 0), B (1, 1), …`. -/
theorem orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex
    (B : Basis (Fin n × Fin 2) R M) (c : Basis (Fin (n + n)) R M)
    (h₀ : ∀ i, c (Fin.castAdd n i) = B (i, 0)) (h₁ : ∀ i, c (Fin.natAdd n i) = B (i, 1)) :
    c.orientation = (-1 : Rˣ) ^ n.choose 2 •
      (B.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))).orientation := by
  set σ : Equiv.Perm (Fin (n + n)) := finSumFinEquiv.symm.trans (interleave n)
  -- `c` is the interleaved basis read along the shuffle `σ`.
  have hc : c = (B.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))).reindex σ.symm := by
    refine Basis.eq_of_apply_eq fun j ↦ Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · rw [h₀, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_symm]
      congr 1
      apply (finProdFinEquiv.trans (finCongr (Nat.mul_two n))).injective
      simp only [σ, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.apply_symm_apply]
      ext
      simp [interleave, Nat.mul_comm]
    · rw [h₁, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_symm]
      congr 1
      apply (finProdFinEquiv.trans (finCongr (Nat.mul_two n))).injective
      simp only [σ, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.apply_symm_apply]
      ext
      simp [interleave, Nat.mul_comm, Nat.add_comm]
  rw [hc, Basis.orientation_reindex, Orientation.reindex_perm, Equiv.Perm.sign_symm,
    sign_interleave]
  simp

end Module.Basis
