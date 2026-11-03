/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import TauCeti.LinearAlgebra.Matrix.KroneckerPower
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination

/-!
# Matrices commuting with the Kronecker powers of orthogonal matrices

Let `M` be a matrix with rows and columns indexed by `κ → ι` which commutes with the Kronecker
power `A.kroneckerPower κ` of every matrix `A` with `Aᵀ * A = 1`. The signed permutation matrices
are orthogonal, and testing `M` against their Kronecker powers constrains its entries:

* relabelling every index by a permutation of `ι` does not change an entry of `M`;
* when `2 ≠ 0` and there are no zero divisors, an entry of `M` vanishes as soon as some label
  occurs an odd number of times among the row index and an even number of times among the column
  index, or the reverse: the diagonal sign matrix negating that label acts on the row and on the
  column with opposite signs.

These are the first steps of the description of the commutant of the orthogonal group on a tensor
power by Brauer diagrams.

## Main results

* `Matrix.apply_comp_mul_prod_of_commute_kroneckerPower`: invariance under a signed permutation.
* `Matrix.apply_comp_comp_of_commute_kroneckerPower`: invariance under relabelling.
* `Matrix.apply_eq_zero_of_commute_kroneckerPower`: the parity constraint on the entries.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {M : Matrix (κ → ι) (κ → ι) R}

/-- A matrix commuting with the Kronecker powers of all orthogonal matrices is invariant under the
signed permutation matrix sending `e_j` to `d j • e_(σ j)`. -/
theorem apply_comp_mul_prod_of_commute_kroneckerPower
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower κ))
    (σ : Equiv.Perm ι) {d : ι → R} (hd : ∀ i, d i * d i = 1) (v u : κ → ι) :
    M (σ ∘ v) (σ ∘ u) * ∏ i, d (u i) = (∏ i, d (v i)) * M v u := by
  set A : Matrix ι ι R := Matrix.of fun i j => if i = σ j then d j else 0 with hAdef
  have hA : Aᵀ * A = 1 := by
    ext j j'
    simp only [hAdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, ite_mul,
      zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      σ.injective.eq_iff, Matrix.one_apply]
    split_ifs with h <;> simp_all
  have hK : ∀ w x : κ → ι, A.kroneckerPower κ w x = if w = σ ∘ x then ∏ i, d (x i) else 0 := by
    intro w x
    simp [hAdef, Finset.prod_ite_zero, funext_iff]
  have h := congrFun (congrFun (hM A hA).eq (σ ∘ v)) u
  have hinj : ∀ w : κ → ι, (σ ∘ v = σ ∘ w) ↔ v = w := fun w => σ.injective.comp_left.eq_iff
  simp only [Matrix.mul_apply, hK, mul_ite, mul_zero, ite_mul, zero_mul, hinj] at h
  simpa using h

/-- A matrix commuting with the Kronecker powers of all orthogonal matrices is invariant under
relabelling by a permutation. -/
theorem apply_comp_comp_of_commute_kroneckerPower
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower κ))
    (σ : Equiv.Perm ι) (v u : κ → ι) : M (σ ∘ v) (σ ∘ u) = M v u := by
  simpa using apply_comp_mul_prod_of_commute_kroneckerPower hM σ (d := fun _ => 1)
    (fun _ => one_mul 1) v u

/-- **The parity constraint.** An entry of a matrix commuting with the Kronecker powers of all
orthogonal matrices vanishes when a label `a` occurs an even number of times in the row index and
an odd number of times in the column index, or the reverse: the diagonal sign matrix negating `a`
acts on the row and on the column with opposite signs. -/
theorem apply_eq_zero_of_commute_kroneckerPower [NoZeroDivisors R]
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower κ))
    (h2 : (2 : R) ≠ 0) {v u : κ → ι} (a : ι)
    (h : ¬(Even (Finset.univ.filter fun i => v i = a).card ↔
      Even (Finset.univ.filter fun i => u i = a).card)) : M v u = 0 := by
  have key := apply_comp_mul_prod_of_commute_kroneckerPower hM (Equiv.refl ι)
    (d := fun i => if i = a then -1 else 1) (fun i => by split_ifs <;> simp) v u
  simp only [Equiv.coe_refl, Function.id_comp, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const] at key
  have hneg : M v u = -M v u → M v u = 0 := fun hz => by
    have : (2 : R) * M v u = 0 := by linear_combination hz
    exact (mul_eq_zero.mp this).resolve_left h2
  rcases Nat.even_or_odd (Finset.univ.filter fun i => v i = a).card with hv | hv <;>
    rcases Nat.even_or_odd (Finset.univ.filter fun i => u i = a).card with hu | hu
  · exact (h (iff_of_true hv hu)).elim
  · rw [hv.neg_one_pow, hu.neg_one_pow] at key
    exact hneg (by linear_combination -key)
  · rw [hv.neg_one_pow, hu.neg_one_pow] at key
    exact hneg (by linear_combination key)
  · exact (h (iff_of_false (Nat.not_even_iff_odd.mpr hv) (Nat.not_even_iff_odd.mpr hu))).elim

end Matrix
