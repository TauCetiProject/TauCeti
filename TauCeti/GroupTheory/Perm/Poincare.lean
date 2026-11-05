/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.GroupTheory.Coxeter.Poincare
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Poincaré polynomial of the symmetric group

The length generating function of permutations on `n` letters is the product of the
geometric sums `1 + x + ⋯ + x^(d-1)` for `1 ≤ d ≤ n`. The formula holds over any
commutative semiring, including at parameters where a factor vanishes. In particular,
at `x = q²` it gives the quantum factorial used to normalize Hecke symmetrizers.

The combinatorial step uses Mathlib's `Equiv.Perm.decomposeFin'`: inserting the value `i`
at the first position creates exactly `i` new inversions and preserves the inversions
between all remaining positions.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.3 and 1.5.
-/

public section

open Finset

namespace Equiv.Perm

/-- Inserting `i` at the first position creates exactly `i` additional inversions. -/
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
  have hzero : (∑ y : Fin (n + 2), if (0 : Fin (n + 2)) < y ∧
      decomposeFin'Symm i σ y < decomposeFin'Symm i σ 0 then 1 else 0) = i.val := by
    rw [Fin.sum_univ_succ]
    simpa using hfirst
  have hsucc (x : Fin (n + 1)) :
      (∑ y : Fin (n + 2), if x.succ < y ∧
        decomposeFin'Symm i σ y < decomposeFin'Symm i σ x.succ then 1 else 0) =
      ∑ y : Fin (n + 1), if x < y ∧ σ y < σ x then 1 else 0 := by
    rw [Fin.sum_univ_succ]
    simp
  simp only [card_filter, Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ, hzero]
  simp_rw [hsucc]

open TauCeti

/-- The length of the permutation obtained by inserting `i` at the first position is
`i` plus the length of the original permutation. -/
theorem permCoxeterSystem_length_decomposeFin'Symm {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2)) :
    (permCoxeterSystem (n + 2)).length (Equiv.Perm.decomposeFin'Symm i σ) =
      i.val + (permCoxeterSystem (n + 1)).length σ := by
  simp only [permCoxeterSystem_length_eq_card_inversion,
    Equiv.Perm.card_inversion_decomposeFin'Symm]

end Equiv.Perm

namespace TauCeti

/-- The length generating function of `Sₙ` is the quantum factorial
`∏ d ∈ Icc 1 n, (1 + x + ⋯ + x^(d-1))`. -/
theorem sum_pow_permCoxeterSystem_length {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    (∑ σ : Equiv.Perm (Fin n), x ^ (permCoxeterSystem n).length σ) =
      ∏ d ∈ Icc 1 n, ∑ j ∈ range d, x ^ j := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hσ : ∀ σ : Equiv.Perm (Fin 1), σ = 1 := fun σ => Subsingleton.elim _ _
    simp [hσ]
  | more n _ ih =>
    rw [← (Equiv.Perm.decomposeFin' (n := n)).symm.sum_comp
      (fun σ => x ^ (permCoxeterSystem (n + 2)).length σ), Fintype.sum_prod_type]
    simp only [Equiv.Perm.decomposeFin'_symm, Equiv.Perm.permCoxeterSystem_length_decomposeFin'Symm,
      pow_add, ← mul_sum, ← sum_mul, ih, Fin.sum_univ_eq_sum_range]
    conv_rhs => rw [prod_Icc_succ_top (by omega)]
    exact mul_comm _ _

/-- The Poincaré polynomial of `Sₙ` is the product of its geometric-sum factors. -/
theorem poincarePolynomial_permCoxeterSystem (n : ℕ) :
    poincarePolynomial (permCoxeterSystem n) =
      ∏ d ∈ Icc 1 n, ∑ j ∈ range d, (Polynomial.X : Polynomial ℤ) ^ j := by
  rw [poincarePolynomial_eq_sum, sum_pow_permCoxeterSystem_length]

end TauCeti
