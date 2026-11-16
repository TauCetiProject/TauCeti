/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.GroupTheory.Coxeter.Poincare
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Poincaré polynomial of the symmetric group

The length generating function of permutations on `n` letters is the product of the
geometric sums `1 + x + ⋯ + x^(d-1)` for `1 ≤ d ≤ n`. The formula holds over any
commutative semiring, including at parameters where a factor vanishes. In particular,
at `x = q²` it gives the quantum factorial used to normalize Hecke symmetrizers.

The combinatorial step uses the inversion and Coxeter-length insertion formulas for
Mathlib's `Equiv.Perm.decomposeFin'`: inserting the value `i` at the first position creates
exactly `i` new inversions and preserves the inversions between all remaining positions.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.3 and 1.5.
-/

public section

open Finset

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
