/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Roots, splitting and divisibility of `X ^ n - C a`

For `n ≠ 0`, membership in the root set of `X ^ n - C a` is the equation `x ^ n = a` in any
domain algebra. For `n = 2`, a single square root `δ` of `a` splits the binomial over any
commutative ring: its linear factors have roots `δ` and `-δ`. No primitive root of unity
is needed, so the splitting statement also applies in characteristic `2`. Over an ordered
field, `X ^ 2 + 1 = X ^ 2 - C (-1)` is irreducible since `-1` is not a square. Over any nontrivial
ring, the monic `X ^ n - C a` of degree `n` does not divide the geometric sum
`1 + X + ⋯ + X ^ (n - 1)`, which is monic of degree `n - 1`.

## Main results

* `Polynomial.mem_rootSet_X_pow_sub_C`: root-set membership is an `n`-th power equation.
* `Polynomial.splits_map_X_pow_two_sub_C`: a square root splits the quadratic binomial.
* `Polynomial.irreducible_X_sq_add_one`: `X ^ 2 + 1` is irreducible over an ordered field.
* `Polynomial.not_X_pow_sub_C_dvd_geom_sum`: `X ^ n - C a` does not divide
  `1 + X + ⋯ + X ^ (n - 1)`.
-/

public section

namespace Polynomial

universe u v

section RootSet

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [IsDomain E]
  [Algebra F E] {a : F}

/-- An element of a domain algebra is a root of `X ^ n - C a` exactly when its `n`-th power
is `a`. -/
@[simp]
theorem mem_rootSet_X_pow_sub_C {n : ℕ} (hn : n ≠ 0) {x : E} :
    x ∈ ((X : F[X]) ^ n - C a).rootSet E ↔ x ^ n = algebraMap F E a := by
  rw [(monic_X_pow_sub_C a hn).mem_rootSet, map_sub, aeval_X_pow, aeval_C,
    sub_eq_zero]

end RootSet

section Splits

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E] {a : F} {δ : E}

/-- A square root of `a` in `E` splits `X ^ 2 - C a` there: the two linear factors are `X - C δ`
and `X + C δ`. Unlike `Polynomial.X_pow_sub_C_splits_of_isPrimitiveRoot` this needs no primitive
root of unity, so it also covers characteristic `2`, where the two factors coincide. -/
theorem splits_map_X_pow_two_sub_C (hδ : δ ^ 2 = algebraMap F E a) :
    (((X : F[X]) ^ 2 - C a).map (algebraMap F E)).Splits := by
  have hmap : ((X : F[X]) ^ 2 - C a).map (algebraMap F E) = (X - C δ) * (X - C (-δ)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hδ, map_pow, map_neg]
    ring
  rw [hmap]
  exact (Splits.X_sub_C δ).mul (Splits.X_sub_C (-δ))

end Splits

/-- **`X ^ 2 + 1` is irreducible over an ordered field**: a square is never `-1`. -/
theorem irreducible_X_sq_add_one (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : Irreducible (X ^ 2 + 1 : K[X]) := by
  have h := X_pow_sub_C_irreducible_of_prime Nat.prime_two (a := (-1 : K))
    fun b hb ↦ by nlinarith [sq_nonneg b]
  simpa [sub_eq_add_neg] using h

section GeomSum

variable {R : Type u} [Ring R] [Nontrivial R]

/-- For `n ≠ 0`, `X ^ n - C a` does not divide `1 + X + ⋯ + X ^ (n - 1)`, which is nonzero of
degree less than `n`. -/
theorem not_X_pow_sub_C_dvd_geom_sum (a : R) {n : ℕ} (hn : n ≠ 0) :
    ¬ (X ^ n - C a : R[X]) ∣ ∑ k ∈ Finset.range n, X ^ k := fun hdvd ↦ by
  have hdeg := (monic_X_pow_sub_C a hn).natDegree_le_of_dvd (monic_geom_sum_X hn).ne_zero hdvd
  have hle : (∑ k ∈ Finset.range n, X ^ k : R[X]).natDegree ≤ n - 1 :=
    natDegree_sum_le_of_forall_le _ _ fun k hk ↦ by
      rw [natDegree_X_pow]
      have := Finset.mem_range.mp hk
      lia
  rw [natDegree_X_pow_sub_C] at hdeg
  lia

end GeomSum

end Polynomial
