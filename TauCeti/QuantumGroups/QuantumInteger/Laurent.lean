/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Symmetric
public import TauCeti.QuantumGroups.QuantumInteger.Basic

import Mathlib.Tactic

/-!
# Quantum integers as Laurent polynomials

The symmetric quantum integer `[r]_q = (q^r - q^(-r)) / (q - q⁻¹)` of
`TauCeti/QuantumGroups/QuantumInteger/Basic.lean` is the value at `v = q` of a Laurent polynomial
with integer coefficients,

`[n]_v = v^(n-1) + v^(n-3) + ⋯ + v^(1-n)` for `n ≥ 0`, and `[-n]_v = -[n]_v`.

This file defines that Laurent polynomial `TauCeti.laurentQuantumInteger r` in `ℤ[v, v⁻¹]` as
`S_(r-1)(v + v⁻¹)`, where `S` is Mathlib's rescaled Chebyshev polynomial of the second kind
`Polynomial.Chebyshev.S`. It is characterized, without a denominator, by
`(v - v⁻¹) [r]_v = v^r - v^(-r)`. Evaluating it at a unit `q` of a field with `q - q⁻¹ ≠ 0` gives
the field quantum integer `[r]_q`, while evaluating it at `v = 1`, where the quotient formula
degenerates, gives the ordinary integer `r`. Writing matrix coefficients with these Laurent
polynomials therefore describes a family of representations at a generic parameter and its
classical specialization at `v = 1` at the same time.

## Main definitions

* `TauCeti.laurentQuantumInteger r`: the quantum integer `[r]_v` in `ℤ[v, v⁻¹]`.

## Main results

* `TauCeti.laurentQuantumInteger_neg`: `[-r]_v = -[r]_v`.
* `TauCeti.T_sub_T_neg_mul_laurentQuantumInteger`: `(v - v⁻¹) [r]_v = v^r - v^(-r)`.
* `TauCeti.laurentEval_laurentQuantumInteger`: the value at a unit `q` of a field with
  `q - q⁻¹ ≠ 0` is the quantum integer `[r]_q`.
* `TauCeti.laurentEval_one_laurentQuantumInteger`: the value at `v = 1` is `r`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, Chapter 0, for
  the symmetric quantum integers as Laurent polynomials.
-/

public section

open LaurentPolynomial Polynomial.Chebyshev

namespace TauCeti

/-- The symmetric quantum integer `[r]_v` as a Laurent polynomial with integer coefficients,
`[r]_v = S_(r-1)(v + v⁻¹)` for the rescaled Chebyshev polynomial `S` of the second kind. Thus
`[n]_v = v^(n-1) + v^(n-3) + ⋯ + v^(1-n)` for `n ≥ 0`, and `[-n]_v = -[n]_v`. -/
noncomputable def laurentQuantumInteger (r : ℤ) : ℤ[T;T⁻¹] :=
  Polynomial.eval₂ C (T 1 + T (-1)) (S ℤ (r - 1))

/-- `[0]_v = 0`. -/
@[simp]
theorem laurentQuantumInteger_zero : laurentQuantumInteger 0 = 0 := by
  simp [laurentQuantumInteger]

/-- `[1]_v = 1`. -/
@[simp]
theorem laurentQuantumInteger_one : laurentQuantumInteger 1 = 1 := by
  simp [laurentQuantumInteger]

/-- Negating the index negates the quantum integer: `[-r]_v = -[r]_v`. -/
@[simp]
theorem laurentQuantumInteger_neg (r : ℤ) :
    laurentQuantumInteger (-r) = -laurentQuantumInteger r := by
  rw [laurentQuantumInteger, laurentQuantumInteger, S_neg_sub_one, Polynomial.eval₂_neg]

/-- The quantum integer `[r]_v` is characterized by `(v - v⁻¹) [r]_v = v^r - v^(-r)`. -/
theorem T_sub_T_neg_mul_laurentQuantumInteger (r : ℤ) :
    (T 1 - T (-1)) * laurentQuantumInteger r = T r - T (-r) := by
  -- For a positive index this is the Chebyshev identity; negating the index negates both sides.
  have key : ∀ n : ℕ, (T 1 - T (-1)) * laurentQuantumInteger n = T n - T (-n) := by
    rintro (_ | n)
    · simp
    · simp [laurentQuantumInteger]
  rcases Int.eq_nat_or_neg r with ⟨n, rfl | rfl⟩
  · exact key n
  · rw [laurentQuantumInteger_neg, mul_neg, key, neg_neg, neg_sub]

/-- At `v = 1` the quantum integer `[r]_v` is the integer `r`. -/
@[simp]
theorem laurentEval_one_laurentQuantumInteger {A : Type*} [Ring A] (r : ℤ) :
    laurentEval (1 : Aˣ) (laurentQuantumInteger r) = r := by
  -- Evaluation at `v = 1` sends `v + v⁻¹` to `2`, and `S_n(2) = n + 1`.
  rw [← AlgHom.coe_toRingHom, laurentQuantumInteger, Polynomial.hom_eval₂]
  simp [one_add_one_eq_two, S_eval_two]

/-- The value of `[r]_v` at a unit `q` of a ring satisfies
`(q - q⁻¹) [r]_q = q^r - q^(-r)`. -/
theorem sub_inv_mul_laurentEval_laurentQuantumInteger {S : Type*} [Ring S] (u : Sˣ) (r : ℤ) :
    ((u : S) - (u⁻¹ : Sˣ)) * laurentEval u (laurentQuantumInteger r) =
      ((u ^ r : Sˣ) : S) - ((u ^ (-r) : Sˣ) : S) := by
  have h := congrArg (laurentEval (R := ℤ) u) (T_sub_T_neg_mul_laurentQuantumInteger r)
  simpa only [map_mul, map_sub, laurentEval_T, zpow_one, zpow_neg_one] using h

/-- At a unit `q` of a field with `q - q⁻¹ ≠ 0`, the Laurent quantum integer `[r]_v` takes the
value `[r]_q`. -/
theorem laurentEval_laurentQuantumInteger {K : Type*} [Field K] {u : Kˣ}
    (hu : (u : K) - (u : K)⁻¹ ≠ 0) (r : ℤ) :
    laurentEval u (laurentQuantumInteger r) = quantumInteger (u : K) r := by
  have h := sub_inv_mul_laurentEval_laurentQuantumInteger u r
  rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val] at h
  rw [quantumInteger_def, eq_div_iff hu, mul_comm, h]

end TauCeti
