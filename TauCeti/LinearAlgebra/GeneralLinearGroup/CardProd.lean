/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Factored Product Formula for the Cardinality of `GL n k`

For a finite field `k` with `q = Nat.card k` elements and a finite index type `n`, this file
proves the factored product formula
`Nat.card (GL n k) = ∏ i ∈ Finset.range (Fintype.card n), (q ^ i * (q ^ (i + 1) - 1))`
both in `ℕ` and cast into an arbitrary commutative ring `R`, derived from the general ring identity
`∏ i : Fin d, (q ^ d - q ^ (i : ℕ)) = (∏ i ∈ range d, q ^ i) * ∏ i ∈ range d, (q ^ (i + 1) - 1)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/LocalGL/Green/CuspidalFunctions.lean`
(`New.card_GL_eq_prod`).
-/

@[expose] public section

namespace TauCeti

open Finset

/-- Algebraic regrouping of the `GL_d` order product in any commutative ring:
`∏ i : Fin d, (q ^ d - q ^ i) = (∏ i ∈ range d, q ^ i) * ∏ i ∈ range d, (q ^ (i + 1) - 1)`. -/
theorem prod_pow_sub_pow_eq_mul_prod {R : Type*} [CommRing R] (q : R) (d : ℕ) :
    ∏ i : Fin d, (q ^ d - q ^ (i : ℕ)) =
      (∏ i ∈ range d, q ^ i) * ∏ i ∈ range d, (q ^ (i + 1) - 1) := by
  induction d with
  | zero => simp
  | succ m ih =>
    simp only [Fin.prod_univ_succ, Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, ← sub_mul,
      prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ih, prod_range_succ]
    ring

/-- The order of `GL n k` for a finite field `k`, cast into any commutative ring `R`, equals
`∏ i ∈ range (Fintype.card n), (q ^ i * (q ^ (i + 1) - 1))` where `q = Nat.card k`. -/
theorem card_GL_eq_prod_cast {k n R : Type*} [Field k] [Finite k] [Fintype n] [DecidableEq n]
    [CommRing R] :
    (Nat.card (GL n k) : R) =
      ∏ i ∈ range (Fintype.card n),
        ((Nat.card k : R) ^ i * ((Nat.card k : R) ^ (i + 1) - 1)) := by
  have : Fintype k := Fintype.ofFinite k
  have h_card : Nat.card (GL n k) = Nat.card (GL (Fin (Fintype.card n)) k) :=
    Nat.card_congr
      (Units.mapEquiv (Matrix.reindexRingEquiv k (Fintype.equivFin n)).toMulEquiv).toEquiv
  rw [h_card, Matrix.card_GL_field, Nat.card_eq_fintype_card,
    prod_mul_distrib, ← prod_pow_sub_pow_eq_mul_prod (Fintype.card k : R) (Fintype.card n)]
  push_cast
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right Fintype.card_pos i.isLt.le)]
  push_cast
  rfl

/-- The order of `GL n k` for a finite field `k` in `ℕ`:
`Nat.card (GL n k) = ∏ i ∈ range (Fintype.card n), (q ^ i * (q ^ (i + 1) - 1))`. -/
theorem card_GL_eq_prod_nat {k n : Type*} [Field k] [Finite k] [Fintype n] [DecidableEq n] :
    Nat.card (GL n k) =
      ∏ i ∈ range (Fintype.card n), (Nat.card k ^ i * (Nat.card k ^ (i + 1) - 1)) := by
  have : Fintype k := Fintype.ofFinite k
  have h_pos : 1 ≤ Nat.card k := Nat.card_eq_fintype_card (α := k) ▸ Fintype.card_pos
  have h_int := card_GL_eq_prod_cast (k := k) (n := n) (R := ℤ)
  refine Nat.cast_injective (R := ℤ) (h_int.trans ?_)
  symm
  push_cast
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (one_le_pow₀ h_pos)]
  push_cast
  rfl

end TauCeti
