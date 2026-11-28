/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Ideal.Maps

/-!
# Congruence exponent lifting in `GL n R`

Let `R` be a commutative ring, `I : Ideal R`, and `q : ℕ` with `(q : R) ∈ I`. If `g : GL n R`
satisfies `g ≡ 1 (mod I)` entrywise, then raising `g` to the `q ^ k`-th power lifts the
congruence to `g ^ (q ^ k) ≡ 1 (mod I ^ (k + 1))`.

## Main results

* `TauCeti.pow_sub_one_mem_ideal_mul`: if `(q : R) ∈ I` and `g ≡ 1 (mod I)` and `g ≡ 1 (mod J)`
  entrywise for ideals `I, J : Ideal R`, then `g ^ q ≡ 1 (mod J * I)`.
* `TauCeti.pow_pow_sub_one_mem_ideal_pow`: if `(q : R) ∈ I` and `g ≡ 1 (mod I)` entrywise, then
  `g ^ (q ^ k) ≡ 1 (mod I ^ (k + 1))` for all `k : ℕ`.

## Provenance

Adapted from `New.pow_pow_mem_localCongruence` in `src/Lib/Weil/Unramified/HeckeGL.lean` of
`grh-lean` (https://github.com/lsernau/grh-lean, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC),
generalized from the maximal ideal of a local ring of integers `LocInt w` to an arbitrary
ideal `I` of any commutative ring `R`.
-/

public section

open Matrix Finset

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- If `(q : R) ∈ I`, and a matrix `M : Matrix n n R` satisfies `M ≡ 1 (mod I)` and
`M ≡ 1 (mod J)` entrywise, then `M ^ q ≡ 1 (mod J * I)`. -/
theorem pow_sub_one_mem_ideal_mul {I J : Ideal R} {q : ℕ} (hq : (q : R) ∈ I)
    {M : Matrix n n R} (hI : ∀ a b : n, (M - 1) a b ∈ I) (hJ : ∀ a b : n, (M - 1) a b ∈ J)
    (a b : n) : (M ^ q - 1) a b ∈ J * I := by
  have hpow (l : ℕ) : ∀ i j : n, (M ^ l - 1) i j ∈ I := by
    induction l with
    | zero => simp
    | succ l ih =>
      intro i j
      have hdecomp : M ^ (l + 1) - 1 = (M ^ l - 1) * M + (M - 1) := by
        simp [pow_succ, sub_mul]
      rw [hdecomp, Matrix.add_apply, Matrix.mul_apply]
      refine I.add_mem (I.sum_mem fun k _ ↦ ?_) (hI i j)
      exact I.mul_mem_right (M k j) (ih i k)
  have hfactor : M ^ q - 1 = (M - 1) * ∑ l ∈ range q, M ^ l := by
    rw [mul_geom_sum]
  rw [hfactor, Matrix.mul_apply]
  refine (J * I).sum_mem fun k _ ↦ ?_
  refine Ideal.mul_mem_mul (hJ a k) ?_
  have hsum : (∑ l ∈ range q, M ^ l) k b =
      (∑ l ∈ range q, (M ^ l - 1) k b) + (if k = b then (q : R) else 0) := by
    simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_ite, mul_one, mul_zero,
      sub_add_cancel]
  rw [hsum]
  refine I.add_mem (I.sum_mem fun l _ ↦ hpow l k b) ?_
  split_ifs
  · exact hq
  · exact I.zero_mem

/-- Exponent lifting for congruence matrices: if `(q : R) ∈ I` and `M : Matrix n n R` satisfies
`M ≡ 1 (mod I)` entrywise, then `M ^ (q ^ k) ≡ 1 (mod I ^ (k + 1))` entrywise for every `k : ℕ`. -/
theorem pow_pow_sub_one_mem_ideal_pow {I : Ideal R} {q : ℕ} (hq : (q : R) ∈ I)
    {M : Matrix n n R} (hI : ∀ a b : n, (M - 1) a b ∈ I) (k : ℕ) (a b : n) :
    (M ^ (q ^ k) - 1) a b ∈ I ^ (k + 1) := by
  induction k generalizing a b with
  | zero => simpa using hI a b
  | succ k ih =>
    rw [pow_succ q k, pow_mul, pow_succ I]
    refine pow_sub_one_mem_ideal_mul hq ?_ ih a b
    intro i j
    exact Ideal.pow_le_self (Nat.succ_ne_zero k) (ih i j)

/-- Exponent lifting in `GL n R`: if `(q : R) ∈ I` and `g : GL n R` satisfies `g ≡ 1 (mod I)`
entrywise, then `g ^ (q ^ k) ≡ 1 (mod I ^ (k + 1))` entrywise for every `k : ℕ`. -/
theorem gl_pow_pow_sub_one_mem_ideal_pow {I : Ideal R} {q : ℕ} (hq : (q : R) ∈ I)
    {g : GL n R} (hI : ∀ a b : n, (g.val - 1) a b ∈ I) (k : ℕ) (a b : n) :
    ((g ^ (q ^ k)).val - 1) a b ∈ I ^ (k + 1) := by
  rw [Units.val_pow_eq_pow_val]
  exact pow_pow_sub_one_mem_ideal_pow hq hI k a b

end TauCeti
