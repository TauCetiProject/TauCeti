/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Floor.Semifield
public import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.Algebra.Polynomial.Taylor

import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.Data.ZMod.Basic

/-!
# Nonvanishing of univariate Hasse jets on finite sets and integer intervals

Over an integral domain, the root multiplicity of a nonzero polynomial `P` at `a` is the order of
its first nonvanishing Hasse derivative at `a`
(`Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero`), and the sum of its root
multiplicities over any finite set `S` is at most `P.natDegree`
(`Polynomial.sum_rootMultiplicity_le_natDegree`). Therefore, whenever `P.natDegree < #S * (k + 1)`,
some Hasse derivative of `P` of order at most `k` does not vanish at some point of `S`.

In characteristic zero, applying this bound to the image in `R` of the integer interval
`[-⌊B⌋₊, ⌊B⌋₊]` (of cardinality `2 * ⌊B⌋₊ + 1`) with `k = ⌊s / B⌋₊` yields the one-variable case
of Evertse's integer-grid nonvanishing lemma: for every `B > 0` and every nonzero `P` with
`P.natDegree ≤ s`, there exist `z : ℤ` with `|z| ≤ B` and `i : ℕ` with `i ≤ s / B` such that
`(hasseDeriv i P).eval (z : R) ≠ 0`.

## Main results

* `Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt`: over an integral domain, if `P ≠ 0`
  and `P.natDegree < #S * (k + 1)`, some Hasse derivative of `P` of order `≤ k` is nonzero on `S`.
* `Polynomial.exists_int_eval_hasseDeriv_ne_zero`: over a domain of characteristic zero, if `P ≠ 0`,
  `P.natDegree ≤ s`, and `0 < B`, some Hasse derivative of `P` of order `≤ s / B` is nonzero at an
  integer `z` with `z.natAbs ≤ B`.

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 25.
-/

public section

open Finset

namespace Polynomial

/-- Over an integral domain, if `P ≠ 0` has degree strictly less than `#S * (k + 1)`, then some
Hasse derivative of `P` of order at most `k` does not vanish at some point of `S`. -/
theorem exists_eval_hasseDeriv_ne_zero_of_natDegree_lt {R : Type*} [CommRing R] [IsDomain R]
    {P : R[X]} (hP : P ≠ 0) {S : Finset R} {k : ℕ} (hdeg : P.natDegree < #S * (k + 1)) :
    ∃ a ∈ S, ∃ i ≤ k, (hasseDeriv i P).eval a ≠ 0 := by
  by_contra! h
  have hle : #S * (k + 1) ≤ ∑ a ∈ S, P.rootMultiplicity a := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun a ha ↦
      (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hP).2 fun i hi ↦
        h a ha i (Nat.lt_succ_iff.1 hi)
  exact (hle.trans (sum_rootMultiplicity_le_natDegree P S)).not_gt hdeg

/-- **Univariate Hasse-jet nonvanishing on a bounded integer interval** (the one-variable case of
Evertse, Lemma 25). Over a domain of characteristic zero, any nonzero polynomial `P` of degree at
most `s` has a nonzero Hasse derivative of order at most `s / B` at some integer `z` with
`z.natAbs ≤ B`, for every `B > 0` (including `s = 0` and `B < 1`). -/
theorem exists_int_eval_hasseDeriv_ne_zero {R K : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
    {P : R[X]} (hP : P ≠ 0) {s : ℕ} (hs : P.natDegree ≤ s) {B : K} (hB : 0 < B) :
    ∃ (z : ℤ) (i : ℕ), (z.natAbs : K) ≤ B ∧ (i : K) ≤ (s : K) / B ∧
      (hasseDeriv i P).eval (z : R) ≠ 0 := by
  classical
  set a := ⌊B⌋₊
  set b := ⌊(s : K) / B⌋₊
  set I : Finset ℤ := Finset.Icc (-(a : ℤ)) (a : ℤ)
  have hcardI : #I = 2 * a + 1 := by
    rw [Int.card_Icc]
    omega
  set S : Finset R := I.image Int.cast
  have hcardS : #S = 2 * a + 1 := by
    rw [Finset.card_image_of_injective _ Int.cast_injective, hcardI]
  have hdeg : P.natDegree < #S * (b + 1) := by
    rw [hcardS]
    exact hs.trans_lt (TauCeti.lt_two_mul_floor_add_one_mul_floor_div_add_one hB s)
  obtain ⟨x, hx, i, hi, hne⟩ := exists_eval_hasseDeriv_ne_zero_of_natDegree_lt hP hdeg
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_Icc] at hz
  have hza : z.natAbs ≤ a := by omega
  exact ⟨z, i, (Nat.cast_le.2 hza).trans (Nat.floor_le hB.le),
    (Nat.cast_le.2 hi).trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg s) hB.le)), hne⟩

/-- Point values alone do not suffice: `X * (X - 1) * (X + 1)` over `ℚ` vanishes on the entire
`B = 1` integer grid `{-1, 0, 1}`, whereas its first Hasse derivative at `0` is `-1`. -/
example : (∀ z ∈ ({-1, 0, 1} : Finset ℤ),
    (X * (X - 1) * (X + 1) : ℚ[X]).eval (z : ℚ) = 0) ∧
    (hasseDeriv 1 (X * (X - 1) * (X + 1) : ℚ[X])).eval 0 = -1 := by
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · fin_cases hz <;> norm_num
  · have h : (X * (X - 1) * (X + 1) : ℚ[X]) = (X - C 0) ^ 3 - (X - C 0) ^ 1 := by simp; ring
    rw [h, map_sub, eval_sub, eval_hasseDeriv_X_sub_C_pow, eval_hasseDeriv_X_sub_C_pow]
    norm_num

/-- When `B < 1`, the integer grid collapses to `{0}` and higher-order Hasse jets are required:
for `X ^ 3` with `B = 1 / 2`, all jets of order `< 3` vanish at `0`, while order `3 ≤ 3 / (1 / 2)`
evaluates to `1`. -/
example : (∀ i < 3, (hasseDeriv i (X ^ 3 : ℚ[X])).eval 0 = 0) ∧
    (hasseDeriv 3 (X ^ 3 : ℚ[X])).eval 0 = 1 ∧
    (3 : ℚ) ≤ (3 : ℚ) / (1 / 2) := by
  refine ⟨fun i hi ↦ ?_, ?_, by norm_num⟩
  · simpa [hi.ne] using eval_hasseDeriv_X_sub_C_pow (0 : ℚ) i 3
  · simpa using eval_hasseDeriv_X_sub_C_pow (0 : ℚ) 3 3

/-- Characteristic zero cannot be omitted in `exists_int_eval_hasseDeriv_ne_zero`: over `ZMod 2`,
`X ^ 2 - X` is nonzero of degree `2`, yet for `B = 3` every derivative order `i ≤ 2 / 3` has
`i = 0` and `(X ^ 2 - X).eval (z : ZMod 2) = 0` for every `z : ℤ`. -/
example : (X ^ 2 - X : (ZMod 2)[X]) ≠ 0 ∧
    (X ^ 2 - X : (ZMod 2)[X]).natDegree ≤ 2 ∧
    ∀ (z : ℤ) (i : ℕ), (i : ℚ) ≤ (2 : ℚ) / 3 →
      (hasseDeriv i (X ^ 2 - X : (ZMod 2)[X])).eval (z : ZMod 2) = 0 := by
  refine ⟨?_, (natDegree_sub_le _ _).trans
    (max_le (natDegree_X_pow_le 2) (natDegree_X_le.trans (by omega))), fun z i hi ↦ ?_⟩
  · intro h
    have h1 := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 1) h
    norm_num [coeff_X_pow, coeff_X] at h1
  · have hi0 : i = 0 := by
      have h1 : (i : ℚ) < 1 := hi.trans_lt (by norm_num)
      have h2 : i < 1 := by exact_mod_cast h1
      omega
    subst hi0
    simp only [hasseDeriv_zero, LinearMap.id_apply, eval_sub, eval_pow, eval_X]
    generalize (z : ZMod 2) = x
    fin_cases x <;> decide

end Polynomial
