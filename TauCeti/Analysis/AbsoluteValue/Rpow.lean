/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Powers of an absolute value that are bounded on the natural numbers

For a real absolute value `v` and `t > 0`, the function `x ↦ v x ^ t` is multiplicative, but it
need not satisfy the triangle inequality when `t > 1`: `|·| ^ 2` on `ℚ` does not. It does when it
is bounded by the real absolute value on the natural numbers, that is, when `v n ^ t ≤ n` for every
`n : ℕ` (`AbsoluteValue.rpow_add_le_of_forall_natCast`). The proof applies `v` to the binomial
expansion of `(x + y) ^ n`, which gives `v (x + y) ^ n ≤ (n + 1) * M ^ n` for every `n`, where
`M ^ t = v x ^ t + v y ^ t`, and takes `n`-th roots.

This is what lets an absolute value of a field of characteristic zero be raised to the power that
makes it restrict to the real or a `p`-adic absolute value on `ℚ`
(`AbsoluteValue.Place.exists_isEquiv_of_isNontrivial_under`).

## Main definitions

* `AbsoluteValue.rpowOfNatCast`: the absolute value `x ↦ v x ^ t` when `v n ^ t ≤ n` on `ℕ`.

## Main results

* `AbsoluteValue.rpow_add_le_of_forall_natCast`: the triangle inequality for `x ↦ v x ^ t`.

The argument is the one of `normalization_triangle` in Jz Pan's lean-iwasawa
(`acmepjz/lean-iwasawa` at `7666c16`, branch `autoformalize.v1`, file
`Iwasawalib/NumberTheory/AbsoluteValue/Normalization.lean`, Apache 2.0).

## References

* E. Artin, *Algebraic Numbers and Algebraic Functions*, Gordon and Breach, 1967, Chapter 1,
  Theorem 3.
* J. W. S. Cassels, *Local Fields*, Cambridge University Press, 1986, Chapter 2, Lemma 2.1.
-/

public section

namespace AbsoluteValue

variable {R : Type*} [CommSemiring R] (v : AbsoluteValue R ℝ) {t : ℝ} (ht : 0 < t)
  (h : ∀ n : ℕ, v n ^ t ≤ n)

include ht h in
/-- If `v n ^ t ≤ n` for every natural number `n`, then each term
`v x ^ k * v y ^ (n - k) * v (C(n, k))` of the binomial bound for `v ((x + y) ^ n)` is at most
`M ^ n`, where `M ^ t = v x ^ t + v y ^ t`. -/
private theorem apply_choose_mul_le (x y : R) (n k : ℕ) (hk : k ≤ n) :
    v x ^ k * v y ^ (n - k) * v (n.choose k) ≤ ((v x ^ t + v y ^ t) ^ t⁻¹) ^ n := by
  have hS : 0 ≤ v x ^ t + v y ^ t := by positivity
  have hl : (v x ^ k * v y ^ (n - k) * v (n.choose k)) ^ t ≤
      (v x ^ t) ^ k * (v y ^ t) ^ (n - k) * n.choose k := by
    rw [Real.mul_rpow (by positivity) (v.nonneg _), Real.mul_rpow (by positivity) (by positivity),
      Real.rpow_pow_comm (v.nonneg _), Real.rpow_pow_comm (v.nonneg _)]
    gcongr
    exact h _
  have hr : (((v x ^ t + v y ^ t) ^ t⁻¹) ^ n) ^ t = (v x ^ t + v y ^ t) ^ n := by
    rw [← Real.rpow_pow_comm (Real.rpow_nonneg hS _), Real.rpow_inv_rpow hS ht.ne']
  rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) ht, hr, add_pow]
  refine hl.trans <| (le_of_eq ?_).trans (Finset.single_le_sum (fun i _ ↦ by positivity)
    (Finset.mem_range_succ_iff.mpr hk))
  ring

include ht h in
/-- **The triangle inequality for a power of an absolute value.** If `v n ^ t ≤ n` for every
natural number `n`, then `v (x + y) ^ t ≤ v x ^ t + v y ^ t`. -/
theorem rpow_add_le_of_forall_natCast (x y : R) : v (x + y) ^ t ≤ v x ^ t + v y ^ t := by
  set M := (v x ^ t + v y ^ t) ^ t⁻¹
  have hS : 0 ≤ v x ^ t + v y ^ t := by positivity
  have hM : M ^ t = v x ^ t + v y ^ t := Real.rpow_inv_rpow hS ht.ne'
  rcases subsingleton_or_nontrivial R with _ | _
  · simp [Subsingleton.elim (x + y) 0, Real.zero_rpow ht.ne', hS]
  rcases (Real.rpow_nonneg hS t⁻¹).eq_or_lt with hM0 | hM0
  · -- `M = 0` forces `x = 0` and `y = 0`.
    have h0 := (Real.rpow_eq_zero hS (inv_ne_zero ht.ne')).mp hM0.symm
    obtain ⟨hx, hy⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp h0
    rw [Real.rpow_eq_zero (v.nonneg _) ht.ne', v.eq_zero] at hx hy
    simp [hx, hy, Real.zero_rpow ht.ne']
  -- `v (x + y) ^ n ≤ (n + 1) * M ^ n` for every `n`, so `v (x + y) ≤ M`.
  have hn (n : ℕ) : (v (x + y) / M) ^ n ≤ 1 * (1 + n) ^ (1 : ℝ) := by
    rw [div_pow, div_le_iff₀ (by positivity), Real.rpow_one, one_mul, add_comm (1 : ℝ),
      ← v.map_pow, add_pow]
    refine (v.sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range (n + 1), v (x ^ k * y ^ (n - k) * n.choose k)
        ≤ ∑ _k ∈ Finset.range (n + 1), M ^ n := Finset.sum_le_sum fun k hk ↦ by
          rw [map_mul, map_mul, map_pow, map_pow]
          exact apply_choose_mul_le v ht h x y n k (Finset.mem_range_succ_iff.mp hk)
      _ = (n + 1) * M ^ n := by simp
  have hle : v (x + y) ≤ M := (div_le_one hM0).mp (Real.le_one_of_forall_pow_le_mul_rpow hn)
  exact (Real.rpow_le_rpow (v.nonneg _) hle ht.le).trans_eq hM

/-- The power `x ↦ v x ^ t` of a real absolute value `v`, as an absolute value, when `t > 0` and
`v n ^ t ≤ n` for every natural number `n`. -/
noncomputable def rpowOfNatCast : AbsoluteValue R ℝ where
  toFun x := v x ^ t
  map_mul' x y := by simp [Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) t
  eq_zero' x := by simp [Real.rpow_eq_zero (v.nonneg x) ht.ne']
  add_le' := rpow_add_le_of_forall_natCast v ht h

@[simp]
theorem rpowOfNatCast_apply (x : R) : v.rpowOfNatCast ht h x = v x ^ t :=
  (rfl)

end AbsoluteValue
