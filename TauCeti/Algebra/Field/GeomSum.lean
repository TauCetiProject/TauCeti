/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Summation by parts against a geometric sequence

In a division ring `𝕜` with a geometric ratio `z ≠ 1`, each power `z ^ j` is the forward difference
`z ^ (j + 1) / (z - 1) - z ^ j / (z - 1)`. Pairing this telescoping identity with a sequence of
scalars `f : ℕ → R` acting on `𝕜` rewrites `∑_{j=m}^{n-1} f(j) • z^j` into boundary terms at `n`
and `m` plus the sum weighted by the forward differences `f(j) - f(j + 1)`, providing the algebraic
step behind summation-by-parts bounds and asymptotic expansions for oscillatory and alternating
partial sums.

The file also telescopes the centred geometric sum `∑_{j=-n}^{n} z^j` over a symmetric integer
interval, the form in which a root string `∑_{j=-n}^{n} e^{j α}` is evaluated at a character.

## Main results

* `TauCeti.one_sub_mul_sum_Icc_zpow`: `(1 - z) ∑_{j=-n}^{n} z^j = z^{-n} - z^{n+1}` for `z ≠ 0`.
* `TauCeti.sum_Ico_smul_pow_eq`: for `z ≠ 1` and `m ≤ n`,
  `∑ j ∈ Ico m n, f j • z ^ j = f n • (z ^ n / (z - 1)) - f m • (z ^ m / (z - 1))
    + ∑ j ∈ Ico m n, (f j - f (j + 1)) • (z ^ (j + 1) / (z - 1))`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formula 2.10.14.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Finset

namespace TauCeti

/-- **Exact summation by parts against a geometric sequence.** For a module action of a ring `R`
on a division ring `𝕜`, `z ≠ 1`, and `m ≤ n`,
`∑_{j=m}^{n-1} f(j) • z^j = f(n) • (z^n / (z - 1)) - f(m) • (z^m / (z - 1))
  + ∑_{j=m}^{n-1} (f(j) - f(j + 1)) • (z^{j+1} / (z - 1))`. -/
theorem sum_Ico_smul_pow_eq {R 𝕜 : Type*} [Ring R] [DivisionRing 𝕜] [Module R 𝕜]
    (f : ℕ → R) {z : 𝕜} (hz : z ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ j ∈ Ico m n, f j • z ^ j =
      f n • (z ^ n / (z - 1)) - f m • (z ^ m / (z - 1)) +
        ∑ j ∈ Ico m n, (f j - f (j + 1)) • (z ^ (j + 1) / (z - 1)) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    have hz₁ : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    have hstep : z ^ k = z ^ (k + 1) / (z - 1) - z ^ k / (z - 1) := by
      rw [← sub_div, pow_succ, ← mul_sub_one, mul_div_cancel_right₀ _ hz₁]
    have hterm : f k • z ^ k =
        f (k + 1) • (z ^ (k + 1) / (z - 1)) - f k • (z ^ k / (z - 1)) +
          (f k - f (k + 1)) • (z ^ (k + 1) / (z - 1)) := by
      conv_lhs => rw [hstep]
      rw [smul_sub, sub_smul]
      abel
    rw [sum_Ico_succ_top hmk, sum_Ico_succ_top hmk, ih, hterm]
    abel

/-- **The centred geometric sum telescopes**: for `z ≠ 0` in a division ring,
`(1 - z) ∑_{j=-n}^{n} z^j = z^{-n} - z^{n+1}`. -/
theorem one_sub_mul_sum_Icc_zpow {𝕜 : Type*} [DivisionRing 𝕜] {z : 𝕜} (hz : z ≠ 0) (n : ℕ) :
    (1 - z) * ∑ j ∈ Icc (-(n : ℤ)) n, z ^ j = z ^ (-(n : ℤ)) - z ^ (n + 1) := by
  -- Reindex `j = -n + k` with `k = 0, …, 2 n`.
  have hsum : ∑ j ∈ Icc (-(n : ℤ)) n, z ^ j = z ^ (-(n : ℤ)) * ∑ k ∈ range (2 * n + 1), z ^ k := by
    rw [sum_Icc_neg_natCast_eq_sum_range, Finset.mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sub_eq_neg_add, zpow_add₀ hz, zpow_natCast]
  -- `1 - z` commutes with the powers of `z`.
  have hc : Commute (1 - z) (z ^ (-(n : ℤ))) :=
    (Commute.one_left _).sub_left ((Commute.refl z).zpow_right₀ _)
  calc (1 - z) * ∑ j ∈ Icc (-(n : ℤ)) n, z ^ j
      = z ^ (-(n : ℤ)) * ((1 - z) * ∑ k ∈ range (2 * n + 1), z ^ k) := by
        rw [hsum, ← mul_assoc, hc.eq, mul_assoc]
    _ = z ^ (-(n : ℤ)) - z ^ (-(n : ℤ) + (2 * n + 1 : ℕ)) := by
        rw [mul_neg_geom_sum, mul_sub, mul_one, zpow_add₀ hz, zpow_natCast]
    _ = z ^ (-(n : ℤ)) - z ^ (n + 1) := by
        rw [← zpow_natCast]
        congr 2
        push_cast
        ring

end TauCeti
