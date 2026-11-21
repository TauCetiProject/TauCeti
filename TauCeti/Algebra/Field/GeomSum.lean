/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Abel

/-!
# Summation by parts against a geometric sequence

In a division ring `𝕜` with a geometric ratio `z ≠ 1`, each power `z ^ j` is the forward difference
`z ^ (j + 1) / (z - 1) - z ^ j / (z - 1)`. Pairing this telescoping identity with a sequence of
scalars `f : ℕ → R` acting on `𝕜` rewrites `∑_{j=m}^{n-1} f(j) • z^j` into boundary terms at `n`
and `m` plus the sum weighted by the forward differences `f(j) - f(j + 1)`, providing the algebraic
step behind summation-by-parts bounds and asymptotic expansions for oscillatory and alternating
partial sums.

## Main results

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

end TauCeti
