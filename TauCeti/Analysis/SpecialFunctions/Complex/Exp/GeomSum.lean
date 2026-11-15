/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite geometric sums of complex exponentials

For a complex frequency `w` with `exp w ≠ 1`, the exponential sequence `k ↦ exp (k * w)` is the
geometric progression `(exp w) ^ k`, so its partial sum over `1 ≤ k ≤ j` evaluates in closed form
to `exp w * (exp (j * w) - 1) / (exp w - 1)`. This closed form supplies the partial-sum kernel for
Dirichlet-type oscillatory sums and Abel summation of exponential sums.

## Main results

* `TauCeti.sum_Icc_cexp_natCast_mul`: for `exp w ≠ 1` and every `j : ℕ`,
  `∑ k ∈ Icc 1 j, exp (k * w) = exp w * (exp (j * w) - 1) / (exp w - 1)`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formula 2.10.13.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Finset

namespace TauCeti

/-- **Geometric partial sum of complex exponentials (DLMF 2.10.13).** For `w : ℂ` with
`e^w ≠ 1` and every `j : ℕ`, `∑_{k=1}^j e^{kw} = e^w (e^{jw} - 1) / (e^w - 1)`. -/
theorem sum_Icc_cexp_natCast_mul {w : ℂ} (hw : Complex.exp w ≠ 1) (j : ℕ) :
    ∑ k ∈ Icc 1 j, Complex.exp (k * w) =
      Complex.exp w * (Complex.exp (j * w) - 1) / (Complex.exp w - 1) := by
  rw [← Ico_add_one_right_eq_Icc]
  have hpow : ∀ k : ℕ, Complex.exp (k * w) = Complex.exp w ^ k := Complex.exp_nat_mul w
  simp_rw [hpow]
  rw [geom_sum_Ico hw (Nat.le_add_left 1 j), pow_add, pow_one]
  ring

end TauCeti
