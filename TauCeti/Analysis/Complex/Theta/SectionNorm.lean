/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Theta.Metric
public import TauCeti.Analysis.Complex.Theta.Sections
import TauCeti.Analysis.Complex.Theta.Vanishing

/-!
# Unconditional lattice descent of the Hermitian norm on theta sections

For a holomorphic theta section `s ∈ thetaSections k τ α β`, the pointwise Hermitian norm squared
`thetaMetric k τ z * ‖s z‖²` is invariant under the lattice `ℤ + τℤ` unconditionally in `τ`:
when `τ.im ≠ 0`, this is `TauCeti.thetaMetric_add_mul_norm_sq`; when `τ.im = 0`, either `k = 0`
(where `thetaMetric` and the multiplier have modulus `1`) or `k > 0` (where `s = 0` by
`TauCeti.thetaSections_eq_bot_of_im_nonpos`).

## Main results

* `TauCeti.thetaMetric_mul_norm_sq_add_int_add_int_mul_tau`: unconditional lattice invariance of
  the pointwise Hermitian norm squared on `thetaSections`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

namespace TauCeti

/-- For every theta section `s`, the pointwise Hermitian norm squared `thetaMetric k τ z * ‖s z‖²`
is doubly periodic on the lattice `ℤ + τℤ`, unconditionally in `τ`. -/
theorem thetaMetric_mul_norm_sq_add_int_add_int_mul_tau {k : ℕ} {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  by_cases hτ : τ.im = 0
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [add_int_add_int_mul_tau_of_mem_thetaSections hs m n z, norm_mul, mul_pow,
        norm_thetaFactor]
      simp [thetaMetric_def]
    · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ.le α β, Submodule.mem_bot] at hs
      simp [hs]
  · exact thetaMetric_add_mul_norm_sq hτ
      (add_int_add_int_mul_tau_of_mem_thetaSections hs m n z)

end TauCeti
