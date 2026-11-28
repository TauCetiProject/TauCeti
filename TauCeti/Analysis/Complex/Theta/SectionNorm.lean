/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThetaLine.Basic
public import TauCeti.Analysis.Complex.Theta.Sections
import TauCeti.Analysis.Complex.Theta.Vanishing

/-!
# Unconditional translation invariance of the Hermitian norm on theta sections

For a holomorphic theta section `s ∈ thetaSections k τ α β`, the pointwise Hermitian norm squared
`thetaMetric k τ z * ‖s z‖²` is invariant under translations `z ↦ z + m + n * τ` (`m, n : ℤ`)
unconditionally in `τ : ℂ`: when `τ.im ≠ 0`, `ℤ + τℤ` is a lattice and this expresses double
periodicity and descent to the complex torus `ℂ / (ℤ + τℤ)`
(`TauCeti.thetaMetric_add_mul_norm_sq`); when `τ.im = 0`, either `k = 0` (where `thetaMetric` is
`1` and the multiplier has modulus `1`) or `k > 0` (where `s = 0` by
`TauCeti.thetaSections_eq_bot_of_im_nonpos`).

## Main results

* `TauCeti.thetaMetric_add_mul_norm_sq_of_mem_thetaSections`: unconditional invariance of the
  pointwise Hermitian norm squared on `thetaSections` under translations `z ↦ z + m + n * τ`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

namespace TauCeti

/-- For every theta section `s`, the pointwise Hermitian norm squared `thetaMetric k τ z * ‖s z‖²`
is invariant under all translations `z ↦ z + m + n * τ` (`m, n : ℤ`), unconditionally in `τ`.
When `τ.im ≠ 0`, `ℤ + τℤ` is a lattice and this expresses double periodicity (descent to the
complex torus `ℂ / (ℤ + τℤ)`). -/
theorem thetaMetric_add_mul_norm_sq_of_mem_thetaSections {k : ℕ} {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  by_cases hτ : τ.im = 0
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [add_eq_thetaFactor_mul_of_mem_thetaSections hs m n z, norm_mul, mul_pow,
        norm_thetaFactor]
      simp [thetaMetric_def]
    · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ.le α β, Submodule.mem_bot] at hs
      simp [hs]
  · exact thetaMetric_add_mul_norm_sq hτ
      (add_eq_thetaFactor_mul_of_mem_thetaSections hs m n z)

end TauCeti
