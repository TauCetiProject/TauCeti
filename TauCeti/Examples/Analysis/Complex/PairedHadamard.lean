/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Hadamard.Paired

/-!
# Example: derivative positivity for `Complex.cosh` via paired Hadamard factorization

`Complex.cosh` is entire of order one, even (`δ = 1`), has all zeros on the imaginary axis, is
strictly positive on `ℝ`, and is not a polynomial, so `TauCeti.pairedHadamard_derivatives_positive`
shows that `(iteratedDeriv k Complex.cosh (x : ℂ)).re > 0` for every `k : ℕ` and every `x > 0`.
-/

namespace TauCeti.PairedHadamardExamples

open Complex

/-- `Complex.cosh` satisfies the paired Hadamard hypotheses with `δ = 1` and is not a polynomial,
so every iterated derivative `iteratedDeriv k Complex.cosh (x : ℂ)` has strictly positive real part
for all `x > 0`. -/
example (k : ℕ) (x : ℝ) (hx : 0 < x) :
    0 < (iteratedDeriv k Complex.cosh (x : ℂ)).re := by
  have hcosh_eq : Complex.cosh = fun z : ℂ ↦ (2 : ℂ)⁻¹ * (exp z + exp (-z)) := by
    ext z; rw [Complex.cosh, div_eq_inv_mul, mul_comm]
  have hf : IsCenteredOrderOne Complex.cosh := by
    rw [hcosh_eq]
    exact (isCenteredOrderOne_cexp.add isCenteredOrderOne_cexp.comp_neg).const_mul (2 : ℂ)⁻¹
  have hzeros (z : ℂ) (hz : Complex.cosh z = 0) : z.re = 0 := by
    rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff] at hz
    obtain ⟨n, hn⟩ := hz
    simpa using congrArg Complex.im hn
  have hpos : ∃ R : ℝ, ∀ y : ℝ, R ≤ y → (Complex.cosh (y : ℂ)).im = 0 ∧
      0 < (Complex.cosh (y : ℂ)).re :=
    ⟨0, fun y _ ↦ by rw [← Complex.ofReal_cosh, ofReal_im, ofReal_re]; exact ⟨rfl, Real.cosh_pos y⟩⟩
  have hnonpoly : ¬ ∃ P : Polynomial ℂ, ∀ z, Complex.cosh z = P.eval z := by
    rintro ⟨P, hP⟩
    set m : ℕ := P.natDegree + 1
    have h1 : iteratedDeriv (2 * m) Complex.cosh 0 = 1 := by
      rw [Complex.iteratedDeriv_even_cosh, Complex.cosh_zero]
    have h0 : iteratedDeriv (2 * m) Complex.cosh 0 = 0 := by
      rw [funext hP, P.iteratedDeriv, Polynomial.iterate_derivative_eq_zero (by omega)]
      simp
    exact one_ne_zero (h1.symm.trans h0)
  exact pairedHadamard_derivatives_positive (δ := 1) hf
    (fun z ↦ by simp [Complex.cosh_neg]) hzeros hpos hnonpoly k x hx

end TauCeti.PairedHadamardExamples
