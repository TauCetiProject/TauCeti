/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.TwoPiI
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Real Tate lines in the complex numbers

The real Tate line of weight `k` is `(2πi)^k ℝ`, regarded as a real submodule of `ℂ`.
Membership is equivalent to the corresponding signed conjugation equation.
-/

public section

noncomputable section

open ComplexConjugate

namespace Complex

/-- The real Tate line `(2πi)^k ℝ` in the complex numbers. -/
def realTateLine (k : ℕ) : Submodule ℝ ℂ :=
  Submodule.span ℝ {((2 * Real.pi * I : ℂ) ^ k)}

/-- Membership in the real Tate line means being a real multiple of `(2πi)^k`. -/
@[simp]
theorem mem_realTateLine_iff (k : ℕ) (z : ℂ) :
    z ∈ realTateLine k ↔ ∃ r : ℝ, z = (r : ℂ) * (2 * Real.pi * I : ℂ) ^ k := by
  simp only [realTateLine, Submodule.mem_span_singleton, real_smul, eq_comm]

/-- Signed conjugation characterizes the real Tate line. -/
theorem mem_realTateLine_iff_conj_eq (k : ℕ) (z : ℂ) :
    z ∈ realTateLine k ↔ conj z = (-1 : ℂ) ^ k * z := by
  rw [mem_realTateLine_iff]
  constructor
  · rintro ⟨r, rfl⟩
    rw [map_mul, conj_ofReal, conj_two_pi_I_pow]
    exact mul_left_comm _ _ _
  · intro hz
    have ht : (2 * Real.pi * I : ℂ) ^ k ≠ 0 := pow_ne_zero k two_pi_I_ne_zero
    have hreal : conj (z / (2 * Real.pi * I : ℂ) ^ k) =
        z / (2 * Real.pi * I : ℂ) ^ k := by
      rw [map_div₀, hz, conj_two_pi_I_pow]
      exact mul_div_mul_left z _ (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero))
    refine ⟨(z / (2 * Real.pi * I : ℂ) ^ k).re, ?_⟩
    rw [conj_eq_iff_re.mp hreal, div_mul_cancel₀ _ ht]

end Complex
