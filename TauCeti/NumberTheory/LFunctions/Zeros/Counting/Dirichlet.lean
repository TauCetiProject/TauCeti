/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Counting.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

/-!
# Symmetric zero counts of primitive Dirichlet L-functions

The dual of the card of a primitive Dirichlet character `χ` is the card of `χ⁻¹`
(`TauCeti.LFunctions.dirichletData_dual`). The zeros of the completed L-function of `χ` below the
real axis are therefore counted by the one-sided counting function of `χ⁻¹`: the count of `χ`
below the axis is the count of `χ⁻¹` above it. At a nonnegative height `T` the symmetric count of
`χ` is `N(T, χ) + N(T, χ⁻¹)` plus the zeros on the real segment `[0, 1]`. For a real character the
two one-sided counts coincide, so the symmetric count is `2 N(T, χ)` plus the real zeros.

For a non-real character the two one-sided counts differ in general, so the symmetric count is not
twice either of them.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §16.
-/

public section

open Set Complex

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)

/-- **The count of `χ⁻¹` above the real axis is the count of `χ` below it.** The one-sided
count of the inverse character at height `T` is the number of zeros of the completed
L-function of `χ` in `0 ≤ Re s ≤ 1`, `-T ≤ Im s < 0`, counted with multiplicity. -/
theorem dirichletData_inv_zeroCountingFunction (T : ℝ) :
    (dirichletData χ⁻¹ hχ.inv).zeroCountingFunction T =
      zeroCount (dirichletData χ hχ).completed univ (Icc 0 1 ×ℂ Ico (-T) 0) := by
  rw [← dirichletData_dual, AnalyticLFunctionData.zeroCountingFunction_dual]

/-- **The symmetric count of a primitive Dirichlet L-function.** At a nonnegative height `T`, the
symmetric count of `χ` is the one-sided count of `χ`, plus the one-sided count of `χ⁻¹`, plus the
zeros of the completed L-function of `χ` on the real segment `[0, 1]`. -/
theorem dirichletData_symmetricZeroCountingFunction {T : ℝ} (hT : 0 ≤ T) :
    (dirichletData χ hχ).symmetricZeroCountingFunction T =
      (dirichletData χ hχ).zeroCountingFunction T +
        (dirichletData χ⁻¹ hχ.inv).zeroCountingFunction T +
          (dirichletData χ hχ).symmetricZeroCountingFunction 0 := by
  rw [← dirichletData_dual, (dirichletData χ hχ).symmetricZeroCountingFunction_eq_add hT]

/-- **The symmetric count of a real primitive Dirichlet L-function.** For a real character, at a
nonnegative height `T`, the symmetric count is twice the one-sided count plus the zeros on the
real segment `[0, 1]`. -/
theorem dirichletData_symmetricZeroCountingFunction_of_inv_eq (hreal : χ⁻¹ = χ) {T : ℝ}
    (hT : 0 ≤ T) :
    (dirichletData χ hχ).symmetricZeroCountingFunction T =
      2 * (dirichletData χ hχ).zeroCountingFunction T +
        (dirichletData χ hχ).symmetricZeroCountingFunction 0 := by
  rw [dirichletData_symmetricZeroCountingFunction hχ hT, dirichletData_inv_of_inv_eq χ hχ hreal,
    two_mul]

end TauCeti.LFunctions
