/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.SqrtDeriv
import TauCeti.Analysis.Complex.Sqrt

/-!
# Principal square roots of real linear forms on the upper half-plane

For real `m` and `n`, the principal square root of `m τ + n` is continuous on the upper
half-plane: `m τ + n` is constant if `m = 0`, and otherwise stays off the real axis, where the
branch cut lies. For an integer matrix `(a b; c d)` this is the square root `√(c τ + d)` of its
automorphy factor, as in half-integral-weight transformation laws; it never vanishes on `ℍ`.

## Main results

* `UpperHalfPlane.continuous_sqrt_ofReal_mul_add`: `τ ↦ √(m τ + n)` is continuous on `ℍ`.
* `UpperHalfPlane.arg_ofReal_mul_add_eq_pi_iff`: `arg (m τ + n) = π ↔ m = 0 ∧ n < 0`.
* `UpperHalfPlane.sqrt_denom_ne_zero`: the square root `√(c τ + d)` of an automorphy factor does
  not vanish on `ℍ`.
-/

public section

open Complex

open scoped Real UpperHalfPlane MatrixGroups

namespace UpperHalfPlane

/-- The principal square root of a real linear combination `m τ + n` is continuous on the upper
half-plane: it is constant if `m = 0`, and otherwise `m τ + n` stays off the real axis. -/
theorem continuous_sqrt_ofReal_mul_add (m n : ℝ) :
    Continuous fun τ : ℍ ↦ Complex.sqrt ((m : ℂ) * τ + n) := by
  by_cases hm : m = 0
  · simp only [hm, ofReal_zero, zero_mul, zero_add]
    exact continuous_const
  refine continuous_iff_continuousAt.2 fun τ ↦ ?_
  have him : ((m : ℂ) * τ + n).im ≠ 0 := by
    simpa [hm] using τ.im_pos.ne'
  exact (continuousAt_sqrt (Or.inr him)).comp
    (f := fun τ : ℍ ↦ (m : ℂ) * τ + n) (by fun_prop)

/-- A real linear combination `m τ + n` at `τ ∈ ℍ` lies on the negative real branch cut
(`arg = π`) if and only if `m = 0` and `n < 0`. -/
theorem arg_ofReal_mul_add_eq_pi_iff (m n : ℝ) (τ : ℍ) :
    ((m : ℂ) * τ + n).arg = π ↔ m = 0 ∧ n < 0 := by
  rw [Complex.arg_eq_pi_iff]
  constructor
  · rintro ⟨hre, him⟩
    have hm : m = 0 := by simpa [τ.im_ne_zero] using him
    subst hm
    exact ⟨rfl, by simpa using hre⟩
  · rintro ⟨rfl, hn⟩
    simpa using hn

/-- The principal square root `√(c τ + d)` of the automorphy factor of `γ = (a b; c d)` in
`SL(2, ℤ)` does not vanish on the upper half-plane. -/
theorem sqrt_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact sqrt_eq_zero_iff.not.2 (denom_ne_zero _ τ)

end UpperHalfPlane

end
