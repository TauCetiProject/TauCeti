/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Regular.SMul

/-!
# Linearized Jordan identity

The four-variable Jordan identity follows from Mathlib's operator linearization after
cancelling `2`. It requires only absence of `2`-torsion, and supplies the common algebraic
identity used for Peirce products and inner derivations.
-/

public section

namespace TauCeti.Jordan

/-- Invertibility of `2` in the scalar ring makes doubling injective on the module. -/
theorem isSMulRegular_two (R J : Type*) [CommRing R] [AddCommGroup J] [Module R J]
    [Invertible (2 : R)] : IsSMulRegular J (2 : ℕ) := by
  intro x y h
  apply (isUnit_of_invertible (2 : R)).isSMulRegular J
  simpa only [← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat] using h

/-- The evaluated four-variable linearized Jordan identity, with no `2`-torsion. -/
theorem mul_mul_mul_sub_add_add_eq_zero {J : Type*} [NonUnitalNonAssocCommRing J]
    [IsCommJordan J] (h2 : IsSMulRegular J (2 : ℕ)) (a b c d : J) :
    a * (b * c * d) - b * c * (a * d) + (b * (c * a * d) - c * a * (b * d)) +
      (c * (a * b * d) - a * b * (c * d)) = 0 := by
  apply h2
  have h := DFunLike.congr_fun (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c) d
  simp only [Ring.lie_def] at h
  -- Evaluation of AddMonoid.End respects its pointwise operations and composition by definition.
  exact h.trans (smul_zero _).symm

end TauCeti.Jordan
