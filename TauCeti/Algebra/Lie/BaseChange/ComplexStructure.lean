/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.LinearAlgebra.Complex.Module

/-!
# Transported complex structures and Lie brackets

A real Lie equivalence from a complex Lie algebra transports multiplication by `Complex.I`
through its underlying linear equivalence. The resulting endomorphism commutes with the Lie
bracket in both arguments. The construction, square laws and composition laws require only
linear equivalences and live in `TauCeti.LinearAlgebra.Complex.Module`.

## Main results

* `RestrictScalars.addEquiv_lie`: the additive scalar-restriction identification preserves brackets.
* `LieEquiv.complexStructure_lie_left` and `LieEquiv.complexStructure_lie_right`:
  compatibility of a transported complex structure with the bracket.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1.
-/

public section

/-- The additive identification for scalar restriction preserves the Lie bracket. -/
theorem RestrictScalars.addEquiv_lie {R A L : Type*} [LieRing L]
    (x y : RestrictScalars R A L) :
    RestrictScalars.addEquiv R A L ⁅x, y⁆ =
      ⁅RestrictScalars.addEquiv R A L x, RestrictScalars.addEquiv R A L y⁆ := rfl

namespace LieEquiv

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℝ L']
  (e : RestrictScalars ℝ ℂ L ≃ₗ⁅ℝ⁆ L')

/-- The transported complex structure commutes with the bracket in its first argument. -/
@[simp]
theorem complexStructure_lie_left (X Y : L') :
    ⁅e.toLinearEquiv.complexStructure (M := L) X, Y⁆ =
      e.toLinearEquiv.complexStructure (M := L) ⁅X, Y⁆ := by
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective X
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective Y
  have hlie (u v : RestrictScalars ℝ ℂ L) :
      ⁅e.toLinearEquiv u, e.toLinearEquiv v⁆ = e.toLinearEquiv ⁅u, v⁆ := e.map_lie u v |>.symm
  -- The restricted Lie ring inherits its additive structure through a type synonym;
  -- `erw` identifies it with the original structure used by the linear transport.
  erw [e.toLinearEquiv.complexStructure_apply_image (M := L),
    hlie, hlie, e.toLinearEquiv.complexStructure_apply_image (M := L)]
  apply congrArg e.toLinearEquiv
  apply (RestrictScalars.addEquiv ℝ ℂ L).injective
  rw [RestrictScalars.addEquiv_lie, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_lie, smul_lie]

/-- The transported complex structure commutes with the bracket in its second argument. -/
@[simp]
theorem complexStructure_lie_right (X Y : L') :
    ⁅X, e.toLinearEquiv.complexStructure (M := L) Y⁆ =
      e.toLinearEquiv.complexStructure (M := L) ⁅X, Y⁆ := by
  rw [← lie_skew X (e.toLinearEquiv.complexStructure (M := L) Y),
    e.complexStructure_lie_left, ← map_neg, lie_skew X Y]

end LieEquiv
