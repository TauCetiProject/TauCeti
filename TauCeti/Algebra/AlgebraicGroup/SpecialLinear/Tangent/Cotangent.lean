/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic

/-!
# The cotangent-dual Lie algebra of the special linear group

The dual of the augmentation cotangent space of `SLₙ` is canonically the classical
Lie algebra of trace-zero matrices. This identifies the cotangent-dual model used
for algebraic adjoint orbits and centralizers with the matrix model, preserving
both scalar multiplication and the Lie bracket. The equivalence includes `n = 0`.

The construction composes `Derivation.cotangentDualLieEquiv` with
`TauCeti.SpecialLinear.tangentLieEquivSl`; its matrix is the existing tangent matrix.
-/

public section

namespace TauCeti.SpecialLinear

universe u

variable {R : Type u} [CommRing R] (n : ℕ)

/-- The cotangent-dual Lie algebra of `SLₙ` is the Lie algebra of trace-zero matrices. -/
noncomputable def cotangentDualLieEquivSl :
    Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R n)) ≃ₗ⁅R⁆
      LieAlgebra.SpecialLinear.sl (Fin n) R :=
  (Derivation.cotangentDualLieEquiv (R := R) (H := coordinateHopfAlgebra R n)).trans
    (tangentLieEquivSl (R := R) (B := R) n)

/-- The cotangent-dual equivalence sends a functional to its trace-zero tangent matrix. -/
@[simp]
theorem cotangentDualLieEquivSl_apply
    (x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R n))) :
    cotangentDualLieEquivSl n x =
      tangentMatrix n (Derivation.cotangentLinearEquiv (B := R) x) := by
  simp only [cotangentDualLieEquivSl, LieEquiv.trans_apply,
    Derivation.cotangentDualLieEquiv_apply]
  exact tangentLieEquivSl_apply n _

/-- The inverse equivalence recovers the cotangent functional of a trace-zero tangent matrix. -/
@[simp]
theorem cotangentDualLieEquivSl_symm_apply (X : LieAlgebra.SpecialLinear.sl (Fin n) R) :
    (cotangentDualLieEquivSl (R := R) n).symm X =
      (Derivation.cotangentLinearEquiv (R := R) (A := coordinateHopfAlgebra R n)
        (B := R)).symm ((tangentLieEquivSl (R := R) (B := R) n).symm X) := by
  simp only [cotangentDualLieEquivSl, LieEquiv.symm_trans, LieEquiv.trans_apply,
    Derivation.cotangentDualLieEquiv_symm_apply]

end TauCeti.SpecialLinear
