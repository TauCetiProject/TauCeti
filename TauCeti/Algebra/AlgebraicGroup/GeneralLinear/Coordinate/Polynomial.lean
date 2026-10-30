/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial

/-!
# Polynomial coordinates inside the general linear coordinate algebra

The inclusion of polynomial matrix coordinates in determinant-localized coordinates
preserves comultiplication and counit. It therefore restricts rational matrix-monoid
actions to rational general-linear actions, including over finite fields.

This bundles `TauCeti.GeneralLinear.coordinateRingMap` using the matrix-multiplication
bialgebra of `TauCeti.MatrixMonoid.coordinateBialgebra`. See J. A. Green,
*Polynomial Representations of GLₙ*, §1, for the coefficient-algebra viewpoint.
-/

public section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The determinant localization map is injective over every commutative ring,
including the zero ring and matrices of size zero. -/
theorem coordinateRingMap_injective : Function.Injective (coordinateRingMap R n) := by
  intro p q h
  apply IsLocalization.injective (CoordinateRing R n)
    (Submonoid.powers_le.mpr (Matrix.det_mvPolynomialX_mem_nonZeroDivisors
      (R := R) (n := Fin n)))
  simpa only [coordinateRingMap_apply] using h

/-- The determinant localization map transported across the bundled coordinate algebras. -/
private noncomputable def polynomialCoordinateAlgHom :
    MatrixMonoid.coordinateBialgebra R n →ₐ[R] coordinateHopfAlgebra R n :=
  ((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n)).comp
    (MatrixMonoid.coordinateBialgebraAlgEquiv R n).symm.toAlgHom

@[simp]
private theorem polynomialCoordinateAlgHom_apply (p : MatrixMonoid.CoordinateRing R n) :
    polynomialCoordinateAlgHom R n (MatrixMonoid.coordinateBialgebraAlgEquiv R n p) =
      coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p) := by
  simp [polynomialCoordinateAlgHom]

/-- The tensor square of the transported map is the transported localization tensor square. -/
private theorem polynomialCoordinateAlgHom_tensorSquare :
    (Algebra.TensorProduct.map (polynomialCoordinateAlgHom R n)
      (polynomialCoordinateAlgHom R n)).comp
        (Algebra.TensorProduct.map (MatrixMonoid.coordinateBialgebraAlgEquiv R n).toAlgHom
          (MatrixMonoid.coordinateBialgebraAlgEquiv R n).toAlgHom) =
      (Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
        (coordinateHopfAlgebraAlgEquiv R n).toAlgHom).comp
          (Algebra.TensorProduct.map (coordinateRingMap R n) (coordinateRingMap R n)) := by
  ext p <;> simp

/-- Polynomial matrix coordinates included in the coordinate Hopf algebra of `GLₙ`.
This is the coordinate morphism of the open inclusion `GLₙ → Matₙ`. -/
noncomputable def polynomialCoordinateBialgHom :
    MatrixMonoid.coordinateBialgebra R n →ₐc[R] coordinateHopfAlgebra R n :=
  BialgHom.ofAlgHom (polynomialCoordinateAlgHom R n)
    (by
      apply (AlgHom.cancel_right (f := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).toAlgHom)
        (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective).mp
      ext p
      simp)
    (by
      apply (AlgHom.cancel_right (f := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).toAlgHom)
        (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective).mp
      apply AlgHom.ext
      intro p
      simpa [comul_coordinateRingMap] using
        DFunLike.congr_fun (polynomialCoordinateAlgHom_tensorSquare R n)
          (MatrixMonoid.comul R n p))

/-- The polynomial coordinate inclusion is the determinant localization map under the
canonical coordinate-algebra identifications. -/
@[simp]
theorem polynomialCoordinateBialgHom_apply (p : MatrixMonoid.CoordinateRing R n) :
    polynomialCoordinateBialgHom R n (MatrixMonoid.coordinateBialgebraAlgEquiv R n p) =
      coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p) := by
  simp [polynomialCoordinateBialgHom]

/-- Over every commutative ring, polynomial matrix coordinates inject into
determinant-localized coordinates. This includes size zero and the zero ring. -/
theorem polynomialCoordinateBialgHom_injective :
    Function.Injective (polynomialCoordinateBialgHom R n) := by
  intro x y h
  obtain ⟨p, rfl⟩ := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective x
  obtain ⟨q, rfl⟩ := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective y
  rw [polynomialCoordinateBialgHom_apply, polynomialCoordinateBialgHom_apply] at h
  exact congrArg (MatrixMonoid.coordinateBialgebraAlgEquiv R n)
    (coordinateRingMap_injective R n ((coordinateHopfAlgebraAlgEquiv R n).injective h))

end TauCeti.GeneralLinear
