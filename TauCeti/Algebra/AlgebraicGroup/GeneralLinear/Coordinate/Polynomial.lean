/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra

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

/-- Polynomial matrix coordinates included in the coordinate Hopf algebra of `GLₙ`.
This is the coordinate morphism of the open inclusion `GLₙ → Matₙ`. -/
noncomputable def polynomialCoordinateBialgHom :
    MatrixMonoid.coordinateBialgebra R n →ₐc[R] coordinateHopfAlgebra R n :=
  BialgHom.ofAlgHom
    (((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n)).comp
      (MatrixMonoid.coordinateBialgebraAlgEquiv R n).symm.toAlgHom)
    (by
      ext x
      obtain ⟨p, rfl⟩ := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective x
      simp)
    (by
      ext x
      obtain ⟨p, rfl⟩ := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective x
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        MatrixMonoid.coordinateBialgebra_comul_apply,
        coordinateHopfAlgebra_comul_apply, AlgEquiv.coe_toAlgHom,
        AlgEquiv.symm_apply_apply]
      rw [comul_coordinateRingMap]
      have hmap :
          (Algebra.TensorProduct.map
            (((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n)).comp
              (MatrixMonoid.coordinateBialgebraAlgEquiv R n).symm.toAlgHom)
            (((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n)).comp
              (MatrixMonoid.coordinateBialgebraAlgEquiv R n).symm.toAlgHom)).comp
            (Algebra.TensorProduct.map
              (MatrixMonoid.coordinateBialgebraAlgEquiv R n).toAlgHom
              (MatrixMonoid.coordinateBialgebraAlgEquiv R n).toAlgHom) =
          (Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
            (coordinateHopfAlgebraAlgEquiv R n).toAlgHom).comp
              (Algebra.TensorProduct.map (coordinateRingMap R n) (coordinateRingMap R n)) := by
        ext p <;> simp
      exact DFunLike.congr_fun hmap (MatrixMonoid.comul R n p))

/-- The polynomial coordinate inclusion is the determinant localization map under the
canonical coordinate-algebra identifications. -/
@[simp]
theorem polynomialCoordinateBialgHom_apply (p : MatrixMonoid.CoordinateRing R n) :
    polynomialCoordinateBialgHom R n (MatrixMonoid.coordinateBialgebraAlgEquiv R n p) =
      coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p) := by
  simp [polynomialCoordinateBialgHom]

/-- Over a domain, polynomial matrix coordinates inject into determinant-localized
coordinates. This includes size zero, where the determinant is one. -/
theorem polynomialCoordinateBialgHom_injective [IsDomain R] :
    Function.Injective (polynomialCoordinateBialgHom R n) := by
  have hi : Function.Injective (coordinateRingMap R n) := by
    intro p q h
    apply IsLocalization.injective (CoordinateRing R n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (Matrix.det_mvPolynomialX_ne_zero (Fin n) R))
    simpa only [coordinateRingMap_apply] using h
  intro x y h
  obtain ⟨p, rfl⟩ := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective x
  obtain ⟨q, rfl⟩ := (MatrixMonoid.coordinateBialgebraAlgEquiv R n).surjective y
  rw [polynomialCoordinateBialgHom_apply, polynomialCoordinateBialgHom_apply] at h
  exact congrArg (MatrixMonoid.coordinateBialgebraAlgEquiv R n)
    (hi ((coordinateHopfAlgebraAlgEquiv R n).injective h))

end TauCeti.GeneralLinear
