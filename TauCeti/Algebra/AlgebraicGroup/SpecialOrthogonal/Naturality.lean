/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Basic

/-!
# Naturality of special orthogonal points

The equivalence between points of the standard special orthogonal coordinate Hopf algebra and
special orthogonal matrices commutes with extension of scalars.  This compatibility lets
geometric arguments pass freely between the functor-of-points and matrix descriptions.

## Main declaration

* `TauCeti.SpecialOrthogonal.pointsMulEquiv_mapValue`: evaluating a point after a ring map
  corresponds to mapping every entry of its special orthogonal matrix.
-/

public section

open WithConv

namespace TauCeti.SpecialOrthogonal

universe u v w

noncomputable section

attribute [local instance] starRingOfComm

variable {R : Type u} [CommRing R] (n : ℕ)
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The matrix description of special orthogonal points is natural under algebra maps. -/
theorem pointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv R n (A := B)
        (AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi f) =
      Matrix.SpecialOrthogonalGroup.map phi.toRingHom
        (pointsMulEquiv R n (A := A) f) := by
  apply Subtype.ext
  have hcoe_lhs := pointsMulEquiv_coe R n
    (AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi f)
  have hcoe_rhs := pointsMulEquiv_coe R n f
  have hnatural := (CommHopfAlgCat.mapValue_quotientPointsHom
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n) phi f).symm
  rw [← hcoe_lhs, hnatural, GeneralLinear.pointsMulEquiv_mapValue,
    Matrix.SpecialOrthogonalGroup.coe_map]
  simpa only [Matrix.GeneralLinearGroup.val_map_apply] using
    congrArg (fun M : Matrix (Fin n) (Fin n) A ↦ M.map phi.toRingHom) hcoe_rhs

/-- Naturality of the inverse pointwise equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (phi : A →ₐ[R] B)
    (g : Matrix.specialOrthogonalGroup (Fin n) A) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R n) phi
        ((pointsMulEquiv R n (A := A)).symm g) =
      (pointsMulEquiv R n (A := B)).symm
        (Matrix.SpecialOrthogonalGroup.map phi.toRingHom g) := by
  apply (pointsMulEquiv R n (A := B)).injective
  rw [pointsMulEquiv_mapValue]
  simp

end

end TauCeti.SpecialOrthogonal
