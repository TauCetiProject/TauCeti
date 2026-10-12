/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic

/-!
# Counit-valued points of the special linear group

A point of `SLₙ` valued in the counit algebra determines a determinant-one matrix. Its image
under the closed-subgroup inclusion is the corresponding counit-valued point of `GLₙ`.

## Main declarations

* `TauCeti.SpecialLinear.counitPointsMulEquiv`: the determinant-one matrix of a counit-valued
  point.
* `TauCeti.SpecialLinear.toGL_counitPointsMulEquiv`: compatibility with the inclusion into
  `GLₙ`.
-/

public section

namespace TauCeti.SpecialLinear

open WithConv

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
variable (n : ℕ)

/-- The determinant-one matrix of a point of `SLₙ` valued in its counit algebra. -/
noncomputable def counitPointsMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R]
        Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃*
      Matrix.SpecialLinearGroup (Fin n) B :=
  (Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B).trans
    (pointsMulEquiv (R := R) (A := B) n)

/-- The determinant-one matrix of a counit-valued point is the matrix of its transported
ordinary point. -/
theorem counitPointsMulEquiv_eq_pointsMulEquiv
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R]
      Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    counitPointsMulEquiv n g = pointsMulEquiv (R := R) (A := B) n
      ((Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B) g) :=
  (rfl)

/-- The image in `GLₙ` of a counit-valued `SLₙ` point is its canonical inclusion. -/
@[simp]
theorem toGL_counitPointsMulEquiv
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R]
      Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    Matrix.SpecialLinearGroup.toGL (counitPointsMulEquiv n g) =
      GeneralLinear.counitPointsMulEquiv n
        (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
          (GeneralLinear.coordinateHopfAlgebra R n) B) (coordinateMap R n).hom g) := by
  rw [counitPointsMulEquiv, MulEquiv.trans_apply]
  rw [GeneralLinear.counitPointsMulEquiv_eq_pointsMulEquiv]
  rw [← pointsMulEquiv_toGL (R := R) (A := B) n]
  rw [CommHopfAlgCat.quotientPointsHom_apply]
  congr 1
  ext x
  simp only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    Bialgebra.CounitAlgebra.pointsMulEquiv_apply]
  -- The two point transports use counit algebras of different coordinate rings. Expose
  -- application of the transported ambient point so `mapDomain_apply_apply` can rewrite it.
  change _ = Bialgebra.CounitAlgebra.algEquivSelf R
    (GeneralLinear.coordinateHopfAlgebra R n) B
      (AlgHom.mapDomain (coordinateMap R n).hom g x)
  rw [AlgHom.mapDomain_apply_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply]
  rw [CommHopfAlgCat.hom_mkQuotient]
  exact (Bialgebra.CounitAlgebra.algEquivSelf_apply
    (R := R) (A := GeneralLinear.coordinateHopfAlgebra R n) (B := B)
      (g.ofConv ((coordinateMap R n).hom x))).symm

end TauCeti.SpecialLinear
