/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Borel

/-!
# Base change of the upper-triangular Borel of `SLₙ`

Scalar extension of the coordinate Hopf algebra of the upper-triangular subgroup of `SLₙ`
is canonically its coordinate Hopf algebra over the new base. The isomorphism commutes with
restriction of functions from `SLₙ`, and the induced point equivalence preserves the
upper-triangular determinant-one matrix over every value algebra. In particular, extending
the base of the standard Borel does not change its embedding in the special linear group.

No flatness or reducedness assumption on the base extension is needed. The construction
uses `CommHopfAlgCat.quotientBaseChangeIsoOfMapEq` and the existing equality
`SpecialLinear.UpperTriangular.map_baseChangeHopfIdeal_definingHopfIdeal`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.SpecialLinear.UpperTriangular

universe u v w

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

/-- Scalar extension of the upper-triangular special-linear coordinate Hopf algebra is
canonically the upper-triangular coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≅
      coordinateHopfAlgebra K n :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R n) (definingHopfIdeal K n)
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K n)

/-- The Borel base-change isomorphism commutes with restriction of functions from `SLₙ`.
Contravariantly, this identifies the base change of the Borel inclusion with the inclusion
constructed over the new base. -/
@[simp, reassoc]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n) ≫
        (coordinateHopfAlgebraBaseChangeIso R K n).hom =
      (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫ coordinateMap K n :=
  CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R n) (definingHopfIdeal K n)
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K n)

/-- On a pure tensor of a restricted ambient function, the Borel base-change isomorphism
is the ambient special-linear base-change isomorphism followed by restriction. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap
    (s : K) (x : SpecialLinear.coordinateHopfAlgebra R n) :
    (coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (s ⊗ₜ[R] (coordinateMap R n).hom x) =
      (coordinateMap K n).hom
        ((SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (s ⊗ₜ[R] x)) := by
  have h := congrArg (fun f ↦ f.hom (s ⊗ₜ[R] x))
    (baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom R K n)
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at h
  rw [CommHopfAlgCat.baseChangeMap_apply_tmul (K := K) (coordinateMap R n) s x] at h
  exact h

/-- The canonical Borel base-change point equivalence preserves the upper-triangular
determinant-one matrix, over every commutative value algebra. -/
-- Use `rw` with explicit base-ring arguments: the `max` universe of the extension ring
-- prevents reliable automatic matching by `simp`.
theorem pointsMulEquiv_baseChangeIsoPointsMulEquiv
    (A : CommAlgCat.{w} K)
    (q : HopfAlgebra.points (R := K) (H := coordinateHopfAlgebra K n) A) :
    pointsMulEquiv R n
        (A := TauCeti.CommAlgCat.restrictScalarsObj (algebraMap R K) A)
        (CommHopfAlgCat.baseChangeIsoPointsMulEquiv
          (coordinateHopfAlgebraBaseChangeIso R K n).symm A q) =
      pointsMulEquiv K n (A := A) q := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [← pointsMulEquiv_coe, ← pointsMulEquiv_coe,
    ← SpecialLinear.pointsMulEquiv_toGL, ← SpecialLinear.pointsMulEquiv_toGL]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply]
  rw [CommHopfAlgCat.quotientPointsHom_apply, CommHopfAlgCat.quotientPointsHom_apply,
    CommHopfAlgCat.quotientPointsHom_apply, CommHopfAlgCat.quotientPointsHom_apply]
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  rw [CommHopfAlgCat.baseChangeIsoPointsMulEquiv_apply_apply]
  simp only [Iso.symm_inv]
  rw [coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap]
  congr 1
  have h := congrArg (fun f ↦ f.hom
      (1 ⊗ₜ[R] GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
        (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))))
    (SpecialLinear.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom
      R K n)
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at h
  rw [CommHopfAlgCat.baseChangeMap_apply_tmul (K := K)
    (SpecialLinear.coordinateMap R n)] at h
  rw [h]
  exact congrArg (fun x ↦ (coordinateMap K n).hom ((SpecialLinear.coordinateMap K n).hom x))
    (by
      simpa using GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v}
        R K n 1 (MvPolynomial.X (i, j)))

end TauCeti.SpecialLinear.UpperTriangular
