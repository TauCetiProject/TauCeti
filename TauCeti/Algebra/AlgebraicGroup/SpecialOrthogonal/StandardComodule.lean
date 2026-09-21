/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic

/-!
# The standard representation of the special orthogonal group

The standard representation of the special orthogonal group scheme `SOₙ` is obtained by
corestricting the standard `O(GLₙ)`-comodule along the quotient coordinate morphism

```text
O(GLₙ) ⟶ O(SOₙ).
```

This representation is faithful in every rank. Its action on algebra-valued points is ordinary
matrix-vector multiplication by the corresponding special orthogonal matrix. Consequently every
subcomodule is stable under the action of every base-valued special orthogonal matrix.

## Main declarations

* `TauCeti.SpecialOrthogonal.standardComodule`: the standard `O(SOₙ)`-comodule on `Rⁿ`.
* `TauCeti.SpecialOrthogonal.isFaithful_standardComodule`: the standard comodule is faithful.
* `TauCeti.SpecialOrthogonal.piScalarRight_comp_endOfPoint`: a point acts after scalar extension
  by its special orthogonal matrix.
* `TauCeti.SpecialOrthogonal.mulVec_mem`: standard subcomodules are stable under special
  orthogonal matrices.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3 and 4.a.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The construction follows the corestriction and point-action interface of
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule`.
-/

public section

open Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.SpecialOrthogonal

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The standard right comodule of the special orthogonal coordinate Hopf algebra, obtained by
corestricting the standard `GLₙ`-comodule along the special orthogonal quotient map. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R n) (Fin n → R) :=
  let _ := GeneralLinear.standardComodule R n
  Comodule.Corestrict (coordinateMap R n).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard special orthogonal coaction is the standard general-linear coaction followed by
the quotient map on the coordinate factor. -/
@[simp]
theorem standardComodule_coact :
    let _ := GeneralLinear.standardComodule R n
    Comodule.corestrictCoact
        (R := R) (C := GeneralLinear.coordinateHopfAlgebra R n)
        (D := coordinateHopfAlgebra R n) (M := Fin n → R)
        (coordinateMap R n).hom.toCoalgHom =
      TensorProduct.map LinearMap.id
          (Bialgebra.Quotient.mkBialgHom (R := R)
            (definingHopfIdeal R n).toIdeal).toLinearMap ∘ₗ
        GeneralLinear.standardCoact R n := by
  rw [coordinateMap_def, CommHopfAlgCat.hom_mkQuotient]
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, LinearMap.comp_apply,
    GeneralLinear.standardComodule_coact]

/-- **The standard comodule of `SOₙ` is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R n) (V := Fin n → R) := by
  unfold standardComodule
  exact Comodule.isFaithful_corestrict_of_surjective (coordinateMap R n).hom
    (by rw [coordinateMap_def]; exact CommHopfAlgCat.mkQuotient_surjective _ _)
    (GeneralLinear.isFaithful_standardComodule R n)

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under the canonical scalar-extension identification `A ⊗[R] Rⁿ ≃ Aⁿ`, a point of
`SOₙ` acts on the standard comodule by multiplication with its special orthogonal matrix. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin n)).toLinearMap.comp
        (Comodule.endOfPoint (Fin n → R) g.ofConv) =
      (Matrix.mulVecLin
          (pointsMulEquiv R n (A := A) g : Matrix (Fin n) (Fin n) A)).comp
        (TensorProduct.piScalarRight R A A (Fin n)).toLinearMap := by
  let q := CommHopfAlgCat.quotientPointsHom
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
    (CommAlgCat.of R A) g
  have hpoint :
      g.ofConv.comp ((coordinateMap R n).hom :
        GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n) =
        q.ofConv := by
    rw [coordinateMap_def]
    simpa only [q, WithConv.ofConv_toConv] using
      congrArg (fun f ↦ f.ofConv)
        (CommHopfAlgCat.quotientPointsHom_apply
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
          (CommAlgCat.of R A) g).symm
  have hmatrix :
      (GeneralLinear.pointToGeneralLinear n q : Matrix (Fin n) (Fin n) A) =
        (pointsMulEquiv R n (A := A) g : Matrix (Fin n) (Fin n) A) := by
    rw [← GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_coe]
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun (GeneralLinear.piScalarRight_comp_endOfPoint R n q) x
  rw [Comodule.endOfPoint_corestrict, hpoint]
  simpa only [LinearMap.comp_apply, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply, hmatrix] using hx

end PointAction

/-- **A subcomodule of the standard special orthogonal comodule is stable under every special
orthogonal matrix.** -/
theorem mulVec_mem (N : Subcomodule R (coordinateHopfAlgebra R n) (Fin n → R))
    (g : Matrix.specialOrthogonalGroup (Fin n) R) {w : Fin n → R} (hw : w ∈ N) :
    (g : Matrix (Fin n) (Fin n) R) *ᵥ w ∈ N := by
  let q := (pointsMulEquiv (R := R) (A := R) n).symm g
  have h := Comodule.basePointsRepresentation_mem N q hw
  rw [Comodule.basePointsRepresentation_corestrict (coordinateMap R n).hom q,
    GeneralLinear.basePointsRepresentation_eq_mulVec] at h
  have hpoint :
      AlgHom.mapDomain (coordinateMap R n).hom q =
        CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
          (CommAlgCat.of R R) q := by
    rw [coordinateMap_def, AlgHom.mapDomain_apply,
      CommHopfAlgCat.quotientPointsHom_apply]
  rw [hpoint, ← GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_coe,
    MulEquiv.apply_symm_apply] at h
  exact h

end TauCeti.SpecialOrthogonal
