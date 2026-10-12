/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

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
* `TauCeti.SpecialOrthogonal.basePointsRepresentation_eq_mulVec`: a base-valued point acts by
  its special orthogonal matrix.
* `TauCeti.SpecialOrthogonal.scalar_sq_eq_one_of_basePointsRepresentation_eq_smul`: a point
  acting as a scalar has scalar a square root of one.
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

-- `@[simp]` would fail `simpNF`: the left-hand side already simplifies via
-- `basePointsRepresentation_corestrict` and the general-linear action formula.
/-- A base-valued point acts on the standard special orthogonal comodule by its matrix. -/
theorem basePointsRepresentation_eq_mulVec
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] R)) (v : Fin n → R) :
    Comodule.basePointsRepresentation (R := R) (H := coordinateHopfAlgebra R n) (Fin n → R) g v =
      (pointsMulEquiv (R := R) (A := R) n g : Matrix (Fin n) (Fin n) R) *ᵥ v := by
  rw [Comodule.basePointsRepresentation_corestrict (coordinateMap R n).hom g,
    GeneralLinear.basePointsRepresentation_eq_mulVec]
  have hpoint :
      AlgHom.mapDomain (coordinateMap R n).hom g =
        CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
          (CommAlgCat.of R R) g := by
    rw [coordinateMap_def, AlgHom.mapDomain_apply, CommHopfAlgCat.quotientPointsHom_apply]
  rw [hpoint, ← GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_coe]

/-- A scalar point in the standard representation of `SOₙ`, for `n ≠ 0`, has scalar a square
root of one: the scalar matrix `c • 1` is orthogonal only when `c ^ 2 = 1`. -/
theorem scalar_sq_eq_one_of_basePointsRepresentation_eq_smul (hn : n ≠ 0)
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] R)) (c : R)
    (hc : Comodule.basePointsRepresentation (R := R) (H := coordinateHopfAlgebra R n)
      (Fin n → R) g = c • (1 : Module.End R (Fin n → R))) : c ^ 2 = 1 := by
  have hmat : (pointsMulEquiv (R := R) (A := R) n g : Matrix (Fin n) (Fin n) R) =
      c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hv := LinearMap.congr_fun hc v
    rw [basePointsRepresentation_eq_mulVec] at hv
    simpa [Matrix.smul_mulVec] using hv
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  exact sq_eq_one_of_smul_one_mem_orthogonalGroup
    (hmat ▸ (Matrix.mem_specialOrthogonalGroup_iff.mp
      (pointsMulEquiv (R := R) (A := R) n g).2).1)

/-- **A subcomodule of the standard special orthogonal comodule is stable under every special
orthogonal matrix.** -/
theorem mulVec_mem (N : Subcomodule R (coordinateHopfAlgebra R n) (Fin n → R))
    (g : Matrix.specialOrthogonalGroup (Fin n) R) {w : Fin n → R} (hw : w ∈ N) :
    (g : Matrix (Fin n) (Fin n) R) *ᵥ w ∈ N := by
  have h := Comodule.basePointsRepresentation_mem N
    ((pointsMulEquiv (R := R) (A := R) n).symm g) hw
  rwa [basePointsRepresentation_eq_mulVec, MulEquiv.apply_symm_apply] at h

end TauCeti.SpecialOrthogonal
