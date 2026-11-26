/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# Transport of the orthogonal group scheme along isometries

Let `q` and `q'` be quadratic forms on `Rⁿ` and `P` an invertible matrix with `q'(P x) = q(x)` for
all `x ∈ Rⁿ`, an isometry from `q` to `q'`. Then conjugation by `P` carries the orthogonal group
scheme `O(q)` (`TauCeti.QuadraticOrthogonal.groupScheme`) isomorphically onto `O(q')`: if
`q(g x) = q(x)` for all `x`, then `q'(P g P⁻¹ y) = q(g P⁻¹ y) = q(P⁻¹ y) = q'(y)`.

The identity `q'(P x) = q(x)` over `R` propagates to every commutative `R`-algebra `A`: the matrix
`Pᵀ M' P - M`, for the coefficient matrices `M`, `M'` of `q`, `q'`, has vanishing quadratic
expression, so it is alternating (`Matrix.isAltMod_bot_iff`), and stays alternating over `A`
(`QuadraticForm.baseChangeForm_map_mulVec`). This uses nothing about `2`, so it holds in
characteristic two, where `q` is not determined by its polar form.

In coordinates, the coordinate automorphism `GeneralLinear.conjCoordinateIso Q` of conjugation by
`Q` pulls the defining Hopf ideal of `O(q)` back to that of `O(q')` when `q'(Q x) = q(x)`
(`TauCeti.QuadraticOrthogonal.definingHopfIdeal_comapOfSurjective_conjCoordinateIso`), as in
`TauCeti.ConstantForm.groupSchemeCongr` for constant matrices.

## Main declarations

* `TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraCongr`: for an isometry `P` from `q` to `q'`,
  the coordinate Hopf algebras of `O(q)` and `O(q')` are isomorphic, through conjugation by `P⁻¹`
  on `GLₙ`.
* `TauCeti.QuadraticOrthogonal.groupSchemeCongr`: the isomorphism `O(q) ≅ O(q')`.
* `TauCeti.QuadraticOrthogonal.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr` and
  `TauCeti.QuadraticOrthogonal.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr_inv`: on
  points, the coordinate isomorphism sends `g ∈ O(q')(A)` to `P⁻¹ g P`, and its inverse sends
  `g ∈ O(q)(A)` to `P g P⁻¹`.
* `TauCeti.QuadraticOrthogonal.groupSchemeCongr_hom_comp_inclusion`: inside `GLₙ`, the isomorphism
  `O(q) ≅ O(q')` is conjugation by `P`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.1, for the orthogonal group scheme of a
  quadratic space over a ring, in every characteristic.
-/

public section

open CategoryTheory Matrix WithConv
open QuadraticForm (baseChangeForm baseChangeForm_map_mulVec)

namespace TauCeti.QuadraticOrthogonal

universe u v

variable {R : Type u} [CommRing R] {n : ℕ} {q q' : QuadraticForm R (Fin n → R)}

/-! ### Points -/

/-- Conjugating by an isometry over `A` carries `O(q)(A)` onto `O(q')(A)`. -/
theorem conj_mem_pointsSubgroup_iff {A : Type*} [CommRing A] [Algebra R A] (Q : GL (Fin n) A)
    (hQ : ∀ x, baseChangeForm q' A ((Q : Matrix (Fin n) (Fin n) A) *ᵥ x) = baseChangeForm q A x)
    (g : GL (Fin n) A) :
    Q * g * Q⁻¹ ∈ pointsSubgroup R n q' A ↔ g ∈ pointsSubgroup R n q A := by
  simp only [mem_pointsSubgroup_iff, Units.val_mul]
  refine ⟨fun h x ↦ ?_, fun h y ↦ ?_⟩
  · have hx : ((Q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ
        ((Q : Matrix (Fin n) (Fin n) A) *ᵥ x) = x := by
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    have := h ((Q : Matrix (Fin n) (Fin n) A) *ᵥ x)
    rwa [← mulVec_mulVec, ← mulVec_mulVec, hx, hQ, hQ] at this
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hQ, h]
    conv_rhs => rw [← one_mulVec y, ← Units.mul_inv Q, ← mulVec_mulVec, hQ]

/-! ### The defining Hopf ideals -/

/-- **Conjugation pulls the Hopf ideal of `O(q)` back to that of `O(q')`.** If `q'(Q x) = q(x)`
for every `x`, the coordinate automorphism of conjugation by `Q` on `GLₙ` pulls the defining Hopf
ideal of `O(q)` back to that of `O(q')`: a matrix `g` preserves `q'` exactly when `Q⁻¹ g Q`
preserves `q`. -/
theorem definingHopfIdeal_comapOfSurjective_conjCoordinateIso (Q : GL (Fin n) R)
    (hQ : ∀ x, q' ((Q : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    (definingHopfIdeal R n q).comapOfSurjective (GeneralLinear.conjCoordinateIso Q).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso Q).hom).2 =
      definingHopfIdeal R n q' := by
  rw [GeneralLinear.comapOfSurjective_conjCoordinateIso_eq_conjugate]
  refine (HopfIdeal.eq_conjugate_of_forall_mem_iff _ fun A x => ?_).symm
  obtain ⟨A⟩ := A
  refine (mem_definingPointsSubgroup_iff R n _ A _).trans
    (Iff.trans ?_ (mem_definingPointsSubgroup_iff R n _ A x).symm)
  rw [map_mul, map_mul, map_inv, GeneralLinear.pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply,
    Algebra.toRingHom_ofId]
  refine conj_mem_pointsSubgroup_iff _ (fun y ↦ ?_) _
  have hq : ((GeneralLinearGroup.map (algebraMap R A) Q : GL (Fin n) A) :
      Matrix (Fin n) (Fin n) A) = (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R A) := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [hq]
  exact baseChangeForm_map_mulVec hQ A y

/-- If `q'(P x) = q(x)` for every `x`, conjugation by `P⁻¹` pulls the defining Hopf ideal of
`O(q')` back to that of `O(q)`. -/
theorem definingHopfIdeal_comapOfSurjective_conjCoordinateIso_inv (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    (definingHopfIdeal R n q').comapOfSurjective (GeneralLinear.conjCoordinateIso P⁻¹).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso P⁻¹).hom).2 =
      definingHopfIdeal R n q :=
  definingHopfIdeal_comapOfSurjective_conjCoordinateIso P⁻¹ fun x ↦ by
    rw [← hP, mulVec_mulVec, Units.mul_inv, one_mulVec]

/-! ### The isomorphism `O(q) ≅ O(q')` -/

/-- **Isometric forms have isomorphic coordinate Hopf algebras.** If `q'(P x) = q(x)` for every
`x`, the coordinate Hopf algebra of `O(q)` is isomorphic to that of `O(q')`, through conjugation
by `P⁻¹` on `GLₙ`. -/
noncomputable def coordinateHopfAlgebraCongr (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    coordinateHopfAlgebra R n q ≅ coordinateHopfAlgebra R n q' :=
  CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso P⁻¹)
    (definingHopfIdeal R n q') (definingHopfIdeal_comapOfSurjective_conjCoordinateIso_inv P hP)

/-- The coordinate isomorphism of isometric forms is the quotient isomorphism induced by
conjugation by `P⁻¹` on `GLₙ`. -/
theorem coordinateHopfAlgebraCongr_def (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    coordinateHopfAlgebraCongr P hP =
      CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso P⁻¹)
        (definingHopfIdeal R n q')
        (definingHopfIdeal_comapOfSurjective_conjCoordinateIso_inv P hP) :=
  (rfl)

/-- The coordinate isomorphism of isometric forms is induced by conjugation by `P⁻¹` on the
coordinates of `GLₙ`. -/
theorem mkQuotient_comp_coordinateHopfAlgebraCongr_hom (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n q) ≫
        (coordinateHopfAlgebraCongr P hP).hom =
      (GeneralLinear.conjCoordinateIso P⁻¹).hom ≫
        CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n q') := by
  rw [coordinateHopfAlgebraCongr, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom]

/-- The inverse coordinate isomorphism of isometric forms is induced by conjugation by `P` on the
coordinates of `GLₙ`. -/
theorem mkQuotient_comp_coordinateHopfAlgebraCongr_inv (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n q') ≫ (coordinateHopfAlgebraCongr P hP).inv =
      (GeneralLinear.conjCoordinateIso P).hom ≫
        CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n q) := by
  rw [Iso.comp_inv_eq, Category.assoc, mkQuotient_comp_coordinateHopfAlgebraCongr_hom,
    GeneralLinear.conjCoordinateIso_inv, Iso.symm_hom, Iso.hom_inv_id_assoc]

variable (A : Type v) [CommRing A] [Algebra R A]

/-- **On points, the coordinate isomorphism of isometric forms is conjugation by `P⁻¹`.**
Precomposing with `coordinateHopfAlgebraCongr P hP` sends an `A`-valued point of `O(q')` with
matrix `g` to the point of `O(q)` with matrix `P⁻¹ g P`. -/
theorem pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q') (CommAlgCat.of R A)) :
    (pointsMulEquiv R n q A ((CommHopfAlgCat.Hom.mapPointsFunctor
        (coordinateHopfAlgebraCongr P hP).hom).app (CommAlgCat.of R A) f) : GL (Fin n) A) =
      GeneralLinearGroup.map (algebraMap R A) P⁻¹ * (pointsMulEquiv R n q' A f : GL (Fin n) A) *
        (GeneralLinearGroup.map (algebraMap R A) P⁻¹)⁻¹ := by
  rw [← pointsMulEquiv_coe]
  refine (pointsMulEquiv_coe R n q A _).symm.trans ?_
  rw [← CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp _ _ _
      (mkQuotient_comp_coordinateHopfAlgebraCongr_hom P hP),
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply, CommHopfAlgCat.quotientPointsHom]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_conjCoordinateIso P⁻¹ _ _

/-- **On points, the inverse coordinate isomorphism of isometric forms is conjugation by `P`.**
Precomposing with the inverse of `coordinateHopfAlgebraCongr P hP` sends an `A`-valued point of
`O(q)` with matrix `g` to the point of `O(q')` with matrix `P g P⁻¹`. -/
theorem pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr_inv (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    (pointsMulEquiv R n q' A ((CommHopfAlgCat.Hom.mapPointsFunctor
        (coordinateHopfAlgebraCongr P hP).inv).app (CommAlgCat.of R A) f) : GL (Fin n) A) =
      GeneralLinearGroup.map (algebraMap R A) P * (pointsMulEquiv R n q A f : GL (Fin n) A) *
        (GeneralLinearGroup.map (algebraMap R A) P)⁻¹ := by
  rw [← pointsMulEquiv_coe]
  refine (pointsMulEquiv_coe R n q' A _).symm.trans ?_
  rw [← CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp _ _ _
      (mkQuotient_comp_coordinateHopfAlgebraCongr_inv P hP),
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply, CommHopfAlgCat.quotientPointsHom]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_conjCoordinateIso P _ _

/-- **Isometric forms have isomorphic orthogonal group schemes.** If `q'(P x) = q(x)` for every
`x`, conjugation by `P` is an isomorphism `O(q) ≅ O(q')` of group schemes over `R`. -/
noncomputable def groupSchemeCongr (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    groupScheme R n q ≅ groupScheme R n q' :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso (coordinateHopfAlgebraCongr P hP).op.symm

/-- The isomorphism of orthogonal group schemes is the spectrum of the coordinate isomorphism. -/
theorem groupSchemeCongr_def (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    groupSchemeCongr P hP = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
      (coordinateHopfAlgebraCongr P hP).op.symm :=
  (rfl)

/-- **The isomorphism of orthogonal group schemes is conjugation by `P` on `GLₙ`.** Followed by
the inclusion into `GLₙ`, the isomorphism `groupSchemeCongr P hP` is the inclusion of `O(q)`
followed by the automorphism of `GLₙ` induced by `GeneralLinear.conjCoordinateIso P`. -/
theorem groupSchemeCongr_hom_comp_inclusion (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x) :
    (groupSchemeCongr P hP).hom ≫ inclusion R n q' =
      inclusion R n q ≫ eqToHom (GeneralLinear.groupScheme_def R n) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (GeneralLinear.conjCoordinateIso P).hom.op ≫
        eqToHom (GeneralLinear.groupScheme_def R n).symm := by
  rw [groupSchemeCongr_def, inclusion_def, inclusion_def, GeneralLinear.hopfIdealInclusion_def,
    GeneralLinear.hopfIdealInclusion_def, CommHopfAlgCat.quotientSpecι_def,
    CommHopfAlgCat.quotientSpecι_def]
  simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv, ← Functor.map_comp_assoc, ← op_comp,
    mkQuotient_comp_coordinateHopfAlgebraCongr_inv]
  simp only [op_comp, Functor.map_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

end TauCeti.QuadraticOrthogonal
