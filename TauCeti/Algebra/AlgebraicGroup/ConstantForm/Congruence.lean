/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose

/-!
# Congruent constant forms give conjugate subgroup schemes

Let `C` and `C'` be constant `n × n` matrices over a commutative ring `R` that are congruent by
an invertible matrix `P`, that is `P C Pᵀ = C'`. If `M C Mᵀ = C`, then

```text
(P M P⁻¹) C' (P M P⁻¹)ᵀ = P M C Mᵀ Pᵀ = P C Pᵀ = C',
```

so conjugation by `P` carries the subgroup scheme `ConstantForm.groupScheme R n C` of `GLₙ`
preserving `C` isomorphically onto the one preserving `C'`. In coordinates, the coordinate
automorphism `GeneralLinear.conjCoordinateIso Q` of conjugation by `Q` pulls the defining Hopf
ideal of `C'` back to the defining Hopf ideal of `Q C' Qᵀ`: the pullback is the conjugate
Hopf ideal (`TauCeti.HopfIdeal.conjugate`), recognized on points by
`TauCeti.HopfIdeal.eq_conjugate_of_forall_mem_iff`. The isomorphism of the quotients is the
induced one (`CommHopfAlgCat.quotientIsoOfComapEq`). Conjugation also preserves determinants, so
the same holds for the joins with the determinant kernel `SpecialLinear.definingHopfIdeal R n`,
which define the determinant-one subgroup schemes preserving `C` and `C'`.

## Main declarations

* `TauCeti.ConstantForm.definingHopfIdeal_comapOfSurjective_conjCoordinateIso`: conjugation by
  `Q` pulls the defining Hopf ideal of `C'` back to that of `Q C' Qᵀ`.
* `TauCeti.ConstantForm.sup_specialLinear_comapOfSurjective_conjCoordinateIso`: the same for the
  join with the determinant kernel.
* `TauCeti.ConstantForm.coordinateHopfAlgebraCongr`: for `P C Pᵀ = C'`, the coordinate Hopf
  algebras of the two subgroup schemes are isomorphic.
* `TauCeti.ConstantForm.groupSchemeCongr`: the corresponding isomorphism of group schemes.
* `TauCeti.ConstantForm.coordinateMap_comp_coordinateHopfAlgebraCongr_hom`: the isomorphism is
  induced by conjugation by `P` on `GLₙ`.
* `TauCeti.ConstantForm.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr`: on points,
  the isomorphism sends a matrix `M` preserving `C'` to `P⁻¹ M P`.
* `TauCeti.ConstantForm.groupSchemeCongr_hom_comp_inclusion`: inside `GLₙ`, the isomorphism of
  subgroup schemes is conjugation by `P`.
* `TauCeti.ConstantForm.smooth_of_congr`: smoothness of the coordinate algebra transfers along
  the isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10 and §3.5.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ConstantForm

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- **Conjugation pulls a constant-form Hopf ideal back to the congruent one.** The coordinate
automorphism of conjugation by `Q` on `GLₙ` pulls the defining Hopf ideal of `C` back to the
defining Hopf ideal of `Q C Qᵀ`: a point `M` satisfies `M (Q C Qᵀ) Mᵀ = Q C Qᵀ` exactly when
`Q⁻¹ M Q` preserves `C`. -/
theorem definingHopfIdeal_comapOfSurjective_conjCoordinateIso
    (Q : GL (Fin n) R) (C : Matrix (Fin n) (Fin n) R) :
    (definingHopfIdeal R n C).comapOfSurjective (GeneralLinear.conjCoordinateIso Q).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso Q).hom).2 =
      definingHopfIdeal R n
        ((Q : Matrix (Fin n) (Fin n) R) * C * (Q : Matrix (Fin n) (Fin n) R)ᵀ) := by
  rw [GeneralLinear.comapOfSurjective_conjCoordinateIso_eq_conjugate]
  refine (HopfIdeal.eq_conjugate_of_forall_mem_iff _ fun A x => ?_).symm
  obtain ⟨A⟩ := A
  refine (mem_definingPointsSubgroup_iff R n _ _).trans
    (Iff.trans ?_ (mem_definingPointsSubgroup_iff R n C x).symm)
  rw [map_mul, map_mul, map_inv, GeneralLinear.pointsMulEquiv_mapValue,
    MulEquiv.apply_symm_apply, Algebra.toRingHom_ofId]
  set q := GeneralLinearGroup.map (algebraMap R A) Q
  have hq : (q : Matrix _ _ A) = (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R A) := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, ← hq,
    GeneralLinearGroup.conj_congruence_congruence]
  exact (GeneralLinearGroup.congruence_injective q).eq_iff

/-- Conjugation by `P⁻¹` pulls the defining Hopf ideal of `C' = P C Pᵀ` back to the defining Hopf
ideal of `C`. -/
theorem definingHopfIdeal_comapOfSurjective_conjCoordinateIso_inv (P : GL (Fin n) R)
    {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    (definingHopfIdeal R n C').comapOfSurjective (GeneralLinear.conjCoordinateIso P⁻¹).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso P⁻¹).hom).2 =
      definingHopfIdeal R n C := by
  rw [definingHopfIdeal_comapOfSurjective_conjCoordinateIso, ← hP,
    GeneralLinearGroup.inv_congruence_congruence]

/-- **Conjugation pulls a determinant-one constant-form Hopf ideal back to the congruent one.** The
coordinate automorphism of conjugation by `Q` on `GLₙ` pulls the join of the constant-form Hopf
ideal of `C` and the determinant kernel back to the corresponding join for `Q C Qᵀ`. -/
theorem sup_specialLinear_comapOfSurjective_conjCoordinateIso (Q : GL (Fin n) R)
    (C : Matrix (Fin n) (Fin n) R) :
    (definingHopfIdeal R n C ⊔ SpecialLinear.definingHopfIdeal R n).comapOfSurjective
        (GeneralLinear.conjCoordinateIso Q).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso Q).hom).2 =
      definingHopfIdeal R n
          ((Q : Matrix (Fin n) (Fin n) R) * C * (Q : Matrix (Fin n) (Fin n) R)ᵀ) ⊔
        SpecialLinear.definingHopfIdeal R n := by
  have hC := definingHopfIdeal_comapOfSurjective_conjCoordinateIso Q C
  rw [GeneralLinear.comapOfSurjective_conjCoordinateIso_eq_conjugate] at hC ⊢
  refine (HopfIdeal.eq_conjugate_of_forall_mem_iff _ fun A x => ?_).symm
  simp only [CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf]
  refine and_congr ?_ ?_
  · rw [← hC]
    exact CommHopfAlgCat.pointConjugation_mem_conjugate_iff _ _ A x
  · obtain ⟨A⟩ := A
    refine (SpecialLinear.mem_definingPointsSubgroup_iff_det_eq_one R n _).trans
      (Iff.trans ?_ (SpecialLinear.mem_definingPointsSubgroup_iff_det_eq_one R n x).symm)
    rw [map_mul, map_mul, map_inv, GeneralLinear.pointsMulEquiv_mapValue,
      MulEquiv.apply_symm_apply, Units.val_mul, Units.val_mul, det_units_conj]

/-- Conjugation by `P⁻¹` pulls the determinant-one constant-form Hopf ideal of `C' = P C Pᵀ` back
to that of `C`. -/
theorem sup_specialLinear_comapOfSurjective_conjCoordinateIso_inv (P : GL (Fin n) R)
    {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    (definingHopfIdeal R n C' ⊔ SpecialLinear.definingHopfIdeal R n).comapOfSurjective
        (GeneralLinear.conjCoordinateIso P⁻¹).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso P⁻¹).hom).2 =
      definingHopfIdeal R n C ⊔ SpecialLinear.definingHopfIdeal R n := by
  rw [sup_specialLinear_comapOfSurjective_conjCoordinateIso, ← hP,
    GeneralLinearGroup.inv_congruence_congruence]

/-- **Congruent constant forms have isomorphic coordinate Hopf algebras.** If `P C Pᵀ = C'`, the
coordinate Hopf algebra of the subgroup scheme preserving `C` is isomorphic to that of the
subgroup scheme preserving `C'`, through conjugation by `P⁻¹` on `GLₙ`. -/
noncomputable def coordinateHopfAlgebraCongr (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    coordinateHopfAlgebra R n C ≅ coordinateHopfAlgebra R n C' :=
  CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso P⁻¹)
    (definingHopfIdeal R n C')
    (definingHopfIdeal_comapOfSurjective_conjCoordinateIso_inv P hP)

/-- The coordinate isomorphism of congruent forms is the quotient isomorphism induced by
conjugation by `P⁻¹` on `GLₙ`. -/
theorem coordinateHopfAlgebraCongr_def (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    coordinateHopfAlgebraCongr P hP =
      CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso P⁻¹)
        (definingHopfIdeal R n C')
        (definingHopfIdeal_comapOfSurjective_conjCoordinateIso_inv P hP) :=
  (rfl)

/-- The coordinate isomorphism of congruent forms is induced by conjugation by `P⁻¹` on the
coordinates of `GLₙ`: on points, it sends a matrix `M` preserving `C'` to `P⁻¹ M P`. -/
theorem coordinateMap_comp_coordinateHopfAlgebraCongr_hom (P : GL (Fin n) R)
    {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    coordinateMap R n C ≫ (coordinateHopfAlgebraCongr P hP).hom =
      (GeneralLinear.conjCoordinateIso P⁻¹).hom ≫ coordinateMap R n C' := by
  rw [coordinateMap_def, coordinateMap_def, coordinateHopfAlgebraCongr,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom]

/-- The inverse coordinate isomorphism of congruent forms is induced by conjugation by `P` on the
coordinates of `GLₙ`. -/
theorem coordinateMap_comp_coordinateHopfAlgebraCongr_inv (P : GL (Fin n) R)
    {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    coordinateMap R n C' ≫ (coordinateHopfAlgebraCongr P hP).inv =
      (GeneralLinear.conjCoordinateIso P).hom ≫ coordinateMap R n C := by
  rw [Iso.comp_inv_eq, Category.assoc, coordinateMap_comp_coordinateHopfAlgebraCongr_hom,
    GeneralLinear.conjCoordinateIso_inv, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- **On points, the coordinate isomorphism of congruent forms is conjugation by `P⁻¹`.**
Precomposing with `coordinateHopfAlgebraCongr P hP` sends an `A`-valued point of the subgroup
scheme preserving `C'`, with ambient matrix `M`, to the point of the subgroup scheme preserving
`C` with ambient matrix `P⁻¹ M P`. -/
theorem pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr (P : GL (Fin n) R)
    {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C')
    (A : CommAlgCat.{v} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n C') A) :
    GeneralLinear.pointsMulEquiv n
        ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R n C)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateHopfAlgebraCongr P hP).hom).app A f)) =
      GeneralLinearGroup.map (algebraMap R A) P⁻¹ *
          GeneralLinear.pointsMulEquiv n
            ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R n C')).app A f) *
        (GeneralLinearGroup.map (algebraMap R A) P⁻¹)⁻¹ := by
  rw [← CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    coordinateMap_comp_coordinateHopfAlgebraCongr_hom,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_conjCoordinateIso P⁻¹ A _

/-- **Smoothness transfers along congruence.** If `P C Pᵀ = C'` and the coordinate algebra of the
subgroup scheme preserving `C'` is smooth, so is that of the subgroup scheme preserving `C`. -/
theorem smooth_of_congr (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C')
    [Algebra.Smooth R (coordinateHopfAlgebra R n C')] :
    Algebra.Smooth R (coordinateHopfAlgebra R n C) :=
  Algebra.Smooth.of_equiv (CommHopfAlgCat.ofIso (coordinateHopfAlgebraCongr P hP).symm).toAlgEquiv

/-- **Congruent constant forms have isomorphic subgroup schemes.** If `P C Pᵀ = C'`, conjugation
by `P` is an isomorphism from the subgroup scheme of `GLₙ` preserving `C` onto the subgroup scheme
preserving `C'`. -/
noncomputable def groupSchemeCongr (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    groupScheme R n C ≅ groupScheme R n C' :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso (coordinateHopfAlgebraCongr P hP).op.symm

/-- The isomorphism of subgroup schemes is the spectrum of the coordinate isomorphism. -/
theorem groupSchemeCongr_def (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    groupSchemeCongr P hP = (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
      (coordinateHopfAlgebraCongr P hP).op.symm :=
  (rfl)

/-- **The isomorphism of subgroup schemes is conjugation by `P` on `GLₙ`.** Followed by the
inclusion into `GLₙ`, the isomorphism `groupSchemeCongr P hP` is the inclusion of the subgroup
scheme preserving `C` followed by the automorphism of `GLₙ` induced by
`GeneralLinear.conjCoordinateIso P`. -/
theorem groupSchemeCongr_hom_comp_inclusion (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    (groupSchemeCongr P hP).hom ≫ inclusion R n C' =
      inclusion R n C ≫ eqToHom (GeneralLinear.groupScheme_def R n) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (GeneralLinear.conjCoordinateIso P).hom.op ≫
        eqToHom (GeneralLinear.groupScheme_def R n).symm := by
  rw [groupSchemeCongr_def, inclusion_eq_eqToHom_comp_hopfSpec_map,
    inclusion_eq_eqToHom_comp_hopfSpec_map]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Functor.mapIso_hom, Iso.symm_hom,
    Iso.op_inv, ← Functor.map_comp_assoc, ← op_comp,
    coordinateMap_comp_coordinateHopfAlgebraCongr_inv]
  simp only [op_comp, Functor.map_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

end TauCeti.ConstantForm
