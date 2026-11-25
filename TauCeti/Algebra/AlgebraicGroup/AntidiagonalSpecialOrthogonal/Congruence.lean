/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Smooth

/-!
# `SO_l^J` and the special orthogonal group of the identity form

Let `R` be a commutative ring in which `2` is invertible and which contains a square root `i` of
`-1`. Then the antidiagonal form `J_l` (`TauCeti.AntidiagonalSpecialOrthogonal.formMatrix`) is
congruent to the identity form: with `a = (1 - i) / 2` and `b = (1 + i) / 2`, the symmetric matrix

`P = a · 1 + b · J_l`

satisfies `P J_l Pᵀ = (a + b J_l)² J_l = (a² + b²) J_l + 2ab = 1`, since `J_l² = 1`,
`a² = -i/2`, `b² = i/2` and `2ab = 1` (`TauCeti.AntidiagonalSpecialOrthogonal.congrMatrix`,
`TauCeti.AntidiagonalSpecialOrthogonal.congrMatrix_mul_formMatrix_mul_transpose`). On each pair
`(e_k, e_{l-1-k})` it is the block `[[a, b], [b, a]]`, and `1 = a + b` on the middle basis vector
for odd `l`.

Conjugation by `P` preserves determinants, so it identifies the determinant-one subgroup schemes
of the two congruent forms: for every congruence `P C Pᵀ = C'`, the coordinate automorphism of
conjugation pulls the join of the constant-form Hopf ideal of `C'` and the determinant kernel back
to the corresponding join for `C`
(`TauCeti.ConstantForm.sup_specialLinear_comapOfSurjective_conjCoordinateIso`). Hence the
coordinate Hopf algebras are isomorphic,

`O(SO_l^J) ≅ O(SO_l)`

as commutative Hopf algebras over `R`, where `O(SO_l)` is
`TauCeti.SpecialOrthogonal.coordinateHopfAlgebra`, the coordinate Hopf algebra of the special
orthogonal group of the identity form
(`TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraIsoSpecialOrthogonal`), and `SO_l^J`
is smooth over `R` (`TauCeti.AntidiagonalSpecialOrthogonal.smooth_coordinateHopfAlgebra`).
Taking spectra gives an isomorphism of group schemes `SO_l^J ≅ SO_l`
(`TauCeti.AntidiagonalSpecialOrthogonal.groupSchemeIsoSpecialOrthogonal`), which inside `GL_l` is
conjugation by `P`
(`TauCeti.AntidiagonalSpecialOrthogonal.groupSchemeIsoSpecialOrthogonal_hom_comp_inclusion`) and
on `A`-valued points sends `M ∈ SO_l(A)` to `P⁻¹ M P`.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10, for groups preserving a constant bilinear form.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti

universe u v

namespace AntidiagonalSpecialOrthogonal

/-! ### The congruence matrix -/

section CongrMatrix

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) (i : R)

/-- The **congruence matrix** `P = a · 1 + b · J_l`, with `a = (1 - i) / 2` and `b = (1 + i) / 2`.
For `i² = -1` it satisfies `P J_l Pᵀ = 1`. -/
noncomputable def congrMatrix : Matrix (Fin l) (Fin l) R :=
  (⅟2 * (1 - i)) • (1 : Matrix (Fin l) (Fin l) R) + (⅟2 * (1 + i)) • formMatrix R l

/-- The congruence matrix is `a · 1 + b · J_l`, with `a = (1 - i) / 2` and `b = (1 + i) / 2`. -/
theorem congrMatrix_def :
    congrMatrix l i =
      (⅟2 * (1 - i)) • (1 : Matrix (Fin l) (Fin l) R) + (⅟2 * (1 + i)) • formMatrix R l :=
  (rfl)

variable {l i}

/-- The entries of the congruence matrix: `a` on the diagonal and `b` on the antidiagonal (their
sum `1` at the middle entry for odd `l`). -/
@[simp]
theorem congrMatrix_apply (j k : Fin l) :
    congrMatrix l i j k =
      (if j = k then ⅟2 * (1 - i) else 0) + if k = Fin.rev j then ⅟2 * (1 + i) else 0 := by
  simp only [congrMatrix_def, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    formMatrix_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The congruence matrix is symmetric. -/
@[simp]
theorem transpose_congrMatrix : (congrMatrix l i)ᵀ = congrMatrix l i := by
  rw [congrMatrix, transpose_add, transpose_smul, transpose_smul, transpose_one,
    transpose_formMatrix]

/-- **The antidiagonal form is congruent to the identity form**: `P J_l Pᵀ = 1` when `i² = -1`. -/
theorem congrMatrix_mul_formMatrix_mul_transpose (hi : i * i = -1) :
    congrMatrix l i * formMatrix R l * (congrMatrix l i)ᵀ = 1 := by
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self 2
  rw [transpose_congrMatrix, congrMatrix]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    formMatrix_mul_self, smul_smul]
  -- Collect the coefficients of `J_l` and of `1`.
  have hJ : ⅟2 * (1 - i) * (⅟2 * (1 - i)) + ⅟2 * (1 + i) * (⅟2 * (1 + i)) = 0 := by
    linear_combination (⅟2 * ⅟2 * 2) * hi
  have h1 : ⅟2 * (1 - i) * (⅟2 * (1 + i)) + ⅟2 * (1 + i) * (⅟2 * (1 - i)) = 1 := by
    linear_combination (-(⅟2 * ⅟2 * 2)) * hi + (⅟2 * 2 + 1) * h2
  calc _ = (⅟2 * (1 - i) * (⅟2 * (1 - i)) + ⅟2 * (1 + i) * (⅟2 * (1 + i))) • formMatrix R l +
        (⅟2 * (1 - i) * (⅟2 * (1 + i)) + ⅟2 * (1 + i) * (⅟2 * (1 - i))) •
          (1 : Matrix (Fin l) (Fin l) R) := by
          module
    _ = 1 := by rw [hJ, h1, zero_smul, one_smul, zero_add]

variable (l) in
/-- The congruence matrix as an invertible matrix, with inverse `J_l Pᵀ`. -/
noncomputable def congrUnit (hi : i * i = -1) : GL (Fin l) R :=
  ⟨congrMatrix l i, formMatrix R l * (congrMatrix l i)ᵀ, by
    rw [← Matrix.mul_assoc, congrMatrix_mul_formMatrix_mul_transpose hi],
    mul_eq_one_comm.1 (by
      rw [← Matrix.mul_assoc, congrMatrix_mul_formMatrix_mul_transpose hi])⟩

@[simp]
theorem coe_congrUnit (hi : i * i = -1) :
    (congrUnit l hi : Matrix (Fin l) (Fin l) R) = congrMatrix l i :=
  (rfl)

/-- The inverse of the congruence unit is `J_l P`. -/
theorem coe_congrUnit_inv (hi : i * i = -1) :
    (↑(congrUnit l hi)⁻¹ : Matrix (Fin l) (Fin l) R) = formMatrix R l * congrMatrix l i := by
  rw [← transpose_congrMatrix (l := l) (i := i)]
  rfl

/-- The inverse of the congruence matrix is `J_l P`. -/
@[simp]
theorem inv_congrMatrix (hi : i * i = -1) :
    (congrMatrix l i)⁻¹ = formMatrix R l * congrMatrix l i := by
  rw [← coe_congrUnit hi, ← coe_units_inv, coe_congrUnit_inv, coe_congrUnit]

end CongrMatrix

/-! ### The isomorphism with the special orthogonal group of the identity form -/

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) {i : R}

/-- Conjugation by the inverse of the congruence matrix pulls the defining Hopf ideal of `SO_l` back
to that of `SO_l^J`. -/
theorem specialOrthogonal_comapOfSurjective_conjCoordinateIso_congrUnit_inv (hi : i * i = -1) :
    (SpecialOrthogonal.definingHopfIdeal R l).comapOfSurjective
        (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹).hom.hom
        (ConcreteCategory.bijective_of_isIso
          (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹).hom).2 =
      definingHopfIdeal R l := by
  rw [SpecialOrthogonal.definingHopfIdeal_def, definingHopfIdeal_def]
  exact ConstantForm.sup_specialLinear_comapOfSurjective_conjCoordinateIso_inv (congrUnit l hi)
    (by rw [coe_congrUnit]; exact congrMatrix_mul_formMatrix_mul_transpose hi)

/-- **`SO_l^J` and `SO_l` have isomorphic coordinate Hopf algebras** over a ring containing `1/2`
and a square root `i` of `-1`, through conjugation by the inverse of the congruence matrix on
`GL_l`. -/
noncomputable def coordinateHopfAlgebraIsoSpecialOrthogonal (hi : i * i = -1) :
    coordinateHopfAlgebra R l ≅ SpecialOrthogonal.coordinateHopfAlgebra R l :=
  CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹)
    (SpecialOrthogonal.definingHopfIdeal R l)
    (specialOrthogonal_comapOfSurjective_conjCoordinateIso_congrUnit_inv l hi)

/-- The isomorphism of coordinate Hopf algebras is the quotient isomorphism induced by conjugation
by the inverse of the congruence matrix on `GL_l`. -/
theorem coordinateHopfAlgebraIsoSpecialOrthogonal_def (hi : i * i = -1) :
    coordinateHopfAlgebraIsoSpecialOrthogonal l hi =
      CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹)
        (SpecialOrthogonal.definingHopfIdeal R l)
        (specialOrthogonal_comapOfSurjective_conjCoordinateIso_congrUnit_inv l hi) :=
  (rfl)

/-- The isomorphism of coordinate Hopf algebras is induced by conjugation by the inverse of the
congruence matrix on the coordinates of `GL_l`. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_hom (hi : i * i = -1) :
    coordinateMap R l ≫ (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).hom =
      (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹).hom ≫
        SpecialOrthogonal.coordinateMap R l := by
  rw [coordinateMap_def, SpecialOrthogonal.coordinateMap_def,
    coordinateHopfAlgebraIsoSpecialOrthogonal,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom]

/-- The inverse isomorphism of coordinate Hopf algebras is induced by conjugation by the congruence
matrix on the coordinates of `GL_l`. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_inv (hi : i * i = -1) :
    SpecialOrthogonal.coordinateMap R l ≫ (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).inv =
      (GeneralLinear.conjCoordinateIso (congrUnit l hi)).hom ≫ coordinateMap R l := by
  rw [Iso.comp_inv_eq, Category.assoc,
    coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_hom,
    GeneralLinear.conjCoordinateIso_inv, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- **`SO_l^J` is smooth** over a ring containing `1/2` and a square root of `-1`. -/
theorem smooth_coordinateHopfAlgebra (hi : i * i = -1) :
    Algebra.Smooth R (coordinateHopfAlgebra R l) :=
  Algebra.Smooth.of_equiv
    (CommHopfAlgCat.ofIso (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).symm).toAlgEquiv

/-! ### The isomorphism of group schemes -/

/-- **`SO_l^J` is isomorphic to `SO_l` as a group scheme** over a ring containing `1/2` and a
square root `i` of `-1`: the spectrum of the isomorphism of coordinate Hopf algebras, so that on
points it is conjugation by the congruence matrix `P`. -/
noncomputable def groupSchemeIsoSpecialOrthogonal (hi : i * i = -1) :
    groupScheme R l ≅ SpecialOrthogonal.groupScheme R l :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
      (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).op.symm ≪≫
    eqToIso (SpecialOrthogonal.groupScheme_def R l).symm

/-- The isomorphism of group schemes is the spectrum of the isomorphism of coordinate Hopf
algebras. -/
theorem groupSchemeIsoSpecialOrthogonal_def (hi : i * i = -1) :
    groupSchemeIsoSpecialOrthogonal l hi =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
          (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).op.symm ≪≫
        eqToIso (SpecialOrthogonal.groupScheme_def R l).symm :=
  (rfl)

/-- **Inside `GL_l`, the isomorphism `SO_l^J ≅ SO_l` is conjugation by the congruence matrix.**
Followed by the inclusion of `SO_l`, it is the inclusion of `SO_l^J` followed by the automorphism
of `GL_l` induced by `GeneralLinear.conjCoordinateIso P`. -/
theorem groupSchemeIsoSpecialOrthogonal_hom_comp_inclusion (hi : i * i = -1) :
    (groupSchemeIsoSpecialOrthogonal l hi).hom ≫ SpecialOrthogonal.inclusion R l =
      inclusion R l ≫ eqToHom (GeneralLinear.groupScheme_def R l) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (GeneralLinear.conjCoordinateIso (congrUnit l hi)).hom.op ≫
        eqToHom (GeneralLinear.groupScheme_def R l).symm := by
  rw [groupSchemeIsoSpecialOrthogonal_def, SpecialOrthogonal.inclusion_eq_eqToHom_comp_hopfSpec_map,
    inclusion_def, GeneralLinear.hopfIdealInclusion_def, CommHopfAlgCat.quotientSpecι_def,
    ← coordinateMap_def]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv, eqToIso.hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Functor.map_comp_assoc,
    ← op_comp, coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_inv]

/-- **On points, the isomorphism `SO_l^J ≅ SO_l` is conjugation by the congruence matrix.**
Precomposing with `coordinateHopfAlgebraIsoSpecialOrthogonal l hi` sends an `A`-valued point of
`SO_l` with ambient matrix `M` to the point of `SO_l^J` with ambient matrix `P⁻¹ M P`. -/
theorem pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraIsoSpecialOrthogonal_hom
    (hi : i * i = -1) (A : CommAlgCat.{v} R)
    (f : HopfAlgebra.points (R := R) (H := SpecialOrthogonal.coordinateHopfAlgebra R l) A) :
    GeneralLinear.pointsMulEquiv l
        ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R l)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor
            (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).hom).app A f)) =
      GeneralLinearGroup.map (algebraMap R A) (congrUnit l hi)⁻¹ *
          GeneralLinear.pointsMulEquiv l
            ((CommHopfAlgCat.Hom.mapPointsFunctor (SpecialOrthogonal.coordinateMap R l)).app A
              f) *
        (GeneralLinearGroup.map (algebraMap R A) (congrUnit l hi)⁻¹)⁻¹ := by
  rw [← CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_hom,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_conjCoordinateIso _ A _

end AntidiagonalSpecialOrthogonal

end TauCeti
