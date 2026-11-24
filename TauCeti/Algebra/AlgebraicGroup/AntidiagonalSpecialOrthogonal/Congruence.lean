/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose

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
(`TauCeti.ConstantForm.sup_specialLinear_comapOfSurjective_conjCoordinateIso`). Hence

`SO_l^J ≅ SO_l`

as group schemes over `R`, where `SO_l` is `TauCeti.SpecialOrthogonal.groupScheme`, the special
orthogonal group of the identity form
(`TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraIsoSpecialOrthogonal`, an
isomorphism of coordinate Hopf algebras), and `SO_l^J` is smooth
over `R` (`TauCeti.AntidiagonalSpecialOrthogonal.smooth_coordinateHopfAlgebra`).

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10, for groups preserving a constant bilinear form.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti

universe u

/-! ### Congruence of the determinant-one subgroup schemes -/

namespace ConstantForm

variable {R : Type u} [CommRing R] {n : ℕ}

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
      MulEquiv.apply_symm_apply, Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm,
      ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]

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

end ConstantForm

namespace AntidiagonalSpecialOrthogonal

/-! ### The congruence matrix -/

section CongrMatrix

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) (i : R)

/-- The **congruence matrix** `P = a · 1 + b · J_l`, with `a = (1 - i) / 2` and `b = (1 + i) / 2`.
For `i² = -1` it satisfies `P J_l Pᵀ = 1`. -/
noncomputable def congrMatrix : Matrix (Fin l) (Fin l) R :=
  (⅟2 * (1 - i)) • (1 : Matrix (Fin l) (Fin l) R) + (⅟2 * (1 + i)) • formMatrix R l

variable {l i}

/-- The congruence matrix is symmetric. -/
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

end CongrMatrix

/-! ### The isomorphism with the special orthogonal group of the identity form -/

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) {i : R}

/-- **`SO_l^J` and `SO_l` have isomorphic coordinate Hopf algebras** over a ring containing `1/2`
and a square root `i` of `-1`, through conjugation by the inverse of the congruence matrix on
`GL_l`. -/
noncomputable def coordinateHopfAlgebraIsoSpecialOrthogonal (hi : i * i = -1) :
    coordinateHopfAlgebra R l ≅ SpecialOrthogonal.coordinateHopfAlgebra R l :=
  CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹)
    (SpecialOrthogonal.definingHopfIdeal R l)
    (by
      rw [SpecialOrthogonal.definingHopfIdeal_def, definingHopfIdeal_def]
      exact ConstantForm.sup_specialLinear_comapOfSurjective_conjCoordinateIso_inv (congrUnit l hi)
        (by rw [coe_congrUnit]; exact congrMatrix_mul_formMatrix_mul_transpose hi))

/-- The isomorphism of coordinate Hopf algebras is induced by conjugation by the inverse of the
congruence matrix on the coordinates of `GL_l`. -/
theorem coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_hom (hi : i * i = -1) :
    coordinateMap R l ≫ (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).hom =
      (GeneralLinear.conjCoordinateIso (congrUnit l hi)⁻¹).hom ≫
        SpecialOrthogonal.coordinateMap R l := by
  rw [coordinateMap_def, SpecialOrthogonal.coordinateMap_def,
    coordinateHopfAlgebraIsoSpecialOrthogonal,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom]

/-- **`SO_l^J` is smooth** over a ring containing `1/2` and a square root of `-1`. -/
theorem smooth_coordinateHopfAlgebra (hi : i * i = -1) :
    Algebra.Smooth R (coordinateHopfAlgebra R l) :=
  Algebra.Smooth.of_equiv
    (CommHopfAlgCat.ofIso (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).symm).toAlgEquiv

end AntidiagonalSpecialOrthogonal

end TauCeti
