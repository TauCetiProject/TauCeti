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
(`TauCeti.QuadraticOrthogonal.baseChangeForm_map_mulVec`). This uses nothing about `2`, so it holds
in characteristic two, where `q` is not determined by its polar form.

In coordinates, the coordinate automorphism `GeneralLinear.conjCoordinateIso Q` of conjugation by
`Q` pulls the defining Hopf ideal of `O(q')` back to that of `O(q)` when `q'(Q x) = q(x)`
(`TauCeti.QuadraticOrthogonal.definingHopfIdeal_comapOfSurjective_conjCoordinateIso`), as in
`TauCeti.ConstantForm.groupSchemeCongr` for constant matrices.

## Main declarations

* `TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraCongr`: for an isometry `P` from `q` to `q'`,
  the coordinate Hopf algebras of `O(q)` and `O(q')` are isomorphic, through conjugation by `P⁻¹`
  on `GLₙ`.
* `TauCeti.QuadraticOrthogonal.groupSchemeCongr`: the isomorphism `O(q) ≅ O(q')`.
* `TauCeti.QuadraticOrthogonal.pointsMulEquiv_coordinateHopfAlgebraCongr`: on points, the
  isomorphism is `g ↦ P g P⁻¹`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.1, for the orthogonal group scheme of a
  quadratic space over a ring, in every characteristic.
-/

public section

open CategoryTheory Matrix WithConv
open QuadraticForm (coefficientMatrix baseChangeForm baseChangeForm_apply)

namespace TauCeti.QuadraticOrthogonal

universe u v

variable {R : Type u} [CommRing R] {n : ℕ} {q q' : QuadraticForm R (Fin n → R)}

/-! ### Isometries over every algebra -/

/-- **An isometry over `R` is an isometry over every `R`-algebra.** If `q'(P x) = q(x)` for every
`x ∈ Rⁿ`, then `q'_A(P x) = q_A(x)` for every `x ∈ Aⁿ`, with `P` read in `A`. -/
theorem baseChangeForm_map_mulVec {P : Matrix (Fin n) (Fin n) R} (hP : ∀ x, q' (P *ᵥ x) = q x)
    (A : Type*) [CommRing A] [Algebra R A] (x : Fin n → A) :
    baseChangeForm q' A (P.map (algebraMap R A) *ᵥ x) = baseChangeForm q A x := by
  set M := coefficientMatrix q (Pi.basisFun R (Fin n))
  set M' := coefficientMatrix q' (Pi.basisFun R (Fin n))
  have hR : IsAltMod ⊥ (Pᵀ * M' * P - M) := by
    rw [isAltMod_bot_iff]
    intro y
    have h1 := hP y
    rw [← QuadraticForm.baseChangeForm_self q', ← QuadraticForm.baseChangeForm_self q,
      baseChangeForm_apply, baseChangeForm_apply] at h1
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1
    rw [sub_mulVec, dotProduct_sub, dotProduct_transpose_mul_mul_mulVec, h1, sub_self]
  have hA := (isAltMod_bot_iff _).mp
    (hR.map (algebraMap R A) (by rw [Ideal.map_bot])) x
  rw [Matrix.map_sub _ (map_sub (algebraMap R A)), Matrix.map_mul, Matrix.map_mul, transpose_map,
    sub_mulVec, dotProduct_sub, dotProduct_transpose_mul_mul_mulVec, sub_eq_zero] at hA
  rw [baseChangeForm_apply, baseChangeForm_apply]
  exact hA

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

variable (A : Type v) [CommRing A] [Algebra R A]

/-- Membership in the subgroup of points cut out by the defining Hopf ideal of `O(q)`. -/
theorem mem_quotientPointsSubgroup_iff
    (x : HopfAlgebra.points (R := R) (H := GeneralLinear.coordinateHopfAlgebra R n)
      (CommAlgCat.of R A)) :
    x ∈ CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n q) (CommAlgCat.of R A) ↔
      GeneralLinear.pointsMulEquiv n x ∈ pointsSubgroup R n q A := by
  rw [← hopfIdealPointsSubgroup_definingHopfIdeal, GeneralLinear.mem_hopfIdealPointsSubgroup_iff,
    MulEquiv.symm_apply_apply, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]

/-! ### The defining Hopf ideals -/

/-- **Conjugation pulls the Hopf ideal of `O(q')` back to that of `O(q)`.** If `q'(Q x) = q(x)`
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
  refine (mem_quotientPointsSubgroup_iff A _).trans
    (Iff.trans ?_ (mem_quotientPointsSubgroup_iff A x).symm)
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

/-- **On points, the isomorphism `O(q) ≅ O(q')` is conjugation by `P`.** Precomposing with the
inverse coordinate isomorphism sends an `A`-valued point of `O(q)` with matrix `g` to the point of
`O(q')` with matrix `P g P⁻¹`. -/
theorem pointsMulEquiv_coordinateHopfAlgebraCongr (P : GL (Fin n) R)
    (hP : ∀ x, q' ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    (pointsMulEquiv R n q' A ((CommHopfAlgCat.Hom.mapPointsFunctor
        (coordinateHopfAlgebraCongr P hP).inv).app (CommAlgCat.of R A) f) : GL (Fin n) A) =
      GeneralLinearGroup.map (algebraMap R A) P * (pointsMulEquiv R n q A f : GL (Fin n) A) *
        (GeneralLinearGroup.map (algebraMap R A) P)⁻¹ := by
  have hinv : CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n q') ≫ (coordinateHopfAlgebraCongr P hP).inv =
      (GeneralLinear.conjCoordinateIso P).hom ≫
        CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n q) := by
    rw [Iso.comp_inv_eq, Category.assoc, mkQuotient_comp_coordinateHopfAlgebraCongr_hom,
      GeneralLinear.conjCoordinateIso_inv, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have h1 := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n q'))
    (coordinateHopfAlgebraCongr P hP).inv (CommAlgCat.of R A) f
  rw [hinv, CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply] at h1
  refine (pointsMulEquiv_coe R n q' A _).symm.trans ?_
  refine (congrArg (GeneralLinear.pointsMulEquiv n) h1.symm).trans ?_
  refine (GeneralLinear.pointsMulEquiv_mapPointsFunctor_conjCoordinateIso P
    (CommAlgCat.of R A) _).trans ?_
  rw [← pointsMulEquiv_coe]
  rfl

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

end TauCeti.QuadraticOrthogonal
