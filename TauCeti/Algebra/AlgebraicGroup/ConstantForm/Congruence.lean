/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

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
ideal of `C'` back to the defining Hopf ideal of `Q C' Qᵀ`, and the isomorphism of the
quotients is the induced one (`CommHopfAlgCat.quotientIsoOfComapEq`).

## Main declarations

* `TauCeti.ConstantForm.definingHopfIdeal_comapOfSurjective_conjCoordinateIso`: conjugation by
  `Q` pulls the defining Hopf ideal of `C'` back to that of `Q C' Qᵀ`.
* `TauCeti.ConstantForm.coordinateHopfAlgebraCongr`: for `P C Pᵀ = C'`, the coordinate Hopf
  algebras of the two subgroup schemes are isomorphic.
* `TauCeti.ConstantForm.groupSchemeCongr`: the corresponding isomorphism of group schemes.
* `TauCeti.ConstantForm.coordinateMap_comp_coordinateHopfAlgebraCongr_hom`: the isomorphism is
  induced by conjugation by `P` on `GLₙ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10 and §3.5.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ConstantForm

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

section Matrix

variable {A : Type*} [CommRing A] (q : GL (Fin n) A)

/-- `q⁻¹ (q Z) = Z` for an invertible matrix `q`. -/
private theorem inv_mul_mul_cancel (Z : Matrix (Fin n) (Fin n) A) :
    ((q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
      ((q : Matrix (Fin n) (Fin n) A) * Z) = Z := by
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- `qᵀ ((q⁻¹)ᵀ Z) = Z` for an invertible matrix `q`. -/
private theorem transpose_mul_transpose_inv_mul_cancel (Z : Matrix (Fin n) (Fin n) A) :
    (q : Matrix (Fin n) (Fin n) A)ᵀ *
      (((q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ * Z) = Z := by
  rw [← Matrix.mul_assoc, ← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    transpose_one, Matrix.one_mul]

/-- Conjugating `N` by `q` and congruence-transforming `C` by `q` transforms `N C Nᵀ` by `q`. -/
private theorem conj_mul_congr_mul_transpose (N : GL (Fin n) A) (C : Matrix (Fin n) (Fin n) A) :
    ((q * N * q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
        ((q : Matrix (Fin n) (Fin n) A) * C * (q : Matrix (Fin n) (Fin n) A)ᵀ) *
        ((q * N * q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ =
      (q : Matrix (Fin n) (Fin n) A) *
        ((N : Matrix (Fin n) (Fin n) A) * C * (N : Matrix (Fin n) (Fin n) A)ᵀ) *
        (q : Matrix (Fin n) (Fin n) A)ᵀ := by
  simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc, inv_mul_mul_cancel,
    transpose_mul_transpose_inv_mul_cancel]

/-- Congruence by `q⁻¹` undoes congruence by `q`. -/
private theorem inv_congr_congr (X : Matrix (Fin n) (Fin n) A) :
    ((q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
        ((q : Matrix (Fin n) (Fin n) A) * X * (q : Matrix (Fin n) (Fin n) A)ᵀ) *
        ((q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ = X := by
  have h : (q : Matrix (Fin n) (Fin n) A)ᵀ * ((q⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ =
      1 := by
    simpa using transpose_mul_transpose_inv_mul_cancel q 1
  simp only [Matrix.mul_assoc, inv_mul_mul_cancel, h, Matrix.mul_one]

variable {q} in
/-- Congruence by an invertible matrix is injective. -/
private theorem congr_cancel {X Y : Matrix (Fin n) (Fin n) A}
    (h : (q : Matrix (Fin n) (Fin n) A) * X * (q : Matrix (Fin n) (Fin n) A)ᵀ =
      (q : Matrix (Fin n) (Fin n) A) * Y * (q : Matrix (Fin n) (Fin n) A)ᵀ) : X = Y := by
  rw [← inv_congr_congr q X, h, inv_congr_congr]

end Matrix

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
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext f
  set e := GeneralLinear.conjCoordinateIso Q
  set g : HopfAlgebra.points (R := R) (H := GeneralLinear.coordinateHopfAlgebra R n) A :=
    BialgHom.mapDomain (A := A) e.inv.hom f
  have hfg : f = BialgHom.mapDomain (A := A) e.hom.hom g := by
    apply WithConv.ofConv_injective
    ext x
    rw [BialgHom.mapDomain_apply_apply, BialgHom.mapDomain_apply_apply,
      ← _root_.CommHopfAlgCat.comp_apply, Iso.hom_inv_id, _root_.CommHopfAlgCat.id_apply]
  have hM : GeneralLinear.pointsMulEquiv n f =
      GeneralLinearGroup.map (algebraMap R A) Q * GeneralLinear.pointsMulEquiv n g *
        (GeneralLinearGroup.map (algebraMap R A) Q)⁻¹ := by
    rw [hfg, BialgHom.mapDomain_apply]
    exact GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso Q A g
  rw [mem_definingPointsSubgroup_iff, hM]
  nth_rw 1 [hfg]
  refine (BialgHom.mapDomain_mem_quotientPointsSubgroup_comapOfSurjective_iff _ _ _ A g).trans ?_
  change g ∈ CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C) A ↔ _
  rw [mem_definingPointsSubgroup_iff]
  set q := GeneralLinearGroup.map (algebraMap R A) Q
  have hq : (q : Matrix _ _ A) = (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R A) :=
    rfl
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, ← hq, conj_mul_congr_mul_transpose]
  exact ⟨fun h ↦ by rw [h], congr_cancel⟩

/-- **Congruent constant forms have isomorphic coordinate Hopf algebras.** If `P C Pᵀ = C'`, the
coordinate Hopf algebra of the subgroup scheme preserving `C` is isomorphic to that of the
subgroup scheme preserving `C'`, through conjugation by `P⁻¹` on `GLₙ`. -/
noncomputable def coordinateHopfAlgebraCongr (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    coordinateHopfAlgebra R n C ≅ coordinateHopfAlgebra R n C' :=
  CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso P⁻¹)
    (definingHopfIdeal R n C') (by
      rw [definingHopfIdeal_comapOfSurjective_conjCoordinateIso, ← hP, inv_congr_congr])

/-- The coordinate isomorphism of congruent forms is the quotient isomorphism induced by
conjugation by `P⁻¹` on `GLₙ`. -/
theorem coordinateHopfAlgebraCongr_def (P : GL (Fin n) R) {C C' : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = C') :
    coordinateHopfAlgebraCongr P hP =
      CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.conjCoordinateIso P⁻¹)
        (definingHopfIdeal R n C') (by
          rw [definingHopfIdeal_comapOfSurjective_conjCoordinateIso, ← hP, inv_congr_congr]) :=
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

end TauCeti.ConstantForm
