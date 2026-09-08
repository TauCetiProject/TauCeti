/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Geometry of the standard Borel subgroup of `SL₂`

The upper-triangular determinant-one subgroup of `SL₂` is smooth, geometrically connected, and
geometrically solvable. Its coordinate algebra has the explicit presentation

```text
R[T, T⁻¹][X],
```

where `T` is the upper-left diagonal entry and `X` is the upper-right entry. This presentation
also makes geometric connectedness transparent: after extending a field, the coordinate ring
remains a polynomial ring over a Laurent polynomial domain.

Smoothness follows from the infinitesimal lifting property for upper-triangular determinant-one
matrices across nilpotent quotients.

These geometric properties combine with maximality among solvable closed subgroups to identify
the standard subgroup as a Borel subgroup.

## Main declarations

* `TauCeti.SpecialLinear.Borel.coordinateAlgEquiv`: the presentation of the coordinate algebra as
  `R[T, T⁻¹][X]`.
* `TauCeti.SpecialLinear.Borel.smoothCommHopfAlgProperty_coordinateHopfAlgebra`: smoothness.
* `TauCeti.SpecialLinear.Borel.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  geometric connectedness.
* `TauCeti.SpecialLinear.Borel.
    geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra`: solvability of
  geometric points.
* `TauCeti.SpecialLinear.Borel.isBorel_definingHopfIdeal`: the standard subgroup is Borel.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 21.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.SpecialLinear.Borel

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

/-! ## Polynomial-Laurent presentation -/

private abbrev presentationRing := Polynomial (LaurentPolynomial R)

/-- The tautological diagonal parameter in the polynomial-Laurent presentation. -/
private def presentationUnit : (presentationRing R)ˣ :=
  Units.map Polynomial.C.toMonoidHom (MultiplicativeGroup.genericUnit R)

@[simp]
private theorem presentationUnit_val :
    (presentationUnit R : presentationRing R) =
      Polynomial.C (LaurentPolynomial.T 1) := by
  simp [presentationUnit]

@[simp]
private theorem presentationUnit_inv :
    (((presentationUnit R)⁻¹ : (presentationRing R)ˣ) : presentationRing R) =
      Polynomial.C (LaurentPolynomial.T (-1)) := by
  simp [presentationUnit]

/-- The tautological upper-triangular determinant-one matrix over the presentation ring. -/
private def presentationPoint : SL2Borel (presentationRing R) :=
  SL2Borel.mk (presentationUnit R) Polynomial.X

/-- Evaluate the standard Borel coordinate algebra at its polynomial-Laurent tautological
matrix. -/
private def coordinateToPresentation :
    coordinateHopfAlgebra R →ₐ[R] presentationRing R :=
  ((pointsMulEquiv (R := R) (A := presentationRing R)).symm
    (presentationPoint R)).ofConv

/-- The tautological point of the standard Borel in its own coordinate algebra. -/
noncomputable def tautologicalPoint : SL2Borel (coordinateHopfAlgebra R) :=
  pointsMulEquiv (R := R) (A := coordinateHopfAlgebra R)
    (toConv (AlgHom.id R (coordinateHopfAlgebra R)))

/-- The upper-left diagonal coordinate of the standard `SL₂` Borel, bundled as a unit. -/
noncomputable def diagonalUnit : (coordinateHopfAlgebra R)ˣ :=
  SL2Borel.diag (tautologicalPoint R)

theorem diagonalUnit_val :
    (diagonalUnit R : coordinateHopfAlgebra R) =
      (tautologicalPoint R : Matrix (Fin 2) (Fin 2) (coordinateHopfAlgebra R)) 0 0 := by
  exact SL2Borel.diag_val (tautologicalPoint R)

/-- The upper-right coordinate of the standard `SL₂` Borel. -/
noncomputable def upperRightCoordinate : coordinateHopfAlgebra R :=
  SL2Borel.upperRight (tautologicalPoint R)

theorem upperRightCoordinate_eq :
    upperRightCoordinate R =
      (tautologicalPoint R : Matrix (Fin 2) (Fin 2) (coordinateHopfAlgebra R)) 0 1 :=
  SL2Borel.upperRight_apply (tautologicalPoint R)

/-- Interpret Laurent coefficients through the tautological diagonal unit. -/
private def presentationCoefficientToCoordinate :
    LaurentPolynomial R →ₐ[R] coordinateHopfAlgebra R :=
  ((MultiplicativeGroup.pointsMulEquiv
    (R := R) (A := coordinateHopfAlgebra R)).symm (diagonalUnit R)).ofConv

/-- Evaluate the polynomial coordinate at the tautological upper-right matrix entry. -/
private def presentationToCoordinate :
    presentationRing R →ₐ[R] coordinateHopfAlgebra R :=
  Polynomial.eval₂AlgHom (presentationCoefficientToCoordinate R)
    (upperRightCoordinate R)
    fun _ ↦ mul_comm _ _

@[simp]
private theorem presentationToCoordinate_X :
    presentationToCoordinate R Polynomial.X = upperRightCoordinate R := by
  exact Polynomial.eval₂_X _ _

private theorem map_tautologicalPoint :
    SL2Borel.map (coordinateToPresentation R).toRingHom (tautologicalPoint R) =
      presentationPoint R := by
  unfold tautologicalPoint
  rw [← pointsMulEquiv_mapValue (R := R) (A := coordinateHopfAlgebra R)
    (B := presentationRing R)]
  simp only [AlgHom.comp_id, coordinateToPresentation,
    WithConv.toConv_ofConv, MulEquiv.apply_symm_apply]

private theorem map_presentationPoint :
    SL2Borel.map (presentationToCoordinate R).toRingHom (presentationPoint R) =
      tautologicalPoint R := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [presentationPoint, presentationToCoordinate, presentationCoefficientToCoordinate,
      presentationUnit_val, MultiplicativeGroup.point_T, diagonalUnit_val]
  · rw [SL2Borel.map_apply, presentationPoint, SL2Borel.coe_mk]
    simpa [AlgHom.coe_toRingHom, upperRightCoordinate_eq] using
      presentationToCoordinate_X R
  · simp [presentationPoint, SL2Borel.apply_one_zero]
  · have hdet := (tautologicalPoint R).1.2
    rw [Matrix.det_fin_two, SL2Borel.apply_one_zero, mul_zero, sub_zero] at hdet
    have hunit :
        ((tautologicalPoint R : Matrix (Fin 2) (Fin 2) (coordinateHopfAlgebra R)) 0 0) *
          ((tautologicalPoint R : Matrix (Fin 2) (Fin 2) (coordinateHopfAlgebra R)) 1 1) = 1 :=
      hdet
    have hunit' :
        (diagonalUnit R : coordinateHopfAlgebra R) *
          ((tautologicalPoint R : Matrix (Fin 2) (Fin 2) (coordinateHopfAlgebra R)) 1 1) = 1 := by
      simpa only [diagonalUnit_val] using hunit
    have hinv := Units.inv_eq_of_mul_eq_one_right hunit'
    simpa [presentationPoint, presentationToCoordinate, presentationCoefficientToCoordinate,
      presentationUnit_val, MultiplicativeGroup.point_T] using hinv

private theorem map_tautologicalUnit :
    Units.map (coordinateToPresentation R).toMonoidHom (diagonalUnit R) =
      presentationUnit R := by
  apply Units.ext
  have h := congrArg
    (fun g : SL2Borel (presentationRing R) ↦
      (g : Matrix (Fin 2) (Fin 2) (presentationRing R)) 0 0)
    (map_tautologicalPoint R)
  rw [SL2Borel.map_apply, presentationPoint, SL2Borel.coe_mk] at h
  simpa [diagonalUnit_val, presentationUnit_val] using h

private theorem unitOfPoint_CAlgHom :
    MultiplicativeGroup.unitOfPoint
        (Polynomial.CAlgHom : LaurentPolynomial R →ₐ[R] presentationRing R) =
      presentationUnit R := by
  apply Units.ext
  simp [MultiplicativeGroup.unitOfPoint_val, presentationUnit_val]

private theorem presentationToCoordinate_comp_coordinateToPresentation :
    (presentationToCoordinate R).comp (coordinateToPresentation R) =
      AlgHom.id R (coordinateHopfAlgebra R) := by
  apply toConv_injective
  apply (pointsMulEquiv (R := R) (A := coordinateHopfAlgebra R)).injective
  rw [pointsMulEquiv_mapValue (R := R) (A := presentationRing R)
    (B := coordinateHopfAlgebra R)]
  simpa only [coordinateToPresentation, WithConv.toConv_ofConv,
    MulEquiv.apply_symm_apply, tautologicalPoint] using map_presentationPoint R

private theorem coordinateToPresentation_comp_presentationToCoordinate :
    (coordinateToPresentation R).comp (presentationToCoordinate R) =
      AlgHom.id R (presentationRing R) := by
  apply Polynomial.algHom_ext'
  · rw [AlgHom.comp_assoc]
    have hcoeff :
        (presentationToCoordinate R).comp Polynomial.CAlgHom =
          presentationCoefficientToCoordinate R := by
      apply DFunLike.ext _ _
      intro x
      change Polynomial.eval₂ (presentationCoefficientToCoordinate R).toRingHom
        (upperRightCoordinate R) (Polynomial.C x) = _
      simp
    rw [hcoeff]
    apply (MultiplicativeGroup.pointEquiv
      (R := R) (A := presentationRing R)).injective
    rw [MultiplicativeGroup.pointEquiv_comp]
    simpa only [presentationCoefficientToCoordinate,
      MultiplicativeGroup.pointsMulEquiv_symm_apply, WithConv.ofConv_toConv,
      MultiplicativeGroup.pointEquiv_apply, MultiplicativeGroup.unitOfPoint_point,
      AlgHom.id_comp, unitOfPoint_CAlgHom] using map_tautologicalUnit R
  · have h := congrArg
      (fun g : SL2Borel (presentationRing R) ↦
        (g : Matrix (Fin 2) (Fin 2) (presentationRing R)) 0 1)
      (map_tautologicalPoint R)
    have hX : presentationToCoordinate R Polynomial.X =
        (tautologicalPoint R : Matrix (Fin 2) (Fin 2) (coordinateHopfAlgebra R)) 0 1 := by
      rw [presentationToCoordinate_X, upperRightCoordinate_eq]
    rw [AlgHom.comp_apply, hX, AlgHom.id_apply]
    rw [SL2Borel.map_apply, presentationPoint, SL2Borel.coe_mk] at h
    exact h

/-- **Polynomial-Laurent coordinates on the standard `SL₂` Borel.** Its coordinate algebra is
`R[T, T⁻¹][X]`: `T` records the upper-left diagonal unit and `X` records the free upper-right
entry. -/
noncomputable def coordinateAlgEquiv :
    coordinateHopfAlgebra R ≃ₐ[R] Polynomial (LaurentPolynomial R) :=
  AlgEquiv.ofAlgHom (coordinateToPresentation R) (presentationToCoordinate R)
    (coordinateToPresentation_comp_presentationToCoordinate R)
    (presentationToCoordinate_comp_coordinateToPresentation R)

/-- The coordinate equivalence sends the diagonal unit to the Laurent generator. -/
@[simp]
theorem coordinateAlgEquiv_diagonalUnit :
    coordinateAlgEquiv R (diagonalUnit R : coordinateHopfAlgebra R) =
      Polynomial.C (LaurentPolynomial.T 1) := by
  have h := congrArg
    (fun g : SL2Borel (presentationRing R) ↦
      (g : Matrix (Fin 2) (Fin 2) (presentationRing R)) 0 0)
    (map_tautologicalPoint R)
  rw [SL2Borel.map_apply, presentationPoint, SL2Borel.coe_mk] at h
  rw [coordinateAlgEquiv, AlgEquiv.ofAlgHom_apply]
  simpa [AlgHom.coe_toRingHom, diagonalUnit_val, presentationUnit_val] using h

/-- The coordinate equivalence sends the upper-right coordinate to the polynomial generator. -/
@[simp]
theorem coordinateAlgEquiv_upperRightCoordinate :
    coordinateAlgEquiv R (upperRightCoordinate R) = Polynomial.X := by
  have h := congrArg
    (fun g : SL2Borel (presentationRing R) ↦
      (g : Matrix (Fin 2) (Fin 2) (presentationRing R)) 0 1)
    (map_tautologicalPoint R)
  rw [SL2Borel.map_apply, presentationPoint, SL2Borel.coe_mk] at h
  rw [coordinateAlgEquiv, AlgEquiv.ofAlgHom_apply]
  simpa [AlgHom.coe_toRingHom, upperRightCoordinate_eq] using h

/-- The inverse coordinate equivalence sends the Laurent generator to the diagonal unit. -/
@[simp]
theorem coordinateAlgEquiv_symm_C_T :
    (coordinateAlgEquiv R).symm (Polynomial.C (LaurentPolynomial.T 1)) =
      (diagonalUnit R : coordinateHopfAlgebra R) := by
  apply (coordinateAlgEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, coordinateAlgEquiv_diagonalUnit]

/-- The inverse coordinate equivalence sends the polynomial generator to the upper-right
coordinate. -/
@[simp]
theorem coordinateAlgEquiv_symm_X :
    (coordinateAlgEquiv R).symm Polynomial.X = upperRightCoordinate R := by
  apply (coordinateAlgEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, coordinateAlgEquiv_upperRightCoordinate]

/-! ## Base change -/

private theorem coordinateHopfAlgebraBaseChangeIso_hom_lowerLeftCoordinate
    (K : Type max u v) [CommRing K] [Algebra R K] :
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K 2).hom.hom
        (1 ⊗ₜ[R] lowerLeftCoordinate R) = lowerLeftCoordinate K := by
  have hcomp := baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom R K 2
  have h := congrArg
    (fun f ↦ f.hom (1 ⊗ₜ[R] GeneralLinear.Borel.lowerLeftCoordinate R)) hcomp
  have hGL :
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K 2).hom
          (1 ⊗ₜ[R] GeneralLinear.Borel.lowerLeftCoordinate R) =
        GeneralLinear.Borel.lowerLeftCoordinate K := by
    rw [GeneralLinear.Borel.lowerLeftCoordinate_def,
      GeneralLinear.Borel.lowerLeftCoordinate_def]
    simpa using GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v}
      R K 2 1 (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply] at h
  rw [CommHopfAlgCat.baseChangeMap_apply_tmul, hGL] at h
  simpa only [lowerLeftCoordinate_def] using h

private theorem map_baseChangeHopfIdeal_definingHopfIdeal
    (K : Type max u v) [CommRing K] [Algebra R K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R)).map
        (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K 2).hom.hom =
      definingHopfIdeal K := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R) (definingHopfIdeal K)
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K 2)
    (definingHopfIdeal_toIdeal R) (definingHopfIdeal_toIdeal K) ?_
  simp only [Set.image_singleton]
  congr 1
  exact coordinateHopfAlgebraBaseChangeIso_hom_lowerLeftCoordinate R K

/-- Base change of the standard `SL₂` Borel coordinate Hopf algebra is canonically the same
coordinate Hopf algebra constructed over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso
    (K : Type max u v) [CommRing K] [Algebra R K] :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R) ≅
      coordinateHopfAlgebra K := by
  apply CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R) (definingHopfIdeal K)
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K 2)
  exact map_baseChangeHopfIdeal_definingHopfIdeal R K

/-- The Borel base-change isomorphism commutes with the quotient coordinate morphisms from
`O(SL₂)`. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom
    (K : Type max u v) [CommRing K] [Algebra R K] :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R) ≫
        (coordinateHopfAlgebraBaseChangeIso R K).hom =
      (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K 2).hom ≫ coordinateMap K := by
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R) (definingHopfIdeal K)
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K 2)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K)

private noncomputable def coordinateRingBaseChangeEquiv
    (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K] :
    coordinateHopfAlgebra k ⊗[k] K ≃+* Polynomial (LaurentPolynomial K) :=
  (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans
    ((CommHopfAlgCat.ofIso (coordinateHopfAlgebraBaseChangeIso k K)).toAlgEquiv.toRingEquiv.trans
      (coordinateAlgEquiv K).toRingEquiv)

/-- **The standard `SL₂` Borel coordinate Hopf algebra is geometrically connected.** After
every field extension its coordinate ring is a polynomial ring over a Laurent polynomial domain. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (coordinateRingBaseChangeEquiv k K)).connectedSpace_iff.mpr inferInstance

private instance instFormallySmoothCoordinateHopfAlgebra :
    Algebra.FormallySmooth R (coordinateHopfAlgebra R) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro A _ _ I hI f
  obtain ⟨g, hg⟩ := SL2Borel.map_quotient_mk_surjective_of_isNilpotent I ⟨2, hI⟩
    ((pointsMulEquiv (R := R) (A := A ⧸ I)) (toConv f))
  let lift : WithConv (coordinateHopfAlgebra R →ₐ[R] A) :=
    (pointsMulEquiv (R := R) (A := A)).symm g
  refine ⟨lift.ofConv, ?_⟩
  apply toConv_injective
  apply (pointsMulEquiv (R := R) (A := A ⧸ I)).injective
  rw [pointsMulEquiv_mapValue (R := R) (A := A) (B := A ⧸ I)]
  have hq : (Ideal.Quotient.mkₐ R I).toRingHom = Ideal.Quotient.mk I :=
    Ideal.Quotient.mkₐ_toRingHom (R₁ := R) I
  rw [hq]
  simpa only [lift, MulEquiv.apply_symm_apply] using hg

/-- The coordinate algebra of the upper-triangular determinant-one subgroup is smooth over every
commutative base ring. -/
instance instSmoothCoordinateHopfAlgebra : Algebra.Smooth R (coordinateHopfAlgebra R) := by
  have hfg : (definingHopfIdeal R).toIdeal.FG := by
    rw [definingHopfIdeal_toIdeal]
    exact Submodule.fg_span_singleton _
  let _ : Algebra.FinitePresentation R (coordinateHopfAlgebra R) :=
    Algebra.FinitePresentation.quotient hfg
  exact ⟨inferInstance, inferInstance⟩

/-- The standard Borel coordinate algebra is smooth over a field. -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  rw [smoothCommHopfAlgProperty_iff]
  infer_instance

/-- Every algebra-valued point group of the standard `SL₂` Borel is solvable. -/
theorem isSolvable_points (A : Type*) [CommRing A] [Algebra R A] :
    Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) (CommAlgCat.of R A)) := by
  let e := pointsMulEquiv (R := R) (A := A)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The standard `SL₂` Borel has a solvable group of geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact isSolvable_points k (AlgebraicClosure k)

/-! ## The Borel property -/

section Field

variable {k : Type u} [Field k]

private theorem isBorelOverAlgClosed_definingHopfIdeal [IsAlgClosed k] :
    HopfIdeal.IsBorelOverAlgClosed k
      ⟨SpecialLinear.coordinateHopfAlgebra k 2,
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
      (definingHopfIdeal k) := by
  rw [HopfIdeal.isBorelOverAlgClosed_iff]
  refine ⟨inferInstance, ?_⟩
  refine ⟨HopfIdeal.IsBorelCandidate.mk
    (smoothCommHopfAlgProperty_coordinateHopfAlgebra k)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k), ?_⟩
  intro I hI hIB
  exact definingHopfIdeal_le_of_le_of_smooth_of_geometricallySolvable
    I hIB hI.smooth hI.geometricallySolvable

/-- **The upper-triangular determinant-one subgroup of `SL₂` is a Borel subgroup over every
field.** Its base change to an algebraic closure is smooth, connected, solvable, and maximal
among closed subgroups with those properties. -/
theorem isBorel_definingHopfIdeal :
    HopfIdeal.IsBorel k (SpecialLinear.coordinateHopfAlgebra k 2) (definingHopfIdeal k) := by
  let K := AlgebraicClosure k
  let H : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨SpecialLinear.coordinateHopfAlgebra k 2,
      (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let L : FiniteTypeCommHopfAlgCat.{u, u} K :=
    ⟨SpecialLinear.coordinateHopfAlgebra K 2,
      (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let e : H' ≅ L := ObjectProperty.isoMk _
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso k K 2)
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal k)
  have hmap : I'.map (FiniteTypeCommHopfAlgCat.toBialgHom e.hom) = definingHopfIdeal K := by
    exact map_baseChangeHopfIdeal_definingHopfIdeal k K
  have hpull := HopfIdeal.IsBorelOverAlgClosed.of_map_eq e hmap
    (isBorelOverAlgClosed_definingHopfIdeal (k := K))
  exact (HopfIdeal.isBorel_iff_isBorelOverAlgClosed_baseChange
    k (SpecialLinear.coordinateHopfAlgebra k 2) (definingHopfIdeal k)).2 (by
      simpa only [K, H, H', I'] using hpull)

end Field

end

end TauCeti.SpecialLinear.Borel
