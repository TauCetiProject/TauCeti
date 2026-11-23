/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import Mathlib.Algebra.Polynomial.Laurent
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Scaling the native projective line

Multiplying the first homogeneous coordinate by the Laurent parameter defines a family
`[x₀ : x₁] ↦ [t x₀ : x₁]` on the native projective line `Proj (Sym R²)`.
The family restricts to the identity at `t = 1`, fixes `[0 : 1]`, and carries `[1 : 1]`
onto the schematically dense torus chart. These identities hold as scheme morphisms over
an arbitrary commutative ring, including nonreduced rings.

The construction transports `Proj.symmetricAlgebraMapIso` through the existing
`projectiveLine.isPullback_baseChangeProjection`. Polynomial chart points supply a common
coordinate calculation for all three identities. The torus is geometrically integral
because every field base change is a nonempty open subscheme of the corresponding
projective line.

## Main declarations

* `projectiveLine.scaling`: the Laurent-parameter scaling family.
* `projectiveLine.scaling_at_unit`, `scaling_fixes_infinity`, `scaling_at_one`: its three slices.
* `projectiveLine.torusInclusion`: the schematically dense open torus chart.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.2 (projective spectra and affine charts).
* The Stacks Project, Section 27.8 (the projective spectrum of a graded ring).
-/

public section

open CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.projectiveLine

open _root_.AlgebraicGeometry Polynomial

universe u

section Diagonal

variable (R : Type u) [CommSemiring R]

/-- The diagonal linear equivalence multiplying the first coordinate by a unit. -/
noncomputable def diagonal (a : Rˣ) : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) :=
  LinearEquiv.piCongrRight fun i ↦
    LinearEquiv.smulOfUnit (M := R) (if i = 0 then a else 1)

/-- The diagonal equivalence acts by the prescribed scalar on each coordinate. -/
@[simp]
lemma diagonal_apply (a : Rˣ) (m : Fin 2 → R) (i : Fin 2) :
    diagonal R a m i = (if i = 0 then (a : R) else 1) * m i := by
  fin_cases i <;> simp [diagonal, LinearEquiv.smulOfUnit, Units.smul_def]

end Diagonal

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "𝒜" => homogeneousSubmodule R (Fin 2 → R)
local notation "ℬ" => homogeneousSubmodule S (Fin 2 → S)

/-- Scaling the first homogeneous coordinate of the native projective line by a unit. -/
noncomputable def scalingBy (a : Rˣ) : projectiveLine R ≅ projectiveLine R :=
  Proj.symmetricAlgebraMapIso R (diagonal R a)

/-- A unit scaling preserves the structure morphism to the coefficient scheme. -/
@[reassoc, simp]
lemma scalingBy_hom_over (a : Rˣ) :
    (scalingBy R a).hom ≫ (projectiveLine R ↘ Spec (.of R)) =
      (projectiveLine R ↘ Spec (.of R)) := by
  simpa only [scalingBy, SymmetricAlgebra.over_eq_projToSpec] using
    Proj.symmetricAlgebraMapIso_hom_projToSpec R (diagonal R a)

section Coordinates

variable {A : Type u} [CommSemiring A]

/-- Scaling the first coordinate multiplies the normalized coordinate in the second chart. -/
lemma pointCoordinates_comp_diagonal (f : R →+* A) (a : A) (t : Rˣ) :
    (pointCoordinates R f 1 a).comp
        (_root_.SymmetricAlgebra.gradedMap R (diagonal R t).toLinearMap).toRingHom =
      pointCoordinates R f 1 (f t * a) := by
  have hcoord (b : A) : pointCoordinates R f 1 b (coord R 0) = b := by
    simpa using pointCoordinates_coord_rev R f 1 b
  ext r
  · simp
  · simp only [RingHom.comp_apply, _root_.SymmetricAlgebra.gradedMap_toRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, _root_.SymmetricAlgebra.map_apply_ι]
    rw [ι_eq_smul_coord_add_smul_coord R 1, ι_eq_smul_coord_add_smul_coord R 1]
    suffices f (r 1) + f ((t : R) * r 0) * a =
        f (r 1) + f (r 0) * (f t * a) by
      simpa [Algebra.smul_def, hcoord] using this
    simp only [map_mul]
    ring

end Coordinates

variable {A : Type u} [CommRing A]

/-- A unit scaling multiplies the affine coordinate in the second polynomial chart. -/
lemma polynomialPoint_comp_scalingBy (f : R →+* A) (a : A) (t : Rˣ) :
    polynomialPoint R f 1 a ≫ (scalingBy R t).hom =
      polynomialPoint R f 1 (f t * a) := by
  rw [scalingBy, Proj.symmetricAlgebraMapIso_hom, polynomialPoint_eq_fromGlobalSections,
    Proj.fromOfGlobalSections_map]
  simp only [RingHom.comp_assoc, pointCoordinates_comp_diagonal]
  exact (polynomialPoint_eq_fromGlobalSections R _ 1 _).symm

/-- The Laurent-parameter scheme for scaling the projective line. -/
noncomputable abbrev scalingBase := Spec (.of (LaurentPolynomial R))

/-- The structure morphism of the Laurent-parameter scheme. -/
noncomputable abbrev scalingToBase : scalingBase R ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R)))

/-- The family `[x₀ : x₁] ↦ [t x₀ : x₁]` on the native projective line. -/
noncomputable def scaling :
    pullback (projectiveLine R ↘ Spec (.of R)) (scalingToBase R) ⟶ projectiveLine R :=
  (isPullback_baseChangeProjection R (LaurentPolynomial R)).isoPullback.inv ≫
    (scalingBy (LaurentPolynomial R) ((LaurentPolynomial.isUnit_T (R := R) 1).unit)).hom ≫
      baseChangeProjection R (LaurentPolynomial R)

/-- The scaling family is a morphism over the coefficient ring. -/
@[reassoc]
lemma scaling_over :
    scaling R ≫ (projectiveLine R ↘ Spec (.of R)) =
      pullback.fst (projectiveLine R ↘ Spec (.of R)) (scalingToBase R) ≫
        (projectiveLine R ↘ Spec (.of R)) := by
  have h := isPullback_baseChangeProjection R (LaurentPolynomial R)
  rw [scaling, Category.assoc, Category.assoc, h.w,
    ← Category.assoc (scalingBy (LaurentPolynomial R) _).hom,
    scalingBy_hom_over, ← Category.assoc, h.isoPullback_inv_snd, pullback.condition]

/-- On the second polynomial chart, the scaling family multiplies the coordinate by the Laurent
parameter. -/
lemma polynomialPoint_scaling (f : LaurentPolynomial R →+* A) (a : A) :
    pullback.lift
        (polynomialPoint R (f.comp (algebraMap R (LaurentPolynomial R))) 1 a)
        (Spec.map (CommRingCat.ofHom f))
        (by rw [polynomialPoint_over, ← Spec.map_comp]; rfl) ≫ scaling R =
      polynomialPoint R (f.comp (algebraMap R (LaurentPolynomial R))) 1
        (f (LaurentPolynomial.T 1) * a) := by
  let h := isPullback_baseChangeProjection R (LaurentPolynomial R)
  have hlift : pullback.lift
        (polynomialPoint R (f.comp (algebraMap R (LaurentPolynomial R))) 1 a)
        (Spec.map (CommRingCat.ofHom f))
        (by rw [polynomialPoint_over, ← Spec.map_comp]; rfl) ≫ h.isoPullback.inv =
      polynomialPoint (LaurentPolynomial R) f 1 a := by
    rw [← cancel_mono h.isoPullback.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc, h.isoPullback_hom_fst, pullback.lift_fst,
        polynomialPoint_comp_baseChangeProjection]
    · simp only [Category.assoc, h.isoPullback_hom_snd, pullback.lift_snd,
        polynomialPoint_over]
  rw [scaling, ← Category.assoc, ← Category.assoc, hlift,
    polynomialPoint_comp_scalingBy, polynomialPoint_comp_baseChangeProjection,
    IsUnit.unit_spec]

/-- The parameter section `t = 1`. -/
noncomputable def scalingUnit : Spec (.of R) ⟶ scalingBase R :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1))

/-- Evaluation at one is a section of the parameter projection. -/
@[reassoc (attr := simp)]
lemma scalingUnit_over : scalingUnit R ≫ scalingToBase R = 𝟙 _ := by
  have h : CommRingCat.ofHom (algebraMap R (LaurentPolynomial R)) ≫
      CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1) = 𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    ext r
    simp [LaurentPolynomial.eval₂_C]
  simpa only [scalingUnit, scalingToBase, Spec.map_comp, Spec.map_id] using congrArg Spec.map h

/-- The open torus chart `Spec R[t,t⁻¹] ⟶ ℙ¹_R` in the second polynomial chart. -/
noncomputable def torusInclusion : scalingBase R ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫ polynomialChartι R 1

/-- The torus inclusion is a morphism over the coefficient ring. -/
@[reassoc (attr := simp)]
lemma torusInclusion_over :
    torusInclusion R ≫ (projectiveLine R ↘ Spec (.of R)) = scalingToBase R := by
  rw [torusInclusion, Category.assoc, polynomialChartι_over, ← Spec.map_comp]
  congr 1
  ext r
  simp [← LaurentPolynomial.C_eq_algebraMap]

instance : IsOpenImmersion (torusInclusion R) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))) :=
    IsOpenImmersion.of_isLocalization Polynomial.X
  dsimp [torusInclusion]
  infer_instance

instance : IsSchemeTheoreticallyDominant (torusInclusion R) := by
  have : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))) :=
    (isSchemeTheoreticallyDominant_SpecMap_iff _).2 Polynomial.toLaurent_injective
  dsimp [torusInclusion]
  infer_instance

/-- The torus inclusion has normalized coordinate equal to the Laurent parameter. -/
lemma torusInclusion_eq_polynomialPoint :
    torusInclusion R = polynomialPoint R (algebraMap R (LaurentPolynomial R)) 1
      (LaurentPolynomial.T 1) := by
  rw [torusInclusion, polynomialPoint_def]
  congr 2
  ext <;> simp [← LaurentPolynomial.C_eq_algebraMap]

/-- Scaling fixes the native infinity section `[0 : 1]`. -/
lemma scaling_fixes_infinity :
    pullback.lift (scalingToBase R ≫ infinitySection R) (𝟙 _)
        (by rw [Category.assoc, infinitySection_over, Category.comp_id, Category.id_comp]) ≫
      scaling R = scalingToBase R ≫ infinitySection R := by
  have h := polynomialPoint_scaling R (RingHom.id (LaurentPolynomial R)) 0
  have hc : (RingHom.id (LaurentPolynomial R)).comp (algebraMap R (LaurentPolynomial R)) =
      algebraMap R (LaurentPolynomial R) := rfl
  have hp : polynomialPoint R (algebraMap R (LaurentPolynomial R)) 1 0 =
      scalingToBase R ≫ infinitySection R := by
    rw [← polynomialPoint_zero, SpecMap_polynomialPoint]
    simp
  simpa only [hc, hp, map_zero, mul_zero, CommRingCat.ofHom_id, Spec.map_id] using h

/-- The orbit of `[1 : 1]` is the torus inclusion. -/
lemma scaling_at_one :
    pullback.lift
        (scalingToBase R ≫ polynomialPoint R (RingHom.id R) 1 1) (𝟙 _)
        (by rw [Category.assoc, polynomialPoint_over, CommRingCat.ofHom_id,
          Spec.map_id, Category.comp_id, Category.id_comp]) ≫ scaling R =
      torusInclusion R := by
  have h := polynomialPoint_scaling R (RingHom.id (LaurentPolynomial R)) 1
  rw [torusInclusion_eq_polynomialPoint]
  simpa only [RingHom.id_comp, mul_one, RingHom.id_apply, CommRingCat.ofHom_id,
    Spec.map_id, scalingToBase, SpecMap_polynomialPoint, RingHom.comp_id, map_one] using h

/-- The parameter projection is surjective because evaluation at one is a section. -/
instance scalingToBase_surjective : Surjective (scalingToBase R) := by
  have : Surjective (scalingUnit R ≫ scalingToBase R) := by
    rw [scalingUnit_over]
    infer_instance
  exact Surjective.of_comp (scalingUnit R) _

/-- The parameter scheme is locally of finite type over its coefficient ring. -/
instance scalingToBase_locallyOfFiniteType :
    LocallyOfFiniteType (scalingToBase R) := by
  rw [← torusInclusion_over]
  infer_instance

/-- Every field fibre of the parameter scheme is integral. -/
instance scalingToBase_geometricallyIntegral :
    GeometricallyIntegral (scalingToBase R) where
  geometrically_isIntegral := by
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    let b : Spec (.of K) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have : Nonempty (pullback (scalingToBase R) b : Scheme) := by
      obtain ⟨x, -⟩ := (pullback.snd (scalingToBase R) b).surjective
        (default : Spec (.of K))
      exact ⟨x⟩
    have : IsIntegral (pullback (projectiveLine R ↘ Spec (.of R)) b) :=
      GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd _ _)
    exact isIntegral_of_isOpenImmersion
      (pullback.map (scalingToBase R) b
        (projectiveLine R ↘ Spec (.of R)) b (torusInclusion R) (𝟙 _) (𝟙 _)
        (by simp) (by simp))

/-- The scaling family at parameter one is the identity. -/
lemma scaling_at_unit :
    pullback.lift (𝟙 (projectiveLine R))
        ((projectiveLine R ↘ Spec (.of R)) ≫ scalingUnit R)
        (by simp) ≫ scaling R = 𝟙 _ := by
  apply ext_of_isSchemeTheoreticallyDominant (polynomialChartι R 1)
    (projectiveLine R ↘ Spec (.of R))
  · simp [scaling_over]
  · let e := LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)
    let f : LaurentPolynomial R →+* R[X] := Polynomial.C.comp e
    have hf : f.comp (algebraMap R (LaurentPolynomial R)) = Polynomial.C := by
      ext r
      simp [f, e, LaurentPolynomial.eval₂_C]
    have hlift : polynomialChartι R 1 ≫
          pullback.lift (f := projectiveLine R ↘ Spec (.of R))
            (g := scalingToBase R) (𝟙 (projectiveLine R))
            ((projectiveLine R ↘ Spec (.of R)) ≫ scalingUnit R) (by simp) =
        pullback.lift (f := projectiveLine R ↘ Spec (.of R))
          (g := scalingToBase R) (polynomialPoint R (f.comp (algebraMap R (LaurentPolynomial R)))
          1 Polynomial.X) (Spec.map (CommRingCat.ofHom f))
          (by rw [polynomialPoint_over, ← Spec.map_comp]; rfl) := by
      apply pullback.hom_ext
      · simp [hf]
      · simp only [Category.assoc, pullback.lift_snd, scalingUnit]
        rw [← Category.assoc, polynomialChartι_over, ← Spec.map_comp]
        rfl
    rw [← Category.assoc, hlift, polynomialPoint_scaling, hf]
    simp [f, e, LaurentPolynomial.eval₂_T]

end TauCeti.AlgebraicGeometry.projectiveLine
