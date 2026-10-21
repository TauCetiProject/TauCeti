/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Orbit
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Subdivision

/-!
# Explicit affine charts of the toric blow-up of the plane

The two maximal cones in the diagonal subdivision of the positive quadrant are unimodular
images of the quadrant. Transporting characters through these lattice shears identifies each
of their complex-point charts with `ℂ × ℂ`. In these coordinates the toric map to the plane is
`(u, v) ↦ (u, u * v)` on the upper cone and `(u, v) ↦ (u * v, v)` on the lower cone.
These formulas identify the exceptional fibre with a coordinate axis in each chart, including
points where a coordinate vanishes.

The toric map is proper because the two fans have the same support. Its fibre over the origin
is the boundary component of the diagonal ray, the closure of that ray’s orbit.

The chart homeomorphisms use `AffineSemigroupComplexPoint.comapHomeomorph`, its product
comparison, and the standard character coordinate of the affine ray. They use the existing
monomial topology on the charts of the subdivided fan.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4, the blow-up of the affine plane.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Multiplicative
open scoped ContDiff

namespace TauCeti.Toric

/-! ### The blow-up of the affine plane at the origin -/

/-- The analytic toric map from the blow-up of the affine plane at the origin, the star
subdivision of the affine-plane fan along the diagonal, to the affine plane is proper. -/
theorem isProperMap_analyticMap_affinePlaneBlowUpFan :
    IsProperMap (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
      isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan) :=
  affinePlaneBlowUpFan_isSubdivision.isProperMap_analyticMap isRegular_affinePlaneBlowUpFan
    isRegular_affinePlaneFan

/-- The exceptional fibre of the blow-up of the affine plane at the origin. The preimage of the
origin, the orbit of the positive quadrant, is the boundary component of the diagonal ray. -/
theorem preimage_analyticMap_analyticConeOrbit_affinePlaneBlowUpFan :
    affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap isRegular_affinePlaneBlowUpFan
        isRegular_affinePlaneFan ⁻¹'
      affinePlaneFan.analyticConeOrbit isRegular_affinePlaneFan
        (affineRayFan.prodCone affineRayFan affineRayFanMaxCone affineRayFanMaxCone) =
      affinePlaneBlowUpFan.analyticBoundaryComponent isRegular_affinePlaneBlowUpFan
        affinePlaneBlowUpDiagonalRay := by
  rw [FanHom.preimage_analyticMap_analyticConeOrbit, Fan.analyticBoundaryComponent_eq_iUnion]
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ici, exists_prop, ← Subtype.coe_le_coe,
    coe_toCone_affinePlaneBlowUpDiagonalRay]
  exact exists_congr fun σ ↦ and_congr_left fun _ ↦ leastCone_affinePlaneBlowUpFan_eq_iff σ.2

/-! ### Explicit affine charts -/

private abbrev PlaneLattice := (Fin 1 → ℤ) × (Fin 1 → ℤ)
private abbrev quadrant := affineRayCone.prod affineRayCone
private abbrev maxCone := affineRayFan.prodCone affineRayFan
  affineRayFanMaxCone affineRayFanMaxCone
private noncomputable abbrev rayGenerators :=
  (affineRayFan.analyticChartGenerators affineRayFanMaxCone).2

private noncomputable def blowUpShear (R : Type*) [CommRing R] (upper : Bool) :
    ((Fin 1 → R) × (Fin 1 → R)) ≃ₗ[R] (Fin 1 → R) × (Fin 1 → R) :=
  let e := LinearEquiv.skewProd (.refl R (Fin 1 → R)) (.refl R (Fin 1 → R)) LinearMap.id
  if upper then e else (LinearEquiv.prodComm R _ _).trans
    (e.trans (LinearEquiv.prodComm R _ _))

private abbrev blowUpCone (upper : Bool) :=
  if upper then affinePlaneBlowUpUpperCone else affinePlaneBlowUpLowerCone

private theorem blowUpShear_map_lattice (upper : Bool) (n : PlaneLattice) :
    blowUpShear ℝ upper
      ((((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1))) n) =
      (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1))) (blowUpShear ℤ upper n) := by
  cases upper <;> ext j <;> simp [blowUpShear]

private theorem map_quadrant_blowUpShear (upper : Bool) :
    PointedCone.map (blowUpShear ℝ upper).toLinearMap quadrant = blowUpCone upper := by
  cases upper
  · have hswap : PointedCone.map
        (LinearEquiv.prodComm ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)).toLinearMap quadrant = quadrant := by
      ext x
      rw [PointedCone.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy.2, hy.1⟩
      · intro hx
        exact ⟨x.swap, ⟨hx.2, hx.1⟩, rfl⟩
    simp only [blowUpShear, blowUpCone, Bool.false_eq_true, ↓reduceIte,
      LinearEquiv.coe_trans, ← PointedCone.map_map, hswap,
      ← affinePlaneBlowUpUpperCone_eq_map, ← affinePlaneBlowUpLowerCone_eq_map]
  · simpa only [blowUpShear, blowUpCone, ↓reduceIte] using
      affinePlaneBlowUpUpperCone_eq_map.symm

private noncomputable def blowUpSemigroupEquiv (upper : Bool) :
    dualSemigroup affinePlaneFan.lattice (blowUpCone upper) ≃+
      dualSemigroup affinePlaneFan.lattice quadrant :=
  dualSemigroupEquiv affinePlaneFan.lattice affinePlaneFan.lattice
    (blowUpShear ℤ upper).toAddEquiv (blowUpShear ℝ upper)
    (blowUpShear_map_lattice upper) (map_quadrant_blowUpShear upper)

private noncomputable abbrev blowUpFanCone (upper : Bool) : affinePlaneBlowUpFan.cones :=
  ⟨blowUpCone upper, by cases upper <;> simp [blowUpCone, PointedCone.IsFaceOf.refl]⟩

private noncomputable def blowUpPointHomeomorph (upper : Bool) :
    @Homeomorph
      (AffineSemigroupComplexPoint (dualSemigroup affinePlaneFan.lattice (blowUpCone upper)))
      (ℂ × ℂ) (affinePointTopology
        (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2) inferInstance := by
  letI := affinePointTopology rayGenerators
  letI := affinePointTopology (affinePlaneFan.analyticChartGenerators maxCone).2
  letI := affinePointTopology (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
  exact (AffineSemigroupComplexPoint.comapHomeomorph (blowUpSemigroupEquiv upper).symm
    (affinePlaneFan.analyticChartGenerators maxCone).2
    (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2).trans
      ((AffineSemigroupComplexPoint.prodHomeomorph
        (dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
          affineRayCone affineRayCone)
        (affinePlaneFan.analyticChartGenerators maxCone).2 rayGenerators rayGenerators).trans
        ((affineRayPointHomeomorph rayGenerators).prodCongr
          (affineRayPointHomeomorph rayGenerators)))

/-- The upper-cone affine chart of the diagonal subdivision, in coordinates corresponding to
its ordered lattice generators `(1, 1)` and `(0, 1)`. -/
noncomputable def affinePlaneBlowUpUpperPointHomeomorph :
    (affinePlaneBlowUpFan.analyticAffineChartDiagram).obj
      ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩ ≃ₜ ℂ × ℂ :=
  blowUpPointHomeomorph true

/-- The lower-cone affine chart of the diagonal subdivision, in coordinates corresponding to
its ordered lattice generators `(1, 0)` and `(1, 1)`. -/
noncomputable def affinePlaneBlowUpLowerPointHomeomorph :
    (affinePlaneBlowUpFan.analyticAffineChartDiagram).obj
      ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩ ≃ₜ ℂ × ℂ :=
  blowUpPointHomeomorph false

private theorem blowUpPointHomeomorph_symm_apply_single (upper : Bool) (z : ℂ × ℂ)
    (m : dualSemigroup affinePlaneFan.lattice (blowUpCone upper)) :
    letI := affinePointTopology rayGenerators
    letI := affinePointTopology (affinePlaneFan.analyticChartGenerators maxCone).2
    letI := affinePointTopology
      (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
    let x : AffineSemigroupComplexPoint (dualSemigroup affinePlaneFan.lattice (blowUpCone upper)) :=
      (blowUpPointHomeomorph upper).symm z
    x (MonoidAlgebra.single (ofAdd m) 1) =
      (affineRayPointHomeomorph rayGenerators).symm z.1
        (MonoidAlgebra.single (ofAdd ((dualSemigroupProdEquiv
          affineRayFan.lattice affineRayFan.lattice affineRayCone affineRayCone
          (blowUpSemigroupEquiv upper m)).1)) 1) *
      (affineRayPointHomeomorph rayGenerators).symm z.2
        (MonoidAlgebra.single (ofAdd ((dualSemigroupProdEquiv
          affineRayFan.lattice affineRayFan.lattice affineRayCone affineRayCone
          (blowUpSemigroupEquiv upper m)).2)) 1) := by
  dsimp only
  let _ := affinePointTopology rayGenerators
  let _ := affinePointTopology (affinePlaneFan.analyticChartGenerators maxCone).2
  let _ := affinePointTopology
    (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
  rw [blowUpPointHomeomorph]
  -- The diagram objects bundle the same monomial topologies used in the homeomorphisms.
  erw [Homeomorph.symm_trans_apply]
  erw [Homeomorph.symm_trans_apply
    (AffineSemigroupComplexPoint.prodHomeomorph
      (dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice affineRayCone affineRayCone)
      (affinePlaneFan.analyticChartGenerators maxCone).2 rayGenerators rayGenerators)
    ((affineRayPointHomeomorph rayGenerators).prodCongr
      (affineRayPointHomeomorph rayGenerators)) z,
    Homeomorph.prodCongr_symm, Homeomorph.coe_prodCongr, Prod.map_apply,
    AffineSemigroupComplexPoint.comapHomeomorph_symm,
    AffineSemigroupComplexPoint.coe_comapHomeomorph,
    AffineSemigroupComplexPoint.comap_apply_single,
    AffineSemigroupComplexPoint.coe_prodHomeomorph_symm,
    AffineSemigroupComplexPoint.prodEquiv_symm_apply_single]
  simp only [AddEquiv.symm_symm]
  -- Coercing the semigroup equivalence to an additive homomorphism preserves its function.
  rfl

private theorem blowUpPointHomeomorph_symm_apply_single_eq_pow (upper : Bool) (z : ℂ × ℂ)
    (m : dualSemigroup affinePlaneFan.lattice (blowUpCone upper)) :
    letI := affinePointTopology
      (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
    (blowUpPointHomeomorph upper).symm z (MonoidAlgebra.single (ofAdd m) 1) =
      z.1 ^ ((m : PlaneLattice →+ ℤ) (blowUpShear ℤ upper (1, 0))).toNat *
        z.2 ^ ((m : PlaneLattice →+ ℤ) (blowUpShear ℤ upper (0, 1))).toNat := by
  have h := blowUpPointHomeomorph_symm_apply_single upper z m
  simp only [affineRayPointHomeomorph_symm_apply_single_eq_pow,
    dualSemigroupProdEquiv_fst_apply, dualSemigroupProdEquiv_snd_apply,
    blowUpSemigroupEquiv, dualSemigroupEquiv_apply] at h
  exact h

/-- In upper-chart coordinates, a character monomial has exponents given by its values on
`(1, 1)` and `(0, 1)`, the two primitive generators of the cone. -/
@[simp]
theorem affinePlaneBlowUpUpperPointHomeomorph_symm_apply_single (z : ℂ × ℂ)
    (m : dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone) :
    let x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone) :=
      affinePlaneBlowUpUpperPointHomeomorph.symm z
    x (MonoidAlgebra.single (ofAdd m) 1) =
      z.1 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (1, 1)).toNat *
        z.2 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (0, 1)).toNat := by
  rw [affinePlaneBlowUpUpperPointHomeomorph]
  have h := blowUpPointHomeomorph_symm_apply_single_eq_pow true z m
  simp only [blowUpShear, ↓reduceIte, LinearEquiv.skewProd_apply, LinearEquiv.refl_apply,
    LinearMap.id_coe, id_eq, zero_add, add_zero] at h
  exact h

/-- In lower-chart coordinates, a character monomial has exponents given by its values on
`(1, 0)` and `(1, 1)`, the two primitive generators of the cone. -/
@[simp]
theorem affinePlaneBlowUpLowerPointHomeomorph_symm_apply_single (z : ℂ × ℂ)
    (m : dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone) :
    let x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone) :=
      affinePlaneBlowUpLowerPointHomeomorph.symm z
    x (MonoidAlgebra.single (ofAdd m) 1) =
      z.1 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (1, 0)).toNat *
        z.2 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (1, 1)).toNat := by
  rw [affinePlaneBlowUpLowerPointHomeomorph]
  have h := blowUpPointHomeomorph_symm_apply_single_eq_pow false z m
  simp only [blowUpShear, Bool.false_eq_true, ↓reduceIte, LinearEquiv.trans_apply,
    LinearEquiv.prodComm_apply, Prod.swap_prod_mk, LinearEquiv.skewProd_apply,
    LinearEquiv.refl_apply, LinearMap.id_coe, id_eq, add_zero, zero_add] at h
  exact h

private theorem blowUpPointHomeomorph_apply (upper : Bool)
    (x : AffineSemigroupComplexPoint (dualSemigroup affinePlaneFan.lattice (blowUpCone upper))) :
    letI := affinePointTopology
      (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
    blowUpPointHomeomorph upper x =
      (x (MonoidAlgebra.single (ofAdd ((blowUpSemigroupEquiv upper).symm
        ((dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
          affineRayCone affineRayCone).symm (affineRayCharacter, 0)))) 1),
        x (MonoidAlgebra.single (ofAdd ((blowUpSemigroupEquiv upper).symm
          ((dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
            affineRayCone affineRayCone).symm (0, affineRayCharacter)))) 1)) := by
  let _ := affinePointTopology rayGenerators
  let _ := affinePointTopology (affinePlaneFan.analyticChartGenerators maxCone).2
  let _ := affinePointTopology
    (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
  rw [blowUpPointHomeomorph]
  -- Read the transports before evaluating the two ray-coordinate monomials.
  erw [Homeomorph.trans_apply, Homeomorph.trans_apply,
    AffineSemigroupComplexPoint.coe_prodHomeomorph,
    AffineSemigroupComplexPoint.coe_comapHomeomorph,
    Homeomorph.coe_prodCongr, Prod.map_apply,
    affineRayPointHomeomorph_apply, affineRayPointHomeomorph_apply,
    AffineSemigroupComplexPoint.prodEquiv_fst_apply_single,
    AffineSemigroupComplexPoint.prodEquiv_snd_apply_single,
    AffineSemigroupComplexPoint.comap_apply_single,
    AffineSemigroupComplexPoint.comap_apply_single]
  -- The additive-hom coercion of the inverse semigroup equivalence has the same function.
  rfl

/-- The first upper-chart coordinate character, dual to the generator `(1, 1)`,
with lattice coefficients `(1, 0)`. -/
noncomputable def affinePlaneBlowUpUpperCharacter₁ :
    dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone :=
  (blowUpSemigroupEquiv true).symm
    ((dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
      affineRayCone affineRayCone).symm (affineRayCharacter, 0))

/-- The first upper-chart coordinate character evaluates the first lattice coordinate. -/
@[simp]
theorem affinePlaneBlowUpUpperCharacter₁_apply (n : (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    (affinePlaneBlowUpUpperCharacter₁ : _ →+ ℤ) n = n.1 0 := by
  simp [affinePlaneBlowUpUpperCharacter₁, blowUpSemigroupEquiv, blowUpShear]

/-- The second upper-chart coordinate character, dual to the generator `(0, 1)`,
with lattice coefficients `(−1, 1)`. -/
noncomputable def affinePlaneBlowUpUpperCharacter₂ :
    dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone :=
  (blowUpSemigroupEquiv true).symm
    ((dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
      affineRayCone affineRayCone).symm (0, affineRayCharacter))

/-- The second upper-chart coordinate character evaluates the difference of lattice coordinates. -/
@[simp]
theorem affinePlaneBlowUpUpperCharacter₂_apply (n : (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    (affinePlaneBlowUpUpperCharacter₂ : _ →+ ℤ) n = n.2 0 - n.1 0 := by
  simp [affinePlaneBlowUpUpperCharacter₂, blowUpSemigroupEquiv, blowUpShear]

/-- The first lower-chart coordinate character, dual to the generator `(1, 0)`,
with lattice coefficients `(1, −1)`. -/
noncomputable def affinePlaneBlowUpLowerCharacter₁ :
    dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone :=
  (blowUpSemigroupEquiv false).symm
    ((dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
      affineRayCone affineRayCone).symm (affineRayCharacter, 0))

/-- The first lower-chart coordinate character evaluates the difference of lattice coordinates. -/
@[simp]
theorem affinePlaneBlowUpLowerCharacter₁_apply (n : (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    (affinePlaneBlowUpLowerCharacter₁ : _ →+ ℤ) n = n.1 0 - n.2 0 := by
  simp [affinePlaneBlowUpLowerCharacter₁, blowUpSemigroupEquiv, blowUpShear]

/-- The second lower-chart coordinate character, dual to the generator `(1, 1)`,
with lattice coefficients `(0, 1)`. -/
noncomputable def affinePlaneBlowUpLowerCharacter₂ :
    dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone :=
  (blowUpSemigroupEquiv false).symm
    ((dualSemigroupProdEquiv affineRayFan.lattice affineRayFan.lattice
      affineRayCone affineRayCone).symm (0, affineRayCharacter))

/-- The second lower-chart coordinate character evaluates the second lattice coordinate. -/
@[simp]
theorem affinePlaneBlowUpLowerCharacter₂_apply (n : (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    (affinePlaneBlowUpLowerCharacter₂ : _ →+ ℤ) n = n.2 0 := by
  simp [affinePlaneBlowUpLowerCharacter₂, blowUpSemigroupEquiv, blowUpShear]

/-- The forward upper-chart coordinates evaluate the dual-basis characters
`(1, 0)` and `(−1, 1)`. -/
@[simp]
theorem affinePlaneBlowUpUpperPointHomeomorph_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone)) :
    affinePlaneBlowUpUpperPointHomeomorph x =
      (x (MonoidAlgebra.single (ofAdd affinePlaneBlowUpUpperCharacter₁) 1),
        x (MonoidAlgebra.single (ofAdd affinePlaneBlowUpUpperCharacter₂) 1)) := by
  exact blowUpPointHomeomorph_apply true x

/-- The forward lower-chart coordinates evaluate the dual-basis characters
`(1, −1)` and `(0, 1)`. -/
@[simp]
theorem affinePlaneBlowUpLowerPointHomeomorph_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone)) :
    affinePlaneBlowUpLowerPointHomeomorph x =
      (x (MonoidAlgebra.single (ofAdd affinePlaneBlowUpLowerCharacter₁) 1),
        x (MonoidAlgebra.single (ofAdd affinePlaneBlowUpLowerCharacter₂) 1)) := by
  exact blowUpPointHomeomorph_apply false x

/-- The upper affine chart parametrization of the toric blow-up. -/
noncomputable def affinePlaneBlowUpUpperChart (z : ℂ × ℂ) :
    affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan :=
  affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
    ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩
    (affinePlaneBlowUpUpperPointHomeomorph.symm z)

/-- The lower affine chart parametrization of the toric blow-up. -/
noncomputable def affinePlaneBlowUpLowerChart (z : ℂ × ℂ) :
    affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan :=
  affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
    ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩
    (affinePlaneBlowUpLowerPointHomeomorph.symm z)

/-- The upper parametrization inserts the point with the prescribed upper coordinates. -/
theorem affinePlaneBlowUpUpperChart_def (z : ℂ × ℂ) :
    affinePlaneBlowUpUpperChart z =
      affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
        ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩
        (affinePlaneBlowUpUpperPointHomeomorph.symm z) := (rfl)

/-- The lower parametrization inserts the point with the prescribed lower coordinates. -/
theorem affinePlaneBlowUpLowerChart_def (z : ℂ × ℂ) :
    affinePlaneBlowUpLowerChart z =
      affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
        ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩
        (affinePlaneBlowUpLowerPointHomeomorph.symm z) := (rfl)

/-- The upper parametrization is an open embedding for the existing monomial topology. -/
theorem isOpenEmbedding_affinePlaneBlowUpUpperChart :
    Topology.IsOpenEmbedding affinePlaneBlowUpUpperChart :=
  (affinePlaneBlowUpFan.isOpenEmbedding_analyticAffineChartι
    isRegular_affinePlaneBlowUpFan _).comp
      affinePlaneBlowUpUpperPointHomeomorph.symm.isOpenEmbedding

/-- The lower parametrization is an open embedding for the existing monomial topology. -/
theorem isOpenEmbedding_affinePlaneBlowUpLowerChart :
    Topology.IsOpenEmbedding affinePlaneBlowUpLowerChart :=
  (affinePlaneBlowUpFan.isOpenEmbedding_analyticAffineChartι
    isRegular_affinePlaneBlowUpFan _).comp
      affinePlaneBlowUpLowerPointHomeomorph.symm.isOpenEmbedding

/-- The two explicit affine charts cover the analytic realization of the subdivided fan. -/
theorem exists_affinePlaneBlowUpUpperChart_eq_or_exists_affinePlaneBlowUpLowerChart_eq
    (x : affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan) :
    (∃ z, affinePlaneBlowUpUpperChart z = x) ∨
      (∃ z, affinePlaneBlowUpLowerChart z = x) := by
  obtain ⟨σ, y, rfl⟩ := affinePlaneBlowUpFan.exists_analyticAffineChartι_apply_eq
    isRegular_affinePlaneBlowUpFan x
  rcases mem_affinePlaneBlowUpFan_cones.1 σ.2 with hσ | hσ
  · let p : affinePlaneBlowUpFan.analyticAffineChartDiagram.obj
        ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2
          (Or.inl (.refl _))⟩ :=
        faceAffinePointMap affinePlaneBlowUpFan.lattice hσ y
    refine Or.inr ⟨affinePlaneBlowUpLowerPointHomeomorph p, ?_⟩
    unfold affinePlaneBlowUpLowerChart
    -- The face map point is read in the bundled maximal chart.
    erw [Homeomorph.symm_apply_apply]
    exact affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap
      isRegular_affinePlaneBlowUpFan hσ.le y
  · let p : affinePlaneBlowUpFan.analyticAffineChartDiagram.obj
        ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2
          (Or.inr (.refl _))⟩ :=
        faceAffinePointMap affinePlaneBlowUpFan.lattice hσ y
    refine Or.inl ⟨affinePlaneBlowUpUpperPointHomeomorph p, ?_⟩
    unfold affinePlaneBlowUpUpperChart
    -- The face map point is read in the bundled maximal chart.
    erw [Homeomorph.symm_apply_apply]
    exact affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap
      isRegular_affinePlaneBlowUpFan hσ.le y

private theorem blowUp_coordinate_formula (upper : Bool) (n : ℕ∞ω) (z : ℂ × ℂ) :
    letI := affinePointTopology
      (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
    affinePlaneDiffeomorph n
      (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
        isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan
        (affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
          (blowUpFanCone upper) ((blowUpPointHomeomorph upper).symm z))) =
      if upper then (z.1, z.1 * z.2) else (z.1 * z.2, z.2) := by
  dsimp only
  let _ := affinePointTopology
    (affinePlaneBlowUpFan.analyticChartGenerators (blowUpFanCone upper)).2
  let _ := affinePointTopology (affinePlaneFan.analyticChartGenerators maxCone).2
  let _ := affinePointTopology rayGenerators
  have hmap : Set.MapsTo affinePlaneBlowUpFan_isSubdivision.toFanHom.realMap
      (blowUpCone upper : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)))
      (quadrant : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) := by
    rw [Fan.IsSubdivision.toFanHom_realMap]
    cases upper
    · exact affinePlaneBlowUpLowerCone_le_prod
    · exact affinePlaneBlowUpUpperCone_le_prod
  erw [FanHom.analyticMap_analyticAffineChartι_of_mapsTo
    (υ := maxCone) _ _ _ hmap, affinePlaneDiffeomorph_analyticAffineChartι]
  -- Unbundle the chart carrier before using the monomial evaluation formulas.
  erw [FanHom.analyticChartMap_apply,
    AffineSemigroupComplexPoint.comap_apply_single,
    AffineSemigroupComplexPoint.comap_apply_single,
    blowUpPointHomeomorph_symm_apply_single,
    blowUpPointHomeomorph_symm_apply_single]
  simp only [affineRayPointHomeomorph_symm_apply_single_eq_pow,
    dualSemigroupProdEquiv_fst_apply, dualSemigroupProdEquiv_snd_apply,
    blowUpSemigroupEquiv, dualSemigroupEquiv_apply, dualSemigroupMap_apply,
    Fan.IsSubdivision.toFanHom_latticeMap, AddMonoidHom.id_apply,
    dualSemigroupProdEquiv_symm_apply, affineRayCharacter_apply,
    AddSubmonoid.coe_zero, AddMonoidHom.zero_apply]
  cases upper <;> simp [blowUpShear]

/-- On the upper chart, the actual toric blow-up map has the polynomial formula
`(u, v) ↦ (u, u * v)`, including on the exceptional axis `u = 0`. -/
theorem affinePlaneDiffeomorph_analyticMap_affinePlaneBlowUpUpperChart
    (n : ℕ∞ω) (z : ℂ × ℂ) :
    affinePlaneDiffeomorph n
      (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
        isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan
        (affinePlaneBlowUpUpperChart z)) = (z.1, z.1 * z.2) :=
  blowUp_coordinate_formula true n z

/-- On the lower chart, the actual toric blow-up map has the polynomial formula
`(u, v) ↦ (u * v, v)`, including on the exceptional axis `v = 0`. -/
theorem affinePlaneDiffeomorph_analyticMap_affinePlaneBlowUpLowerChart
    (n : ℕ∞ω) (z : ℂ × ℂ) :
    affinePlaneDiffeomorph n
      (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
        isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan
        (affinePlaneBlowUpLowerChart z)) = (z.1 * z.2, z.2) :=
  blowUp_coordinate_formula false n z

end TauCeti.Toric
