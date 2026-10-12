/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.Basic

/-!
# Explicit affine charts of the toric blow-up of the plane

The two maximal cones in the diagonal subdivision of the positive quadrant are unimodular
images of the quadrant. Transporting characters through these lattice shears identifies each
of their complex-point charts with `ℂ × ℂ`. In these coordinates the toric map to the plane is
`(u, v) ↦ (u, u * v)` on the upper cone and `(u, v) ↦ (u * v, v)` on the lower cone.
These formulas identify the exceptional fibre with a coordinate axis in each chart, including
points where a coordinate vanishes.

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
  rfl

/-- In upper-chart coordinates, a character monomial has exponents given by its values on
`(1, 1)` and `(0, 1)`, the two primitive generators of the cone. -/
theorem affinePlaneBlowUpUpperPointHomeomorph_symm_apply_single (z : ℂ × ℂ)
    (m : dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone) :
    let x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone) :=
      affinePlaneBlowUpUpperPointHomeomorph.symm z
    x (MonoidAlgebra.single (ofAdd m) 1) =
      z.1 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (1, 1)).toNat *
        z.2 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (0, 1)).toNat := by
  have h := blowUpPointHomeomorph_symm_apply_single true z m
  simp only [affineRayPointHomeomorph_symm_apply_single_eq_pow,
    dualSemigroupProdEquiv_fst_apply, dualSemigroupProdEquiv_snd_apply,
    blowUpSemigroupEquiv, dualSemigroupEquiv_apply] at h
  dsimp only
  -- The public homeomorphism has the same inverse as the shared construction.
  convert h using 1
  · rfl
  · simp [blowUpShear]

/-- In lower-chart coordinates, a character monomial has exponents given by its values on
`(1, 0)` and `(1, 1)`, the two primitive generators of the cone. -/
theorem affinePlaneBlowUpLowerPointHomeomorph_symm_apply_single (z : ℂ × ℂ)
    (m : dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone) :
    let x : AffineSemigroupComplexPoint
      (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone) :=
      affinePlaneBlowUpLowerPointHomeomorph.symm z
    x (MonoidAlgebra.single (ofAdd m) 1) =
      z.1 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (1, 0)).toNat *
        z.2 ^ ((m : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) →+ ℤ) (1, 1)).toNat := by
  have h := blowUpPointHomeomorph_symm_apply_single false z m
  simp only [affineRayPointHomeomorph_symm_apply_single_eq_pow,
    dualSemigroupProdEquiv_fst_apply, dualSemigroupProdEquiv_snd_apply,
    blowUpSemigroupEquiv, dualSemigroupEquiv_apply] at h
  dsimp only
  -- The public homeomorphism has the same inverse as the shared construction.
  convert h using 1
  · rfl
  · simp [blowUpShear]

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

/-- The upper parametrization is the inverse coordinate homeomorphism followed by the
canonical affine-chart inclusion. -/
theorem affinePlaneBlowUpUpperChart_def (z : ℂ × ℂ) :
    affinePlaneBlowUpUpperChart z =
      affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
        ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩
        (affinePlaneBlowUpUpperPointHomeomorph.symm z) := (rfl)

/-- The lower parametrization is the inverse coordinate homeomorphism followed by the
canonical affine-chart inclusion. -/
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
theorem exists_affinePlaneBlowUpChart_eq
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
    rw [affinePlaneBlowUpLowerChart_def]
    -- The face map point is read in the bundled maximal chart.
    erw [Homeomorph.symm_apply_apply]
    exact affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap
      isRegular_affinePlaneBlowUpFan hσ.le y
  · let p : affinePlaneBlowUpFan.analyticAffineChartDiagram.obj
        ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2
          (Or.inr (.refl _))⟩ :=
        faceAffinePointMap affinePlaneBlowUpFan.lattice hσ y
    refine Or.inl ⟨affinePlaneBlowUpUpperPointHomeomorph p, ?_⟩
    rw [affinePlaneBlowUpUpperChart_def]
    -- The face map point is read in the bundled maximal chart.
    erw [Homeomorph.symm_apply_apply]
    exact affinePlaneBlowUpFan.analyticAffineChartι_faceAffinePointMap
      isRegular_affinePlaneBlowUpFan hσ.le y

private theorem blowUpCone_le_quadrant (upper : Bool) : blowUpCone upper ≤ quadrant := by
  intro x hx
  cases upper
  · have hx' := (mem_affinePlaneBlowUpLowerCone_iff _).1 hx
    exact ⟨(mem_affineRayCone_iff _).2 (hx'.1.trans hx'.2),
      (mem_affineRayCone_iff _).2 hx'.1⟩
  · have hx' := (mem_affinePlaneBlowUpUpperCone_iff _).1 hx
    exact ⟨(mem_affineRayCone_iff _).2 hx'.1,
      (mem_affineRayCone_iff _).2 (hx'.1.trans hx'.2)⟩

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
    exact blowUpCone_le_quadrant upper
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
