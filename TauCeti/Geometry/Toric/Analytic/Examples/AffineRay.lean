/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.AffineRay
public import TauCeti.Geometry.Toric.Analytic.Cone.FaceLocalization
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# The affine toric line and its punctured-line face chart

The positive ray in the standard rank-one lattice has affine complex-point chart `ℂ`.
Its zero face has chart `ℂˣ`, and face localization is the ordinary inclusion into `ℂ`.
The identifications use the regular-cone coordinate maps, with the standard lattice basis;
in particular, the coordinate on the affine line is evaluation of the standard character.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.2.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2.
-/

public section

open scoped ContDiff Manifold
open Multiplicative

namespace TauCeti.Toric

private noncomputable instance rayUnique : Unique (ToricRay affineRayCone) := by
  rw [affineRayCone_eq_hull]
  exact ⟨⟨ToricRay.hullSingleton one_ne_zero⟩, ToricRay.eq_hullSingleton one_ne_zero⟩

private noncomputable def rayBasis :
    Module.Basis (ToricRay affineRayCone ⊕ Fin 0) ℤ (Fin 1 → ℤ) :=
  (Pi.basisFun ℤ (Fin 1)).reindex
    ((Equiv.ofUnique (Fin 1) (ToricRay affineRayCone)).trans (Equiv.sumEmpty _ _).symm)

private theorem rayBasis_apply (ρ : ToricRay affineRayCone) : rayBasis (Sum.inl ρ) = 1 := by
  ext j
  simp [rayBasis, Pi.basisFun_apply, Subsingleton.elim j (0 : Fin 1)]

private theorem rayBasis_extends (ρ : ToricRay affineRayCone) :
    IsPrimitiveGenerator ((Int.castAddHom ℝ).compLeft (Fin 1)) ρ
      (rayBasis (Sum.inl ρ)) := by
  rw [rayBasis_apply, isPrimitiveGenerator_iff]
  refine ⟨?_, ?_⟩
  · have hi : ((Int.castAddHom ℝ).compLeft (Fin 1)) (1 : Fin 1 → ℤ) = 1 := by
      ext j
      simp
    rw [hi]
    -- Rewriting under the binder transports the ray's dependent cone carrier.
    revert ρ
    rw [affineRayCone_eq_hull]
    intro ρ
    rw [ToricRay.eq_hullSingleton one_ne_zero ρ, ToricRay.mem_hullSingleton]
    exact PointedCone.subset_hull (by simp)
  · simpa only [rayBasis_apply] using rayBasis.isPrimitive (Sum.inl ρ)

private noncomputable def rayNumbering : ToricRay affineRayCone ≃ Fin 1 := Equiv.ofUnique _ _

variable {s : ℕ}
  (g : AddGeneratingFamily (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone) s)

/-- The regular coordinate identification of the affine ray chart with the complex line,
for any finite monomial generating family. -/
noncomputable def affineRayPointHomeomorph :
    @Homeomorph (AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) ℂ
      (affinePointTopology g) inferInstance :=
  let _ := affinePointTopology g
  (coneChartHomeomorph (isIntegralLattice_intCast 1)
    isRegularCone_affineRayCone.toIsToricCone rayBasis_extends g).trans
      ((Homeomorph.prodUnique _ _).trans (Homeomorph.piUnique fun _ ↦ ℂ))

/-- The standard character, restricted to the semigroup of the positive ray. -/
noncomputable def affineRayCharacter : dualSemigroup (isIntegralLattice_intCast 1) affineRayCone :=
  dualSemigroupCoord (isIntegralLattice_intCast 1)
    isRegularCone_affineRayCone.toIsToricCone rayBasis_extends (Sum.inl default)

/-- The affine-line coordinate is evaluation of its standard character monomial. -/
@[simp]
theorem affineRayPointHomeomorph_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    affineRayPointHomeomorph g x = x (MonoidAlgebra.single (ofAdd affineRayCharacter) 1) := by
  simpa only [affineRayPointHomeomorph, affineRayCharacter, Homeomorph.trans_apply,
    Homeomorph.coe_prodUnique, Homeomorph.piUnique_apply,
    coe_coneChartHomeomorph] using coneChartEquiv_fst_apply (isIntegralLattice_intCast 1)
    isRegularCone_affineRayCone.toIsToricCone rayBasis_extends x default

/-- The complex point with coordinate `z` evaluates the standard character monomial to `z`. -/
@[simp]
theorem affineRayPointHomeomorph_symm_apply_single (z : ℂ) :
    let _ := affinePointTopology g
    ((affineRayPointHomeomorph g).symm z)
      (MonoidAlgebra.single (ofAdd affineRayCharacter) 1) = z := by
  let _ := affinePointTopology g
  rw [← affineRayPointHomeomorph_apply]
  exact (affineRayPointHomeomorph g).apply_symm_apply z

/-- Reconstructing a complex point from its standard character coordinate returns that point. -/
@[simp]
theorem affineRayPointHomeomorph_symm_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    let _ := affinePointTopology g
    (affineRayPointHomeomorph g).symm
      (x (MonoidAlgebra.single (ofAdd affineRayCharacter) 1)) = x := by
  let _ := affinePointTopology g
  rw [← affineRayPointHomeomorph_apply]
  exact (affineRayPointHomeomorph g).symm_apply_apply x

/-- The standard character takes the value `n 0` on an integer lattice vector `n`. -/
@[simp]
theorem affineRayCharacter_apply (n : Fin 1 → ℤ) :
    (affineRayCharacter : _ →+ ℤ) n = n 0 := by
  rw [affineRayCharacter, coe_dualSemigroupCoord]
  simp [rayBasis, Pi.basisFun_repr]

/-- The regular-cone complex structure on the affine ray chart. Its model retains the single
ray coordinate and the empty family of complementary coordinates. -/
@[instance_reducible]
noncomputable def affineRayChartedSpace :
    @ChartedSpace ((Fin 1 → ℂ) × (Fin 0 → ℂ)) inferInstance
      (AffineSemigroupComplexPoint (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone))
      (affinePointTopology g) :=
  coneChartedSpace (isIntegralLattice_intCast 1) isRegularCone_affineRayCone.toIsToricCone
    rayBasis_extends rayNumbering g

/-- The affine ray chart is a complex manifold for its regular-cone complex structure. -/
theorem isManifold_affineRayChartedSpace (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := affineRayChartedSpace g
    IsManifold 𝓘(ℂ, (Fin 1 → ℂ) × (Fin 0 → ℂ)) n
      (AffineSemigroupComplexPoint (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :=
  isManifold_coneChartedSpace (isIntegralLattice_intCast 1)
    isRegularCone_affineRayCone.toIsToricCone rayBasis_extends rayNumbering g n

private noncomputable def rayModelEquiv : ((Fin 1 → ℂ) × (Fin 0 → ℂ)) ≃L[ℂ] ℂ :=
  (ContinuousLinearEquiv.prodUnique ℂ _ _).trans
    (ContinuousLinearEquiv.piUnique ℂ fun _ ↦ ℂ)

private theorem rayModelEquiv_coneChartAmbient
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    rayModelEquiv (coneChartAmbient (isIntegralLattice_intCast 1)
      isRegularCone_affineRayCone.toIsToricCone rayBasis_extends rayNumbering x) =
      affineRayPointHomeomorph g x := by
  rw [affineRayPointHomeomorph_apply]
  simpa only [rayModelEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodUnique_apply, ContinuousLinearEquiv.piUnique_apply,
    coneChartAmbient_fst_apply, Subsingleton.elim (rayNumbering.symm default) default,
    affineRayCharacter] using
      coneChartEquiv_fst_apply (isIntegralLattice_intCast 1)
        isRegularCone_affineRayCone.toIsToricCone rayBasis_extends x default

/-- The standard coordinate identifies the affine ray chart biholomorphically with `ℂ`,
for the existing regular-cone complex structure. -/
noncomputable def affineRayPointDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := affineRayChartedSpace g
    Diffeomorph 𝓘(ℂ, (Fin 1 → ℂ) × (Fin 0 → ℂ)) 𝓘(ℂ, ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone))
      ℂ n := by
  let _ := affinePointTopology g
  let _ := affineRayChartedSpace g
  refine ⟨(affineRayPointHomeomorph g).toEquiv, ?_, ?_⟩
  · exact (contMDiff_apply_single (isIntegralLattice_intCast 1)
      isRegularCone_affineRayCone.toIsToricCone rayBasis_extends rayNumbering g
        affineRayCharacter n).congr fun x ↦ affineRayPointHomeomorph_apply g x
  · apply (contMDiff_coneChartAmbient_comp_iff (isIntegralLattice_intCast 1)
      isRegularCone_affineRayCone.toIsToricCone rayBasis_extends rayNumbering g).1
    refine rayModelEquiv.symm.toContinuousLinearMap.contMDiff.congr fun z ↦ ?_
    apply rayModelEquiv.injective
    exact (rayModelEquiv_coneChartAmbient g ((affineRayPointHomeomorph g).symm z)).trans
      (((affineRayPointHomeomorph g).apply_symm_apply z).trans
        (rayModelEquiv.apply_symm_apply z).symm)

/-- The biholomorphic identification has the same underlying homeomorphism as the standard
coordinate identification. -/
@[simp]
theorem affineRayPointDiffeomorph_toHomeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := affineRayChartedSpace g
    (affineRayPointDiffeomorph g n).toHomeomorph = affineRayPointHomeomorph g := by
  let _ := affinePointTopology g
  let _ := affineRayChartedSpace g
  rfl

/-- The biholomorphic affine-line coordinate evaluates the standard character monomial. -/
@[simp]
theorem affineRayPointDiffeomorph_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    let _ := affinePointTopology g
    let _ := affineRayChartedSpace g
    affineRayPointDiffeomorph g n x = x (MonoidAlgebra.single (ofAdd affineRayCharacter) 1) := by
  let _ := affinePointTopology g
  let _ := affineRayChartedSpace g
  exact affineRayPointHomeomorph_apply g x

/-- The inverse biholomorphic coordinate reconstructs a point from its standard character value. -/
@[simp]
theorem affineRayPointDiffeomorph_symm_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    let _ := affinePointTopology g
    let _ := affineRayChartedSpace g
    (affineRayPointDiffeomorph g n).symm
      (x (MonoidAlgebra.single (ofAdd affineRayCharacter) 1)) = x := by
  let _ := affinePointTopology g
  let _ := affineRayChartedSpace g
  rw [← affineRayPointDiffeomorph_apply]
  exact (affineRayPointDiffeomorph g n).symm_apply_apply x

private noncomputable def zeroFaceBasis :
    Module.Basis (ToricRay (⊥ : PointedCone ℝ (Fin 1 → ℝ)) ⊕ Fin 1) ℤ (Fin 1 → ℤ) :=
  (Pi.basisFun ℤ (Fin 1)).reindex (Equiv.emptySum _ _).symm

private theorem zeroFaceBasis_extends
    (ρ : ToricRay (⊥ : PointedCone ℝ (Fin 1 → ℝ))) :
    IsPrimitiveGenerator ((Int.castAddHom ℝ).compLeft (Fin 1)) ρ
      (zeroFaceBasis (Sum.inl ρ)) := isEmptyElim ρ

/-- The standard Laurent character on the zero-face semigroup. -/
noncomputable def affineRayZeroFaceCharacter :
    dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)) :=
  dualSemigroupCoord (isIntegralLattice_intCast 1) (isToricCone_bot _)
    zeroFaceBasis_extends (Sum.inr 0)

/-- The Laurent coordinate is the same integral character as the affine-line coordinate. -/
@[simp]
theorem affineRayZeroFaceCharacter_apply (n : Fin 1 → ℤ) :
    (affineRayZeroFaceCharacter : _ →+ ℤ) n = n 0 := by
  rw [affineRayZeroFaceCharacter, coe_dualSemigroupCoord]
  simp [zeroFaceBasis, Pi.basisFun_repr]

variable {t : ℕ}
  (g₀ : AddGeneratingFamily
    (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ))) t)

/-- The zero-face chart is the punctured complex line, with its usual units topology. -/
noncomputable def affineRayZeroFacePointHomeomorph :
    @Homeomorph (AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) ℂˣ
      (affinePointTopology g₀) inferInstance :=
  let _ := affinePointTopology g₀
  (coneChartHomeomorph (isIntegralLattice_intCast 1) (isToricCone_bot _)
    zeroFaceBasis_extends g₀).trans
      ((Homeomorph.uniqueProd _ _).trans (Homeomorph.piUnique fun _ ↦ ℂˣ))

/-- The punctured-line coordinate is evaluation of the standard Laurent character. -/
@[simp]
theorem affineRayZeroFacePointHomeomorph_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :
    (affineRayZeroFacePointHomeomorph g₀ x : ℂ) =
      x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1) := by
  simpa only [affineRayZeroFacePointHomeomorph, affineRayZeroFaceCharacter,
    Homeomorph.trans_apply, Homeomorph.coe_uniqueProd, Homeomorph.piUnique_apply,
    coe_coneChartHomeomorph, Subsingleton.elim (default : Fin 1) (0 : Fin 1)] using
      val_coneChartEquiv_snd_apply (isIntegralLattice_intCast 1) (isToricCone_bot _)
        zeroFaceBasis_extends x 0

/-- The zero-face point with unit coordinate `z` evaluates its standard Laurent monomial to `z`. -/
@[simp]
theorem affineRayZeroFacePointHomeomorph_symm_apply_single (z : ℂˣ) :
    let _ := affinePointTopology g₀
    ((affineRayZeroFacePointHomeomorph g₀).symm z)
      (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1) = (z : ℂ) := by
  let _ := affinePointTopology g₀
  rw [← affineRayZeroFacePointHomeomorph_apply]
  exact congrArg (fun w : ℂˣ ↦ (w : ℂ))
    ((affineRayZeroFacePointHomeomorph g₀).apply_symm_apply z)

/-- Reconstructing a zero-face point from its standard Laurent character unit returns the point. -/
@[simp]
theorem affineRayZeroFacePointHomeomorph_symm_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ))))
    (hx : x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1) ≠ 0) :
    let _ := affinePointTopology g₀
    (affineRayZeroFacePointHomeomorph g₀).symm
      (Units.mk0 (x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1)) hx) = x := by
  let _ := affinePointTopology g₀
  have h : Units.mk0 (x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1)) hx =
      affineRayZeroFacePointHomeomorph g₀ x := by
    apply Units.ext
    exact (affineRayZeroFacePointHomeomorph_apply g₀ x).symm
  rw [h]
  exact (affineRayZeroFacePointHomeomorph g₀).symm_apply_apply x

private noncomputable def zeroFaceNumbering :
    ToricRay (⊥ : PointedCone ℝ (Fin 1 → ℝ)) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _

/-- The regular-cone complex structure on the zero-face chart. Its model retains the empty
family of ray coordinates and the single invertible coordinate. -/
@[instance_reducible]
noncomputable def affineRayZeroFaceChartedSpace :
    @ChartedSpace ((Fin 0 → ℂ) × (Fin 1 → ℂ)) inferInstance
      (AffineSemigroupComplexPoint
        (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ))))
      (affinePointTopology g₀) :=
  coneChartedSpace (isIntegralLattice_intCast 1) (isToricCone_bot _)
    zeroFaceBasis_extends zeroFaceNumbering g₀

/-- The zero-face chart is a complex manifold for its regular-cone complex structure. -/
theorem isManifold_affineRayZeroFaceChartedSpace (n : ℕ∞ω) :
    let _ := affinePointTopology g₀
    let _ := affineRayZeroFaceChartedSpace g₀
    IsManifold 𝓘(ℂ, (Fin 0 → ℂ) × (Fin 1 → ℂ)) n
      (AffineSemigroupComplexPoint
        (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :=
  isManifold_coneChartedSpace (isIntegralLattice_intCast 1) (isToricCone_bot _)
    zeroFaceBasis_extends zeroFaceNumbering g₀ n

private noncomputable def zeroFaceModelEquiv : ((Fin 0 → ℂ) × (Fin 1 → ℂ)) ≃L[ℂ] ℂ :=
  (ContinuousLinearEquiv.uniqueProd ℂ _ _).trans
    (ContinuousLinearEquiv.piUnique ℂ fun _ ↦ ℂ)

private theorem zeroFaceModelEquiv_coneChartAmbient
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :
    zeroFaceModelEquiv (coneChartAmbient (isIntegralLattice_intCast 1) (isToricCone_bot _)
      zeroFaceBasis_extends zeroFaceNumbering x) =
      (affineRayZeroFacePointHomeomorph g₀ x : ℂ) := by
  rw [affineRayZeroFacePointHomeomorph_apply]
  simpa only [zeroFaceModelEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.uniqueProd_apply, ContinuousLinearEquiv.piUnique_apply,
    coneChartAmbient_snd_apply, Subsingleton.elim (default : Fin 1) (0 : Fin 1),
    affineRayZeroFaceCharacter] using
      val_coneChartEquiv_snd_apply (isIntegralLattice_intCast 1) (isToricCone_bot _)
        zeroFaceBasis_extends x 0

/-- The standard Laurent coordinate identifies the zero-face chart biholomorphically with
the usual complex manifold `ℂˣ`. -/
noncomputable def affineRayZeroFacePointDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g₀
    let _ := affineRayZeroFaceChartedSpace g₀
    Diffeomorph 𝓘(ℂ, (Fin 0 → ℂ) × (Fin 1 → ℂ)) 𝓘(ℂ, ℂ)
      (AffineSemigroupComplexPoint
        (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ))))
      ℂˣ n := by
  let _ := affinePointTopology g₀
  let _ := affineRayZeroFaceChartedSpace g₀
  refine ⟨(affineRayZeroFacePointHomeomorph g₀).toEquiv, ?_, ?_⟩
  · apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    exact (contMDiff_apply_single (isIntegralLattice_intCast 1) (isToricCone_bot _)
      zeroFaceBasis_extends zeroFaceNumbering g₀ affineRayZeroFaceCharacter n).congr
        fun x ↦ affineRayZeroFacePointHomeomorph_apply g₀ x
  · apply (contMDiff_coneChartAmbient_comp_iff (isIntegralLattice_intCast 1)
      (isToricCone_bot _) zeroFaceBasis_extends zeroFaceNumbering g₀).1
    refine (zeroFaceModelEquiv.symm.toContinuousLinearMap.contMDiff.comp
      Units.contMDiff_val).congr fun z ↦ ?_
    apply zeroFaceModelEquiv.injective
    exact (zeroFaceModelEquiv_coneChartAmbient g₀
      ((affineRayZeroFacePointHomeomorph g₀).symm z)).trans
        ((congrArg (fun w : ℂˣ ↦ (w : ℂ))
          ((affineRayZeroFacePointHomeomorph g₀).apply_symm_apply z)).trans
            (zeroFaceModelEquiv.apply_symm_apply (z : ℂ)).symm)

/-- The biholomorphic zero-face identification has its standard coordinate homeomorphism. -/
@[simp]
theorem affineRayZeroFacePointDiffeomorph_toHomeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g₀
    let _ := affineRayZeroFaceChartedSpace g₀
    (affineRayZeroFacePointDiffeomorph g₀ n).toHomeomorph =
      affineRayZeroFacePointHomeomorph g₀ := by
  let _ := affinePointTopology g₀
  let _ := affineRayZeroFaceChartedSpace g₀
  rfl

/-- The biholomorphic punctured-line coordinate evaluates the standard Laurent monomial. -/
@[simp]
theorem val_affineRayZeroFacePointDiffeomorph_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :
    let _ := affinePointTopology g₀
    let _ := affineRayZeroFaceChartedSpace g₀
    (affineRayZeroFacePointDiffeomorph g₀ n x : ℂ) =
      x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1) := by
  let _ := affinePointTopology g₀
  let _ := affineRayZeroFaceChartedSpace g₀
  exact affineRayZeroFacePointHomeomorph_apply g₀ x

/-- The inverse biholomorphic coordinate reconstructs a point from its Laurent character unit. -/
@[simp]
theorem affineRayZeroFacePointDiffeomorph_symm_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ))))
    (hx : x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1) ≠ 0) :
    let _ := affinePointTopology g₀
    let _ := affineRayZeroFaceChartedSpace g₀
    (affineRayZeroFacePointDiffeomorph g₀ n).symm
      (Units.mk0 (x (MonoidAlgebra.single (ofAdd affineRayZeroFaceCharacter) 1)) hx) = x := by
  let _ := affinePointTopology g₀
  let _ := affineRayZeroFaceChartedSpace g₀
  exact affineRayZeroFacePointHomeomorph_symm_apply g₀ x hx

/-- In the standard coordinates, localization along the zero face is `ℂˣ → ℂ`. -/
theorem affineRayPointHomeomorph_faceAffinePointMap
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :
    affineRayPointHomeomorph g
      (faceAffinePointMap (isIntegralLattice_intCast 1)
        isRegularCone_affineRayCone.salient.bot_isFaceOf x) =
      (affineRayZeroFacePointHomeomorph g₀ x : ℂ) := by
  rw [affineRayPointHomeomorph_apply, faceAffinePointMap_apply_single,
    affineRayZeroFacePointHomeomorph_apply]
  apply congrArg x
  apply congrArg (fun m ↦ MonoidAlgebra.single (ofAdd m) 1)
  apply Subtype.ext
  exact DFunLike.ext _ _ fun n ↦
    (affineRayCharacter_apply n).trans (affineRayZeroFaceCharacter_apply n).symm

/-- On a unit coordinate, the face map is the usual inclusion of the punctured line. -/
@[simp↓]
theorem affineRayPointHomeomorph_faceAffinePointMap_symm (z : ℂˣ) :
    let _ := affinePointTopology g₀
    affineRayPointHomeomorph g
      (faceAffinePointMap (isIntegralLattice_intCast 1)
        isRegularCone_affineRayCone.salient.bot_isFaceOf
        ((affineRayZeroFacePointHomeomorph g₀).symm z)) = (z : ℂ) := by
  let _ := affinePointTopology g₀
  rw [affineRayPointHomeomorph_faceAffinePointMap g g₀, Homeomorph.apply_symm_apply]

end TauCeti.Toric
