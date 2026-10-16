/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine
public import TauCeti.Geometry.Toric.Analytic.Examples.AffineRay

/-!
# The two affine coordinates of the toric projective line

The two rays of the complete rank-one fan give affine complex-line charts. The coordinate
on the negative-ray chart is evaluation of the negative standard character. On their common
zero-cone chart the positive and negative coordinates are units and multiply to one. Thus
the chart transition is inversion, the usual transition for the projective line.

The negative-ray coordinate construction follows the positive-ray construction in
`TauCeti.Geometry.Toric.Analytic.Examples.AffineRay`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open Multiplicative Set
open scoped ContDiff Manifold

namespace TauCeti.Toric

private noncomputable instance negativeRayUnique : Unique (ToricRay negativeRayCone) := by
  rw [negativeRayCone_def]
  exact ⟨⟨ToricRay.hullSingleton (neg_ne_zero.mpr one_ne_zero)⟩,
    ToricRay.eq_hullSingleton (neg_ne_zero.mpr one_ne_zero)⟩

private noncomputable def negativeRayBasis :
    Module.Basis (ToricRay negativeRayCone ⊕ Fin 0) ℤ (Fin 1 → ℤ) :=
  ((Pi.basisFun ℤ (Fin 1)).map
    (LinearEquiv.neg ℤ : (Fin 1 → ℤ) ≃ₗ[ℤ] (Fin 1 → ℤ))).reindex
    ((Equiv.ofUnique (Fin 1) (ToricRay negativeRayCone)).trans (Equiv.sumEmpty _ _).symm)

private theorem negativeRayBasis_apply (ρ : ToricRay negativeRayCone) :
    negativeRayBasis (Sum.inl ρ) = -(1 : Fin 1 → ℤ) := by
  ext j
  simp [negativeRayBasis, Pi.basisFun_apply, Subsingleton.elim j (0 : Fin 1)]

private theorem negativeRayBasis_extends (ρ : ToricRay negativeRayCone) :
    IsPrimitiveGenerator ((Int.castAddHom ℝ).compLeft (Fin 1)) ρ
      (negativeRayBasis (Sum.inl ρ)) := by
  rw [negativeRayBasis_apply, isPrimitiveGenerator_iff]
  refine ⟨?_, ?_⟩
  · rw [map_neg, intCast_finOne_one]
    revert ρ
    rw [negativeRayCone_def]
    intro ρ
    rw [ToricRay.eq_hullSingleton (neg_ne_zero.mpr one_ne_zero) ρ,
      ToricRay.mem_hullSingleton]
    exact PointedCone.subset_hull (by simp)
  · simpa only [negativeRayBasis_apply] using negativeRayBasis.isPrimitive (Sum.inl ρ)

variable {s : ℕ}
  (g : AddGeneratingFamily (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone) s)

/-- The negative standard character, restricted to the dual semigroup of the negative ray. -/
noncomputable def negativeRayCharacter :
    dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone :=
  dualSemigroupCoord (isIntegralLattice_intCast 1)
    isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends (Sum.inl default)

/-- The negative-ray character takes the negative of the integer lattice coordinate. -/
@[simp] theorem negativeRayCharacter_apply (n : Fin 1 → ℤ) :
    (negativeRayCharacter : _ →+ ℤ) n = -(n 0) := by
  rw [negativeRayCharacter, coe_dualSemigroupCoord]
  simp [negativeRayBasis, Pi.basisFun_repr]

/-- The negative-ray affine chart is the complex line in its standard character coordinate. -/
noncomputable def negativeRayPointHomeomorph :
    @Homeomorph (AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) ℂ
      (affinePointTopology g) inferInstance :=
  let _ := affinePointTopology g
  (coneChartHomeomorph (isIntegralLattice_intCast 1)
    isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends g).trans
      ((Homeomorph.prodUnique _ _).trans (Homeomorph.piUnique fun _ ↦ ℂ))

/-- The negative-ray coordinate evaluates the negative standard character monomial. -/
@[simp] theorem negativeRayPointHomeomorph_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    negativeRayPointHomeomorph g x =
      x (MonoidAlgebra.single (ofAdd negativeRayCharacter) 1) := by
  simpa only [negativeRayPointHomeomorph, negativeRayCharacter, Homeomorph.trans_apply,
    Homeomorph.coe_prodUnique, Homeomorph.piUnique_apply,
    coe_coneChartHomeomorph] using coneChartEquiv_fst_apply (isIntegralLattice_intCast 1)
      isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends x default

/-- A negative-ray point is reconstructed from its negative-character coordinate. -/
@[simp] theorem negativeRayPointHomeomorph_symm_apply
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    let _ := affinePointTopology g
    (negativeRayPointHomeomorph g).symm
      (x (MonoidAlgebra.single (ofAdd negativeRayCharacter) 1)) = x := by
  let _ := affinePointTopology g
  rw [← negativeRayPointHomeomorph_apply]
  exact (negativeRayPointHomeomorph g).symm_apply_apply x

private noncomputable def negativeRayNumbering : ToricRay negativeRayCone ≃ Fin 1 :=
  Equiv.ofUnique _ _

/-- The regular-cone complex structure on the negative-ray affine chart. -/
@[instance_reducible]
noncomputable def negativeRayChartedSpace :
    @ChartedSpace ((Fin 1 → ℂ) × (Fin 0 → ℂ)) inferInstance
      (AffineSemigroupComplexPoint
        (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone))
      (affinePointTopology g) :=
  coneChartedSpace (isIntegralLattice_intCast 1)
    isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends
      negativeRayNumbering g

private noncomputable def negativeRayModelEquiv :
    ((Fin 1 → ℂ) × (Fin 0 → ℂ)) ≃L[ℂ] ℂ :=
  (ContinuousLinearEquiv.prodUnique ℂ _ _).trans
    (ContinuousLinearEquiv.piUnique ℂ fun _ ↦ ℂ)

private theorem negativeRayModelEquiv_coneChartAmbient
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    negativeRayModelEquiv (coneChartAmbient (isIntegralLattice_intCast 1)
      isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends
        negativeRayNumbering x) = negativeRayPointHomeomorph g x := by
  rw [negativeRayPointHomeomorph_apply]
  simpa only [negativeRayModelEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodUnique_apply, ContinuousLinearEquiv.piUnique_apply,
    coneChartAmbient_fst_apply,
    Subsingleton.elim (negativeRayNumbering.symm default) default,
    negativeRayCharacter] using
      coneChartEquiv_fst_apply (isIntegralLattice_intCast 1)
        isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends x default

/-- The negative-ray chart is biholomorphic to `ℂ` in its negative-character coordinate. -/
noncomputable def negativeRayPointDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := negativeRayChartedSpace g
    Diffeomorph 𝓘(ℂ, (Fin 1 → ℂ) × (Fin 0 → ℂ)) 𝓘(ℂ, ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone))
      ℂ n := by
  let _ := affinePointTopology g
  let _ := negativeRayChartedSpace g
  refine ⟨(negativeRayPointHomeomorph g).toEquiv, ?_, ?_⟩
  · exact (contMDiff_apply_single (isIntegralLattice_intCast 1)
      isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends
        negativeRayNumbering g negativeRayCharacter n).congr
          fun x ↦ negativeRayPointHomeomorph_apply g x
  · apply (contMDiff_coneChartAmbient_comp_iff (isIntegralLattice_intCast 1)
      isRegularCone_negativeRayCone.toIsToricCone negativeRayBasis_extends
        negativeRayNumbering g).1
    refine negativeRayModelEquiv.symm.toContinuousLinearMap.contMDiff.congr fun z ↦ ?_
    apply negativeRayModelEquiv.injective
    exact (negativeRayModelEquiv_coneChartAmbient g
      ((negativeRayPointHomeomorph g).symm z)).trans
        (((negativeRayPointHomeomorph g).apply_symm_apply z).trans
          (negativeRayModelEquiv.apply_symm_apply z).symm)

/-- The biholomorphic coordinate has the standard character homeomorphism as its underlying map. -/
@[simp] theorem negativeRayPointDiffeomorph_toHomeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := negativeRayChartedSpace g
    (negativeRayPointDiffeomorph g n).toHomeomorph = negativeRayPointHomeomorph g := by
  let _ := affinePointTopology g
  let _ := negativeRayChartedSpace g
  rfl

/-- The biholomorphic negative-ray coordinate evaluates the negative character. -/
@[simp] theorem negativeRayPointDiffeomorph_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    let _ := affinePointTopology g
    let _ := negativeRayChartedSpace g
    negativeRayPointDiffeomorph g n x =
      x (MonoidAlgebra.single (ofAdd negativeRayCharacter) 1) := by
  let _ := affinePointTopology g
  let _ := negativeRayChartedSpace g
  exact negativeRayPointHomeomorph_apply g x

/-- The inverse biholomorphism recovers a point from its negative-character coordinate. -/
@[simp] theorem negativeRayPointDiffeomorph_symm_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    let _ := affinePointTopology g
    let _ := negativeRayChartedSpace g
    (negativeRayPointDiffeomorph g n).symm
      (x (MonoidAlgebra.single (ofAdd negativeRayCharacter) 1)) = x := by
  let _ := affinePointTopology g
  let _ := negativeRayChartedSpace g
  rw [← negativeRayPointDiffeomorph_apply]
  exact (negativeRayPointDiffeomorph g n).symm_apply_apply x

/-- On the common zero-face chart the two affine coordinates multiply to one. -/
theorem projectiveLine_chart_coordinates_mul {sp : ℕ}
    (gp : AddGeneratingFamily (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone) sp)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :
    affineRayPointHomeomorph gp
        (faceAffinePointMap (isIntegralLattice_intCast 1)
          isRegularCone_affineRayCone.salient.bot_isFaceOf x) *
      negativeRayPointHomeomorph g
        (faceAffinePointMap (isIntegralLattice_intCast 1)
          isRegularCone_negativeRayCone.salient.bot_isFaceOf x) = 1 := by
  rw [affineRayPointHomeomorph_apply, negativeRayPointHomeomorph_apply,
    faceAffinePointMap_apply_single, faceAffinePointMap_apply_single]
  rw [← x.apply_single_add]
  have h : (⟨affineRayCharacter, by simp⟩ :
      dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ))) +
      ⟨negativeRayCharacter, by simp⟩ = 0 := by
    apply Subtype.ext
    apply DFunLike.ext
    intro n
    simp [affineRayCharacter_apply, negativeRayCharacter_apply]
  rw [h, ofAdd_zero, ← MonoidAlgebra.one_def, map_one]

/-- The positive maximal cone of the projective-line fan. -/
abbrev projectiveLinePositiveCone : projectiveLineFan.cones :=
  ⟨affineRayCone, affineRayCone_mem_projectiveLineFan⟩

/-- The negative maximal cone of the projective-line fan. -/
abbrev projectiveLineNegativeCone : projectiveLineFan.cones :=
  ⟨negativeRayCone, negativeRayCone_mem_projectiveLineFan⟩

/-- The common zero cone of the projective-line fan. -/
abbrev projectiveLineZeroCone : projectiveLineFan.cones :=
  ⟨⊥, (mem_projectiveLineFan_cones _).2 (Or.inl rfl)⟩

/-- The zero cone is contained in the positive maximal cone of the projective-line fan. -/
theorem projectiveLineZeroCone_le_positiveCone :
    projectiveLineZeroCone ≤ projectiveLinePositiveCone :=
  Subtype.mk_le_mk.mpr bot_le

/-- The zero cone is contained in the negative maximal cone of the projective-line fan. -/
theorem projectiveLineZeroCone_le_negativeCone :
    projectiveLineZeroCone ≤ projectiveLineNegativeCone :=
  Subtype.mk_le_mk.mpr bot_le

private theorem projectiveLinePositiveCone_inf_negativeCone :
    projectiveLinePositiveCone ⊓ projectiveLineNegativeCone = projectiveLineZeroCone :=
  Subtype.ext affineRayCone_inf_negativeRayCone

/-- The positive and negative affine charts cover the analytic projective-line realization. -/
theorem projectiveLine_chart_cover :
    Set.range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
      projectiveLinePositiveCone) ∪
      Set.range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨σ, y, rfl⟩ := projectiveLineFan.exists_analyticAffineChartι_apply_eq
    isRegular_projectiveLineFan x
  rcases (mem_projectiveLineFan_cones σ.1).1 σ.2 with h | h | h
  · have hz : σ ≤ projectiveLinePositiveCone := by
      rcases σ with ⟨σ, _⟩
      apply Subtype.mk_le_mk.mpr
      have hσbot : σ = ⊥ := by simpa only using h
      rw [hσbot]
      exact bot_le
    left
    exact ⟨faceAffinePointMap projectiveLineFan.lattice
      (projectiveLineFan.isFaceOf_of_le projectiveLinePositiveCone.2 σ.2 hz) y,
      projectiveLineFan.analyticAffineChartι_faceAffinePointMap
        isRegular_projectiveLineFan hz y⟩
  · left
    have heq : σ = projectiveLinePositiveCone := Subtype.ext h
    subst σ
    exact ⟨y, rfl⟩
  · right
    have heq : σ = projectiveLineNegativeCone := Subtype.ext h
    subst σ
    exact ⟨y, rfl⟩

/-- The two affine charts meet exactly in the zero-cone chart, the dense complex torus. -/
theorem projectiveLine_chart_overlap :
    Set.range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
      projectiveLinePositiveCone) ∩
      Set.range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone) =
      Set.range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineZeroCone) := by
  rw [projectiveLineFan.range_analyticAffineChartι_inter_range_analyticAffineChartι
    isRegular_projectiveLineFan, projectiveLinePositiveCone_inf_negativeCone]

/-- When points in the two affine charts represent the same point of the analytic realization,
their complex coordinates multiply to one. -/
theorem projectiveLine_chart_coordinates_mul_of_eq
    (x : (projectiveLineFan.analyticAffineChartDiagram).obj projectiveLinePositiveCone)
    (y : (projectiveLineFan.analyticAffineChartDiagram).obj projectiveLineNegativeCone)
    (hxy : projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLinePositiveCone x =
      projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone y) :
    affineRayPointHomeomorph
        (projectiveLineFan.analyticChartGenerators projectiveLinePositiveCone).2 x *
      negativeRayPointHomeomorph
        (projectiveLineFan.analyticChartGenerators projectiveLineNegativeCone).2 y = 1 := by
  have hz : projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
      projectiveLinePositiveCone x ∈
      Set.range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineZeroCone) := by
    rw [← projectiveLine_chart_overlap]
    exact ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
  obtain ⟨z, hz⟩ := hz
  have hpx : faceAffinePointMap projectiveLineFan.lattice
      (projectiveLineFan.isFaceOf_of_le projectiveLinePositiveCone.2
        projectiveLineZeroCone.2 projectiveLineZeroCone_le_positiveCone) z = x :=
    (projectiveLineFan.isOpenEmbedding_analyticAffineChartι
      isRegular_projectiveLineFan projectiveLinePositiveCone).injective <| by
      exact (projectiveLineFan.analyticAffineChartι_faceAffinePointMap
        isRegular_projectiveLineFan projectiveLineZeroCone_le_positiveCone z).trans hz
  have hny : faceAffinePointMap projectiveLineFan.lattice
      (projectiveLineFan.isFaceOf_of_le projectiveLineNegativeCone.2
        projectiveLineZeroCone.2 projectiveLineZeroCone_le_negativeCone) z = y :=
    (projectiveLineFan.isOpenEmbedding_analyticAffineChartι
      isRegular_projectiveLineFan projectiveLineNegativeCone).injective <| by
      exact (projectiveLineFan.analyticAffineChartι_faceAffinePointMap
        isRegular_projectiveLineFan projectiveLineZeroCone_le_negativeCone z).trans (hz.trans hxy)
  have hm := projectiveLine_chart_coordinates_mul
    (gp := (projectiveLineFan.analyticChartGenerators projectiveLinePositiveCone).2)
    (g := (projectiveLineFan.analyticChartGenerators projectiveLineNegativeCone).2) z
  rw [hpx, hny] at hm
  exact hm

namespace Fan

variable (Φ : Fan ((Int.castAddHom ℝ).compLeft (Fin 1))) (hΦ : Φ.IsRegular)
  (hσ : negativeRayCone ∈ Φ.cones)

/-- The negative-ray chart inclusion is a biholomorphism onto its cone open, for the standard
negative-character complex structure. -/
noncomputable def negativeRayChartPartialDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := negativeRayChartedSpace g
    let _ := Φ.analyticChartedSpace hΦ
    PartialDiffeomorph 𝓘(ℂ, (Fin 1 → ℂ) × (Fin 0 → ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone))
      (Φ.analyticRealization hΦ) n :=
  Φ.analyticAffineChartPartialDiffeomorph hΦ ⟨negativeRayCone, hσ⟩
    negativeRayBasis_extends negativeRayNumbering g n

/-- The standard negative-ray chart inclusion is defined everywhere. -/
@[simp] theorem negativeRayChartPartialDiffeomorph_source (n : ℕ∞ω) :
    (Φ.negativeRayChartPartialDiffeomorph g hΦ hσ n).source = Set.univ :=
  Φ.analyticAffineChartPartialDiffeomorph_source hΦ ⟨negativeRayCone, hσ⟩
    negativeRayBasis_extends negativeRayNumbering g n

/-- The target of the standard negative-ray chart inclusion is its cone open. -/
@[simp] theorem negativeRayChartPartialDiffeomorph_target (n : ℕ∞ω) :
    (Φ.negativeRayChartPartialDiffeomorph g hΦ hσ n).target =
      Set.range (Φ.analyticAffineChartι hΦ ⟨negativeRayCone, hσ⟩) :=
  Φ.analyticAffineChartPartialDiffeomorph_target hΦ ⟨negativeRayCone, hσ⟩
    negativeRayBasis_extends negativeRayNumbering g n

/-- The standard negative-ray chart inclusion is the canonical map into the fan realization. -/
@[simp] theorem negativeRayChartPartialDiffeomorph_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    Φ.negativeRayChartPartialDiffeomorph g hΦ hσ n x =
      Φ.analyticAffineChartι hΦ ⟨negativeRayCone, hσ⟩ x :=
  Φ.analyticAffineChartPartialDiffeomorph_apply hΦ ⟨negativeRayCone, hσ⟩
    negativeRayBasis_extends negativeRayNumbering g n x

end Fan

end TauCeti.Toric
