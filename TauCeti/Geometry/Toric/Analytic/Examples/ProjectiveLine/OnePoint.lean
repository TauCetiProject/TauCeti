/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.ProjectiveLine.Atlas
public import TauCeti.Geometry.Toric.Analytic.Examples.ProjectiveLine.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The toric projective line as the one-point compactification of the complex line

The positive affine chart of the standard complete rank-one fan misses precisely the origin
of the negative affine chart. Thus its compact analytic realization is the one-point
compactification of `ℂ`. The comparison sends the positive character coordinate `z` to the
finite point `z`, and the negative character coordinate `w` to `w⁻¹`, with `w = 0` sent to
infinity. These formulas identify the two toric charts with the usual projective-line charts
and supply the chart computations needed to compare their complex structures.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open Set Topology
open scoped OnePoint

namespace TauCeti.Toric

local notation "X" => projectiveLineFan.analyticRealization isRegular_projectiveLineFan
local notation "gp" =>
  Sigma.snd (projectiveLineFan.analyticChartGenerators projectiveLinePositiveCone)
local notation "gn" =>
  Sigma.snd (projectiveLineFan.analyticChartGenerators projectiveLineNegativeCone)
local notation "g₀" =>
  Sigma.snd (projectiveLineFan.analyticChartGenerators projectiveLineZeroCone)
local notation "ιp" => projectiveLineFan.analyticAffineChartι
  isRegular_projectiveLineFan projectiveLinePositiveCone
local notation "ιn" => projectiveLineFan.analyticAffineChartι
  isRegular_projectiveLineFan projectiveLineNegativeCone

-- These instances equip the unbundled affine complex-point types with the topologies needed
-- by the coordinate homeomorphisms and continuity proofs. Using the fan's own chart generators
-- makes them definitionally equal to the corresponding `analyticAffineChartDiagram.obj`
-- topologies, so they also match the domains of the chart inclusions.
private noncomputable instance positiveTopology :
    TopologicalSpace (AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) := affinePointTopology gp

private noncomputable instance negativeTopology :
    TopologicalSpace (AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) := affinePointTopology gn

private noncomputable instance zeroTopology :
    TopologicalSpace (AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) (⊥ : PointedCone ℝ (Fin 1 → ℝ)))) :=
  affinePointTopology g₀

/-- The positive affine chart of the toric projective line, parametrized by its standard
character coordinate. -/
noncomputable def projectiveLinePositiveChartMap (z : ℂ) : X :=
  ιp ((affineRayPointHomeomorph gp).symm z)

/-- The negative affine chart of the toric projective line, parametrized by its negative
standard character coordinate. Its origin is the point at infinity of the positive chart. -/
noncomputable def projectiveLineNegativeChartMap (w : ℂ) : X :=
  ιn ((negativeRayPointHomeomorph gn).symm w)

/-- Reconstructing a positive-chart point from its standard character value gives its image
in the toric projective line. -/
@[simp]
theorem projectiveLinePositiveChartMap_apply_single
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    projectiveLinePositiveChartMap
        (x (MonoidAlgebra.single (Multiplicative.ofAdd affineRayCharacter) 1)) = ιp x := by
  simp [projectiveLinePositiveChartMap]

/-- Reconstructing a negative-chart point from its negative character value gives its image
in the toric projective line. -/
@[simp]
theorem projectiveLineNegativeChartMap_apply_single
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    projectiveLineNegativeChartMap
        (x (MonoidAlgebra.single (Multiplicative.ofAdd negativeRayCharacter) 1)) = ιn x := by
  simp [projectiveLineNegativeChartMap]

/-- The positive complex-line parametrization is an open embedding. -/
theorem isOpenEmbedding_projectiveLinePositiveChartMap :
    IsOpenEmbedding projectiveLinePositiveChartMap :=
  (projectiveLineFan.isOpenEmbedding_analyticAffineChartι isRegular_projectiveLineFan
    projectiveLinePositiveCone).comp (affineRayPointHomeomorph gp).symm.isOpenEmbedding

/-- The negative complex-line parametrization is an open embedding. -/
theorem isOpenEmbedding_projectiveLineNegativeChartMap :
    IsOpenEmbedding projectiveLineNegativeChartMap :=
  (projectiveLineFan.isOpenEmbedding_analyticAffineChartι isRegular_projectiveLineFan
    projectiveLineNegativeCone).comp (negativeRayPointHomeomorph gn).symm.isOpenEmbedding

private theorem range_positiveChartMap : range projectiveLinePositiveChartMap = range ιp := by
  exact (affineRayPointHomeomorph gp).symm.surjective.range_comp _

private theorem range_negativeChartMap : range projectiveLineNegativeChartMap = range ιn := by
  exact (negativeRayPointHomeomorph gn).symm.surjective.range_comp _

/-- A point in the positive chart and a point in the negative chart represent the same global
point exactly when their coordinates multiply to one. In particular neither coordinate can be
zero on the overlap. -/
@[simp]
theorem projectiveLinePositiveChartMap_eq_negativeChartMap_iff (z w : ℂ) :
    projectiveLinePositiveChartMap z = projectiveLineNegativeChartMap w ↔ z * w = 1 := by
  constructor
  · intro h
    simpa only [Homeomorph.apply_symm_apply] using
      projectiveLine_chart_coordinates_mul_of_eq
        ((affineRayPointHomeomorph gp).symm z) ((negativeRayPointHomeomorph gn).symm w) h
  · intro h
    have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one h
    let x := (affineRayZeroFacePointHomeomorph g₀).symm (Units.mk0 z hz)
    -- The fan lattice reduces to `isIntegralLattice_intCast 1`; the two proofs of the
    -- zero-face inclusion agree by proof irrelevance. `zeroTopology` is `affinePointTopology g₀`,
    -- the same topology used by the affine-ray coordinate lemma.
    have hp : affineRayPointHomeomorph gp
        (faceAffinePointMap projectiveLineFan.lattice
          (projectiveLineFan.isFaceOf_of_le projectiveLinePositiveCone.2
            projectiveLineZeroCone.2 projectiveLineZeroCone_le_positiveCone) x) = z :=
      affineRayPointHomeomorph_faceAffinePointMap_symm gp g₀ (Units.mk0 z hz)
    have hn : negativeRayPointHomeomorph gn
        (faceAffinePointMap projectiveLineFan.lattice
          (projectiveLineFan.isFaceOf_of_le projectiveLineNegativeCone.2
            projectiveLineZeroCone.2 projectiveLineZeroCone_le_negativeCone) x) = w := by
      have hm := projectiveLine_chart_coordinates_mul («gp» := gp) (g := gn) x
      rw [hp] at hm
      exact mul_left_cancel₀ hz (hm.trans h.symm)
    have hxp := (affineRayPointHomeomorph gp).injective
      (hp.trans ((affineRayPointHomeomorph gp).apply_symm_apply z).symm)
    have hxn := (negativeRayPointHomeomorph gn).injective
      (hn.trans ((negativeRayPointHomeomorph gn).apply_symm_apply w).symm)
    rw [projectiveLinePositiveChartMap, projectiveLineNegativeChartMap, ← hxp, ← hxn]
    exact projectiveLineFan.analyticAffineChartι_faceAffinePointMap_eq
      isRegular_projectiveLineFan projectiveLineZeroCone_le_positiveCone
      projectiveLineZeroCone_le_negativeCone x

/-- The two complex-line parametrizations cover the toric projective line. -/
theorem projectiveLineChartMap_cover :
    range projectiveLinePositiveChartMap ∪ range projectiveLineNegativeChartMap = univ := by
  rw [range_positiveChartMap, range_negativeChartMap]
  exact projectiveLine_chart_cover

/-- The positive affine chart misses exactly the origin of the negative affine chart. -/
@[simp]
theorem range_projectiveLinePositiveChartMap :
    range projectiveLinePositiveChartMap = {projectiveLineNegativeChartMap 0}ᶜ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩ h
    have hm := (projectiveLinePositiveChartMap_eq_negativeChartMap_iff z 0).1 h
    simp at hm
  · intro hx
    have hcover : x ∈ range projectiveLinePositiveChartMap ∪
        range projectiveLineNegativeChartMap := by rw [projectiveLineChartMap_cover]; trivial
    rcases hcover with hp | ⟨w, rfl⟩
    · exact hp
    · have hw : w ≠ 0 := fun h ↦ hx (congrArg projectiveLineNegativeChartMap h)
      exact ⟨w⁻¹, (projectiveLinePositiveChartMap_eq_negativeChartMap_iff _ _).2
        (inv_mul_cancel₀ hw)⟩

/-- The negative affine chart misses exactly the origin of the positive affine chart. -/
@[simp]
theorem range_projectiveLineNegativeChartMap :
    range projectiveLineNegativeChartMap = {projectiveLinePositiveChartMap 0}ᶜ := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩ h
    have hm := (projectiveLinePositiveChartMap_eq_negativeChartMap_iff 0 w).1 h.symm
    simp at hm
  · intro hx
    have hcover : x ∈ range projectiveLinePositiveChartMap ∪
        range projectiveLineNegativeChartMap := by rw [projectiveLineChartMap_cover]; trivial
    rcases hcover with ⟨z, rfl⟩ | hn
    · have hz : z ≠ 0 := fun h ↦ hx (congrArg projectiveLinePositiveChartMap h)
      exact ⟨z⁻¹, ((projectiveLinePositiveChartMap_eq_negativeChartMap_iff _ _).2
        (mul_inv_cancel₀ hz)).symm⟩
    · exact hn

/-- The toric projective line is homeomorphic to `OnePoint ℂ`. The positive character coordinate
is the finite coordinate, and the origin of the negative chart is infinity. -/
noncomputable def projectiveLineOnePointHomeomorph : X ≃ₜ OnePoint ℂ := by
  letI := compactSpace_projectiveLineFan_analyticRealization
  -- Use Mathlib's one-point compactification constructor `OnePoint.equivOfIsEmbeddingOfRangeEq`.
  exact (OnePoint.equivOfIsEmbeddingOfRangeEq (projectiveLineNegativeChartMap 0)
    projectiveLinePositiveChartMap isOpenEmbedding_projectiveLinePositiveChartMap.isEmbedding
      range_projectiveLinePositiveChartMap).symm

/-- A finite point reconstructs the point of the positive toric chart with that coordinate. -/
@[simp]
theorem projectiveLineOnePointHomeomorph_symm_coe (z : ℂ) :
    projectiveLineOnePointHomeomorph.symm (z : OnePoint ℂ) =
      projectiveLinePositiveChartMap z := by
  simp [projectiveLineOnePointHomeomorph]

/-- Infinity reconstructs the origin of the negative toric chart. -/
@[simp]
theorem projectiveLineOnePointHomeomorph_symm_infty :
    projectiveLineOnePointHomeomorph.symm ∞ = projectiveLineNegativeChartMap 0 := by
  simp [projectiveLineOnePointHomeomorph]

/-- The positive toric chart becomes the finite chart of the one-point compactification. -/
@[simp]
theorem projectiveLineOnePointHomeomorph_positiveChartMap (z : ℂ) :
    projectiveLineOnePointHomeomorph (projectiveLinePositiveChartMap z) = (z : OnePoint ℂ) := by
  rw [← projectiveLineOnePointHomeomorph_symm_coe, Homeomorph.apply_symm_apply]

/-- The negative toric chart becomes the inverted chart, including its origin at infinity. -/
@[simp]
theorem projectiveLineOnePointHomeomorph_negativeChartMap (w : ℂ) :
    projectiveLineOnePointHomeomorph (projectiveLineNegativeChartMap w) =
      if w = 0 then ∞ else ((w⁻¹ : ℂ) : OnePoint ℂ) := by
  classical
  by_cases hw : w = 0
  · subst w
    rw [← projectiveLineOnePointHomeomorph_symm_infty, Homeomorph.apply_symm_apply]
    simp
  · rw [ite_eq_right hw, ← (projectiveLinePositiveChartMap_eq_negativeChartMap_iff _ w).2
      (inv_mul_cancel₀ hw), projectiveLineOnePointHomeomorph_positiveChartMap]

/-- On the positive affine complex-point chart, the comparison evaluates the standard character
monomial and regards its value as a finite point. -/
@[simp]
theorem projectiveLineOnePointHomeomorph_positive_analyticAffineChartι
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    projectiveLineOnePointHomeomorph (ιp x) =
      ((x (MonoidAlgebra.single (Multiplicative.ofAdd affineRayCharacter) 1) : ℂ) :
        OnePoint ℂ) := by
  rw [← projectiveLinePositiveChartMap_apply_single x]
  exact projectiveLineOnePointHomeomorph_positiveChartMap _

/-- On the negative affine complex-point chart, the comparison inverts the negative character
value, sending its zero to infinity. -/
@[simp]
theorem projectiveLineOnePointHomeomorph_negative_analyticAffineChartι
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    projectiveLineOnePointHomeomorph (ιn x) =
      if x (MonoidAlgebra.single (Multiplicative.ofAdd negativeRayCharacter) 1) = 0 then ∞
      else ((x (MonoidAlgebra.single (Multiplicative.ofAdd negativeRayCharacter) 1))⁻¹ : ℂ) := by
  rw [← projectiveLineNegativeChartMap_apply_single x]
  exact projectiveLineOnePointHomeomorph_negativeChartMap _

end TauCeti.Toric
