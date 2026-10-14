/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Toric.Analytic.Examples.ProjectiveLine.Atlas

/-!
# Biholomorphic affine charts of the toric projective line

The positive and negative character coordinates give biholomorphisms from `ℂ` onto the two
maximal cone opens of the analytic realization of the projective-line fan. They cover the
realization, and their transition is inversion on the overlap. These charts allow comparison
with the usual affine and inverted charts of the Riemann sphere in the complex category, not
just topologically.

The constructions compose `affineRayPointDiffeomorph` and `negativeRayPointDiffeomorph` with
`Fan.analyticAffineChartPartialDiffeomorph`, through the standard ray-chart inclusions. Thus
they use the existing regular-cone complex structures and the glued fan atlas, rather than
defining a new atlas on the realization.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Toric

local notation "P" => projectiveLineFan.analyticRealization isRegular_projectiveLineFan
local notation "I" => 𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ)
local notation "gp" => Sigma.snd
  (projectiveLineFan.analyticChartGenerators projectiveLinePositiveCone)
local notation "gn" => Sigma.snd
  (projectiveLineFan.analyticChartGenerators projectiveLineNegativeCone)

/-- The positive character parametrizes the positive cone open biholomorphically by `ℂ`. -/
noncomputable def projectiveLinePositivePartialDiffeomorph (n : ℕ∞ω) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    PartialDiffeomorph 𝓘(ℂ, ℂ) I ℂ P n :=
  let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  let _ := affinePointTopology gp
  let _ := affineRayChartedSpace gp
  (affineRayPointDiffeomorph gp n).symm.toPartialDiffeomorph.trans
    (projectiveLineFan.affineRayChartPartialDiffeomorph gp isRegular_projectiveLineFan
      affineRayCone_mem_projectiveLineFan n)

/-- The negative character parametrizes the negative cone open biholomorphically by `ℂ`. -/
noncomputable def projectiveLineNegativePartialDiffeomorph (n : ℕ∞ω) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    PartialDiffeomorph 𝓘(ℂ, ℂ) I ℂ P n :=
  let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  let _ := affinePointTopology gn
  let _ := negativeRayChartedSpace gn
  (negativeRayPointDiffeomorph gn n).symm.toPartialDiffeomorph.trans
    (projectiveLineFan.negativeRayChartPartialDiffeomorph gn isRegular_projectiveLineFan
      negativeRayCone_mem_projectiveLineFan n)

/-- The positive parametrization is defined on the whole complex line. -/
@[simp] theorem projectiveLinePositivePartialDiffeomorph_source (n : ℕ∞ω) :
    (projectiveLinePositivePartialDiffeomorph n).source = univ := by
  simp [projectiveLinePositivePartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_source]

/-- The negative parametrization is defined on the whole complex line. -/
@[simp] theorem projectiveLineNegativePartialDiffeomorph_source (n : ℕ∞ω) :
    (projectiveLineNegativePartialDiffeomorph n).source = univ := by
  simp [projectiveLineNegativePartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_source]

/-- The positive parametrization maps onto exactly the positive maximal cone open. -/
@[simp] theorem projectiveLinePositivePartialDiffeomorph_target (n : ℕ∞ω) :
    (projectiveLinePositivePartialDiffeomorph n).target =
      range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLinePositiveCone) := by
  simp [projectiveLinePositivePartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_target]

/-- The negative parametrization maps onto exactly the negative maximal cone open. -/
@[simp] theorem projectiveLineNegativePartialDiffeomorph_target (n : ℕ∞ω) :
    (projectiveLineNegativePartialDiffeomorph n).target =
      range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone) := by
  simp [projectiveLineNegativePartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_target]

/-- The positive parametrization inserts the point with the specified positive-character value. -/
@[simp] theorem projectiveLinePositivePartialDiffeomorph_apply (n : ℕ∞ω) (z : ℂ) :
    let _ := affinePointTopology gp
    projectiveLinePositivePartialDiffeomorph n z =
      projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLinePositiveCone ((affineRayPointHomeomorph gp).symm z) := by
  let _ := affinePointTopology gp
  simp [projectiveLinePositivePartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_apply,
    ← Diffeomorph.coe_toHomeomorph_symm]

/-- The negative parametrization inserts the point with the specified negative-character value. -/
@[simp] theorem projectiveLineNegativePartialDiffeomorph_apply (n : ℕ∞ω) (z : ℂ) :
    let _ := affinePointTopology gn
    projectiveLineNegativePartialDiffeomorph n z =
      projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone ((negativeRayPointHomeomorph gn).symm z) := by
  let _ := affinePointTopology gn
  simp [projectiveLineNegativePartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_apply,
    ← Diffeomorph.coe_toHomeomorph_symm]

/-- On the positive cone open, the inverse chart evaluates the positive character monomial. -/
@[simp] theorem projectiveLinePositivePartialDiffeomorph_symm_analyticAffineChartι (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    (projectiveLinePositivePartialDiffeomorph n).toPartialEquiv.symm
      (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLinePositiveCone x) =
      x (MonoidAlgebra.single (Multiplicative.ofAdd affineRayCharacter) 1) := by
  intro _
  let _ := affinePointTopology gp
  have hx := (projectiveLinePositivePartialDiffeomorph n).left_inv
    (x := affineRayPointHomeomorph gp x) (by simp)
  rw [projectiveLinePositivePartialDiffeomorph_apply, Homeomorph.symm_apply_apply] at hx
  exact hx.trans (affineRayPointHomeomorph_apply gp x)

/-- On the negative cone open, the inverse chart evaluates the negative character monomial. -/
@[simp] theorem projectiveLineNegativePartialDiffeomorph_symm_analyticAffineChartι (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone)) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    (projectiveLineNegativePartialDiffeomorph n).toPartialEquiv.symm
      (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone x) =
      x (MonoidAlgebra.single (Multiplicative.ofAdd negativeRayCharacter) 1) := by
  intro _
  let _ := affinePointTopology gn
  have hx := (projectiveLineNegativePartialDiffeomorph n).left_inv
    (x := negativeRayPointHomeomorph gn x) (by simp)
  rw [projectiveLineNegativePartialDiffeomorph_apply, Homeomorph.symm_apply_apply] at hx
  exact hx.trans (negativeRayPointHomeomorph_apply gn x)

/-- The positive parametrization is a local biholomorphism everywhere, including at zero. -/
theorem isLocalDiffeomorph_projectiveLinePositivePartialDiffeomorph (n : ℕ∞ω) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    IsLocalDiffeomorph 𝓘(ℂ, ℂ) I n (projectiveLinePositivePartialDiffeomorph n) := by
  intro _ z
  exact (projectiveLinePositivePartialDiffeomorph n).isLocalDiffeomorphAt _ _ _ (by simp)

/-- The negative parametrization is a local biholomorphism everywhere, including at zero. -/
theorem isLocalDiffeomorph_projectiveLineNegativePartialDiffeomorph (n : ℕ∞ω) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    IsLocalDiffeomorph 𝓘(ℂ, ℂ) I n (projectiveLineNegativePartialDiffeomorph n) := by
  intro _ z
  exact (projectiveLineNegativePartialDiffeomorph n).isLocalDiffeomorphAt _ _ _ (by simp)

/-- The targets of the two biholomorphic affine parametrizations cover the realization. -/
theorem projectiveLinePartialDiffeomorph_target_cover (n : ℕ∞ω) :
    (projectiveLinePositivePartialDiffeomorph n).target ∪
      (projectiveLineNegativePartialDiffeomorph n).target = univ := by
  simpa only [projectiveLinePositivePartialDiffeomorph_target,
    projectiveLineNegativePartialDiffeomorph_target] using projectiveLine_chart_cover

/-- On the actual overlap, the negative chart coordinate is the reciprocal positive coordinate.
No transition is asserted outside the negative chart's target. -/
theorem projectiveLinePartialDiffeomorph_transition (n : ℕ∞ω) (z : ℂ)
    (hz : projectiveLinePositivePartialDiffeomorph n z ∈
      (projectiveLineNegativePartialDiffeomorph n).target) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    (projectiveLineNegativePartialDiffeomorph n).toPartialEquiv.symm
      (projectiveLinePositivePartialDiffeomorph n z) = z⁻¹ := by
  intro _
  let _ := affinePointTopology gp
  let _ := affinePointTopology gn
  rw [projectiveLineNegativePartialDiffeomorph_target] at hz
  obtain ⟨y, hy⟩ := hz
  have hxy := (projectiveLinePositivePartialDiffeomorph_apply n z).symm.trans hy.symm
  have ht := eq_inv_of_mul_eq_one_right <|
    projectiveLine_chart_coordinates_mul_of_eq ((affineRayPointHomeomorph gp).symm z) y hxy
  rw [Homeomorph.apply_symm_apply] at ht
  rw [← hy]
  exact (projectiveLineNegativePartialDiffeomorph_symm_analyticAffineChartι n y).trans
    ((negativeRayPointHomeomorph_apply gn y).symm.trans ht)

/-- On the actual overlap in the reverse direction, the positive coordinate is the reciprocal
negative coordinate. -/
theorem projectiveLinePartialDiffeomorph_transition_symm (n : ℕ∞ω) (z : ℂ)
    (hz : projectiveLineNegativePartialDiffeomorph n z ∈
      (projectiveLinePositivePartialDiffeomorph n).target) :
    let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    (projectiveLinePositivePartialDiffeomorph n).toPartialEquiv.symm
      (projectiveLineNegativePartialDiffeomorph n z) = z⁻¹ := by
  intro _
  let _ := affinePointTopology gp
  let _ := affinePointTopology gn
  rw [projectiveLinePositivePartialDiffeomorph_target] at hz
  obtain ⟨x, hx⟩ := hz
  have hxy := hx.trans (projectiveLineNegativePartialDiffeomorph_apply n z)
  have ht := eq_inv_of_mul_eq_one_right <|
    projectiveLine_chart_coordinates_mul_of_eq x ((negativeRayPointHomeomorph gn).symm z) hxy
  rw [Homeomorph.apply_symm_apply] at ht
  rw [← hx]
  exact (projectiveLinePositivePartialDiffeomorph_symm_analyticAffineChartι n x).trans
    ((affineRayPointHomeomorph_apply gp x).symm.trans (by rw [ht, inv_inv]))

/-- A positive chart point lies in the negative chart exactly when its coordinate is nonzero. -/
@[simp↓] theorem projectiveLinePositivePartialDiffeomorph_mem_negative_target
    (n : ℕ∞ω) (z : ℂ) :
    projectiveLinePositivePartialDiffeomorph n z ∈
      (projectiveLineNegativePartialDiffeomorph n).target ↔ z ≠ 0 := by
  let _ := affinePointTopology gp
  let g₀ := (projectiveLineFan.analyticChartGenerators projectiveLineZeroCone).2
  let _ := affinePointTopology g₀
  rw [projectiveLinePositivePartialDiffeomorph_apply,
    projectiveLineNegativePartialDiffeomorph_target]
  have hoverlap : projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
      projectiveLinePositiveCone ((affineRayPointHomeomorph gp).symm z) ∈
      range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineNegativeCone) ↔
      projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLinePositiveCone ((affineRayPointHomeomorph gp).symm z) ∈
      range (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
        projectiveLineZeroCone) := by
    rw [← projectiveLine_chart_overlap, mem_inter_iff]
    exact ⟨fun h ↦ ⟨⟨_, rfl⟩, h⟩, And.right⟩
  rw [hoverlap]
  constructor
  · rintro ⟨w, hw⟩
    have hwp := (projectiveLineFan.isOpenEmbedding_analyticAffineChartι
      isRegular_projectiveLineFan projectiveLinePositiveCone).injective
        ((projectiveLineFan.analyticAffineChartι_faceAffinePointMap
          isRegular_projectiveLineFan projectiveLineZeroCone_le_positiveCone w).trans hw)
    have hcoord := affineRayPointHomeomorph_faceAffinePointMap gp g₀ w
    rw [hwp, Homeomorph.apply_symm_apply] at hcoord
    exact hcoord.symm ▸ Units.ne_zero (affineRayZeroFacePointHomeomorph g₀ w)
  · intro hz
    let w := (affineRayZeroFacePointHomeomorph g₀).symm (Units.mk0 z hz)
    have hwp : faceAffinePointMap projectiveLineFan.lattice
        (projectiveLineFan.isFaceOf_of_le projectiveLinePositiveCone.2
          projectiveLineZeroCone.2 projectiveLineZeroCone_le_positiveCone) w =
        (affineRayPointHomeomorph gp).symm z := by
      apply (affineRayPointHomeomorph gp).injective
      rw [Homeomorph.apply_symm_apply]
      exact affineRayPointHomeomorph_faceAffinePointMap_symm gp g₀ (Units.mk0 z hz)
    exact ⟨w, (projectiveLineFan.analyticAffineChartι_faceAffinePointMap
      isRegular_projectiveLineFan projectiveLineZeroCone_le_positiveCone w).symm.trans (congrArg
        (projectiveLineFan.analyticAffineChartι isRegular_projectiveLineFan
          projectiveLinePositiveCone) hwp)⟩

/-- A negative chart point lies in the positive chart exactly when its coordinate is nonzero. -/
@[simp↓] theorem projectiveLineNegativePartialDiffeomorph_mem_positive_target
    (n : ℕ∞ω) (z : ℂ) :
    projectiveLineNegativePartialDiffeomorph n z ∈
      (projectiveLinePositivePartialDiffeomorph n).target ↔ z ≠ 0 := by
  let _ := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  constructor
  · intro hz
    have hcoord := (projectiveLinePositivePartialDiffeomorph_mem_negative_target n _).1
      (by rw [(projectiveLinePositivePartialDiffeomorph n).right_inv hz]
          exact (projectiveLineNegativePartialDiffeomorph n).map_source (by simp))
    rwa [projectiveLinePartialDiffeomorph_transition_symm n z hz, ne_eq,
      inv_eq_zero] at hcoord
  · intro hz
    have hoverlap := (projectiveLinePositivePartialDiffeomorph_mem_negative_target n
      z⁻¹).2 (inv_ne_zero hz)
    have hcoord := projectiveLinePartialDiffeomorph_transition n z⁻¹ hoverlap
    rw [inv_inv] at hcoord
    have hpoint := (projectiveLineNegativePartialDiffeomorph n).right_inv hoverlap
    rw [hcoord] at hpoint
    rw [hpoint]
    exact (projectiveLinePositivePartialDiffeomorph n).map_source (by simp)

end TauCeti.Toric
