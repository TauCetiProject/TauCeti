/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Convex
public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The Gaussian perimeter of the open quadrant

The open quadrant `C = {x₁ > 0, x₂ > 0}` in `ℝ²` is convex and unbounded, so its Gaussian
perimeter is the Gaussian length of its frontier
(`Convex.gaussianPerimeter_eq_setLIntegral_frontier`). The frontier is the union of the two
boundary half-lines, which meet only at the corner, a point of zero length. The symmetry `x ↦ −x`
shows that each boundary half-line carries half of the Gaussian length `φ(0)` of the line
`{x₁ = 0}` (`TauCeti.gaussianPerimeter_setOf_inner_lt`), and the coordinate swap exchanges the two
half-lines, so `P_γ(C) = φ(0)`, the standard normal density at `0`.
-/

open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal

public noncomputable section

namespace TauCeti.Examples.GaussianQuadrant

/-- The open quadrant `{x₁ > 0, x₂ > 0}` of `ℝ²`. -/
def quadrant : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | 0 < x 0 ∧ 0 < x 1}

/-- The Gaussian density `e^{−W}` of `ℝ²`, with values in `ℝ≥0∞`. -/
private def density (x : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x))

/-- The Gaussian length is invariant under linear isometries: the `μHE[1]`-integral of the
Gaussian density over `e⁻¹(s)` equals that over `s`. -/
private theorem setLIntegral_density_preimage
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (s : Set _) :
    ∫⁻ x in e ⁻¹' s, density x ∂μHE[1] = ∫⁻ x in s, density x ∂μHE[1] := by
  have h := (e.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure 1)
    |>.setLIntegral_comp_preimage_emb e.toHomeomorph.measurableEmbedding density s
  refine Eq.trans ?_ h
  refine lintegral_congr fun x => ?_
  simp [density, e.gaussianWeight_apply]

/-- Two sets of `ℝ²` meeting at most at the origin have intersection of zero `μHE[1]`-measure. -/
private theorem euclideanHausdorffMeasure_inter_eq_zero {s t : Set (EuclideanSpace ℝ (Fin 2))}
    (h : s ∩ t ⊆ {0}) : μHE[1] (s ∩ t) = 0 := by
  have := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2))
    (d := ((1 : ℕ) : ℝ)) (by norm_num)
  exact measure_mono_null h (Measure.euclideanHausdorffMeasure_eq_zero_iff.2 (measure_singleton 0))

/-- The open quadrant is nonempty. -/
theorem quadrant_nonempty : quadrant.Nonempty :=
  ⟨EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1, by simp [quadrant]⟩

/-- The open quadrant is convex. -/
theorem convex_quadrant : Convex ℝ quadrant :=
  (convex_halfSpace_gt (EuclideanSpace.projₗ 0).isLinear 0).inter
    (convex_halfSpace_gt (EuclideanSpace.projₗ 1).isLinear 0)

/-- The open quadrant is open. -/
theorem isOpen_quadrant : IsOpen quadrant :=
  (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)).inter
    (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 1))

/-- The frontier of the open quadrant is the union of the two boundary half-lines. -/
theorem frontier_quadrant :
    frontier quadrant = {x | x 0 = 0 ∧ 0 ≤ x 1} ∪ {x | x 1 = 0 ∧ 0 ≤ x 0} := by
  -- The open quadrant is the interior of the closed quadrant, a convex set, so its frontier is
  -- the frontier of the closed quadrant.
  have hq : quadrant = interior {y : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ y i} := by
    rw [interior_quadrant]
    ext x
    simp [quadrant, Fin.forall_fin_two]
  have hne : (interior {y : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ y i}).Nonempty :=
    hq ▸ quadrant_nonempty
  rw [hq, frontier, interior_interior,
    EuclideanQuadrant.convex.closure_interior_eq_closure_of_nonempty_interior hne, ← frontier,
    _root_.frontier_quadrant]
  ext x
  simp only [mem_ofPred_eq, mem_union, Fin.forall_fin_two, Fin.exists_fin_two]
  grind

/-- The Gaussian length of the line `{x₁ = 0}` is `φ(0)`. -/
private theorem setLIntegral_density_line :
    ∫⁻ x in {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0}, density x ∂μHE[1] =
      ENNReal.ofReal (gaussianPDFReal 0 1 0) := by
  have hν : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 := by simp
  have h := gaussianPerimeter_setOf_inner_lt hν 0
  rw [gaussianPerimeter_def,
    weightedPerimeter_setOf_inner_lt contDiff_gaussianWeight hν 0 ⊤] at h
  simpa [density, finrank_euclideanSpace_fin, EuclideanSpace.inner_single_right] using h

/-- A point of `ℝ²` with both coordinates zero is the origin. -/
private theorem eq_zero_of_apply_eq_zero {x : EuclideanSpace ℝ (Fin 2)} (h0 : x 0 = 0)
    (h1 : x 1 = 0) : x = 0 := by
  ext i
  fin_cases i <;> simp [h0, h1]

/-- The upper half-line `{x₁ = 0, x₂ ≥ 0}` has Gaussian length `φ(0)/2`: twice its Gaussian
length is `φ(0)`. -/
private theorem setLIntegral_density_halfLine_add_self :
    ∫⁻ x in {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0 ∧ 0 ≤ x 1}, density x ∂μHE[1] +
        ∫⁻ x in {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0 ∧ 0 ≤ x 1}, density x ∂μHE[1] =
      ENNReal.ofReal (gaussianPDFReal 0 1 0) := by
  -- The symmetry `x ↦ −x` carries the upper half `A` of the line onto the lower half `A'`, and
  -- the two halves meet only at the origin.
  set A : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 = 0 ∧ 0 ≤ x 1}
  set A' : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 = 0 ∧ x 1 ≤ 0}
  have hA'm : MeasurableSet A' :=
    ((isClosed_eq (PiLp.continuous_apply 2 _ 0) continuous_const).inter
      (isClosed_le (PiLp.continuous_apply 2 _ 1) continuous_const)).measurableSet
  have hneg : (LinearIsometryEquiv.neg ℝ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] _) ⁻¹' A' = A := by
    ext x
    simp [A, A']
  have hA' : ∫⁻ x in A', density x ∂μHE[1] = ∫⁻ x in A, density x ∂μHE[1] := by
    rw [← hneg]
    exact (setLIntegral_density_preimage (LinearIsometryEquiv.neg ℝ) A').symm
  have hline : {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0} = A ∪ A' := by
    ext x
    simp only [A, A', mem_ofPred_eq, mem_union]
    constructor
    · intro h
      rcases le_total 0 (x 1) with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (h | h) <;> exact h.1
  rw [← setLIntegral_density_line, hline, Measure.restrict_union₀
      (euclideanHausdorffMeasure_inter_eq_zero fun x (hx : x ∈ A ∩ A') =>
        eq_zero_of_apply_eq_zero hx.1.1 (le_antisymm hx.2.2 hx.1.2))
      hA'm.nullMeasurableSet,
    lintegral_add_measure, hA']

/-- **The Gaussian perimeter of the open quadrant** of `ℝ²` is `φ(0)`, the standard normal
density at `0`: each of the two boundary half-lines has Gaussian length `φ(0)/2`. -/
theorem gaussianPerimeter_quadrant :
    gaussianPerimeter quadrant = ENNReal.ofReal (gaussianPDFReal 0 1 0) := by
  have hn : 2 ≤ finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  have hne : (interior quadrant).Nonempty := isOpen_quadrant.interior_eq.symm ▸ quadrant_nonempty
  rw [convex_quadrant.gaussianPerimeter_eq_setLIntegral_frontier hn hne, frontier_quadrant,
    finrank_euclideanSpace_fin]
  set A : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 = 0 ∧ 0 ≤ x 1}
  set B : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 1 = 0 ∧ 0 ≤ x 0}
  have hBm : MeasurableSet B :=
    ((isClosed_eq (PiLp.continuous_apply 2 _ 1) continuous_const).inter
      (isClosed_le continuous_const (PiLp.continuous_apply 2 _ 0))).measurableSet
  -- The swap of coordinates carries `B` onto `A`.
  let σ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)
  have hσ : σ ⁻¹' B = A := by
    ext x
    simp [σ, A, B, LinearIsometryEquiv.piLpCongrLeft_apply]
  have hB : ∫⁻ x in B, density x ∂μHE[1] = ∫⁻ x in A, density x ∂μHE[1] := by
    rw [← hσ]
    exact (setLIntegral_density_preimage σ B).symm
  -- Fold the integrand `ENNReal.ofReal (Real.exp (-gaussianWeight _ x))` into `density x` (by
  -- definition) and the frontier into `A ∪ B`, to match the helper lemmas above.
  change ∫⁻ x in A ∪ B, density x ∂μHE[1] = _
  rw [Measure.restrict_union₀ (euclideanHausdorffMeasure_inter_eq_zero
      fun x (hx : x ∈ A ∩ B) => eq_zero_of_apply_eq_zero hx.1.1 hx.2.1) hBm.nullMeasurableSet,
    lintegral_add_measure, hB, setLIntegral_density_halfLine_add_self]

end TauCeti.Examples.GaussianQuadrant
