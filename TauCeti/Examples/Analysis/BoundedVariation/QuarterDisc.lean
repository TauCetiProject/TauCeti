/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.SurfaceArea
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Function.AreaFormula.Circle

/-!
# Check: truncation of the unit square by a ball

In the plane `ℂ`, let `s = (0, 1)²` be the open unit square (`unitSquare`), `x₀ = 0` and `r = 1/2`.
The truncation `s ∩ ball 0 (1/2)` is a quarter disc (`quarterDisc`), and the truncation inequality
`P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + H¹(s ∩ sphere x₀ r)` is an equality here:

* `perimeter_quarterDisc`: `P(s ∩ ball 0 (1/2)) = 1/2 + 1/2 + π/4`, the two radii and the arc;
* `perimeter_unitSquare_ball`: `P(s; ball 0 (1/2)) = 1`, the two edges of the square inside the
  ball;
* `euclideanHausdorffMeasure_unitSquare_inter_sphere`: `H¹(s ∩ sphere 0 (1/2)) = π/4`;
* `perimeter_quarterDisc_eq_add`: the equality, and `perimeter_unitSquare_ball_lt`: the version
  of the inequality without the boundary term fails.

All perimeters are computed from `Convex.perimeter_eq_euclideanHausdorffMeasure_frontier_inter`,
since the square and the quarter disc are convex; the lengths of the radii come from the isometric
embeddings `t ↦ t` and `t ↦ t i` of `ℝ`, that of the arc from
`TauCeti.smul_map_volume_restrict_circleMap`.
-/

public section

noncomputable section

namespace TauCeti.Examples.QuarterDisc

open Complex MeasureTheory Metric Set TopologicalSpace Real
open scoped ENNReal

/-- The open unit square `(0, 1)²` in `ℂ`. -/
def unitSquare : Set ℂ := Ioo 0 1 ×ℂ Ioo 0 1

/-- The quarter disc `(0, 1)² ∩ ball 0 (1/2)`. -/
def quarterDisc : Set ℂ := unitSquare ∩ ball 0 (1 / 2)

/-- The ball `ball 0 (1/2)` as an open set. -/
def halfBall : Opens ℂ := ⟨ball 0 (1 / 2), isOpen_ball⟩

/-! ### Lengths of radii and arcs -/

private theorem isometry_mul_I : Isometry fun t : ℝ ↦ (t : ℂ) * I :=
  Isometry.of_dist_eq fun s t ↦ by
    rw [dist_eq_norm, ← sub_mul, norm_mul, norm_I, mul_one, ← ofReal_sub, norm_real,
      Real.dist_eq, Real.norm_eq_abs]

/-- The one-dimensional Hausdorff measure of a real set placed on the real axis. -/
private theorem euclideanHausdorffMeasure_image_ofReal (S : Set ℝ) :
    μHE[1] (((↑) : ℝ → ℂ) '' S) = volume S := by
  rw [Measure.euclideanHausdorffMeasure_one,
    isometry_ofReal.hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real]

/-- The one-dimensional Hausdorff measure of a real set placed on the imaginary axis. -/
private theorem euclideanHausdorffMeasure_image_mul_I (S : Set ℝ) :
    μHE[1] ((fun t : ℝ ↦ (t : ℂ) * I) '' S) = volume S := by
  rw [Measure.euclideanHausdorffMeasure_one,
    isometry_mul_I.hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real]

/-- Arcs of the circle `sphere 0 (1/2)` by the parameters on a full turn. -/
private theorem euclideanHausdorffMeasure_sphere_inter {T : Set ℂ} (hT : MeasurableSet T) :
    μHE[1] (sphere 0 (1 / 2) ∩ T) =
      ENNReal.ofReal (1 / 2) * volume (Icc 0 (2 * π) ∩ circleMap 0 (1 / 2) ⁻¹' T) := by
  have h := smul_map_volume_restrict_circleMap 0 (1 / 2) 0
  rw [zero_add, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  rw [inter_comm, ← Measure.restrict_apply hT, ← h, smul_apply,
    Measure.map_apply (continuous_circleMap 0 _).measurable hT,
    Measure.restrict_apply (hT.preimage (continuous_circleMap 0 _).measurable), smul_eq_mul,
    inter_comm]

private theorem re_circleMap (θ : ℝ) : (circleMap 0 (1 / 2) θ).re = 1 / 2 * Real.cos θ := by
  rw [circleMap_zero, re_ofReal_mul, exp_ofReal_mul_I_re]

private theorem im_circleMap (θ : ℝ) : (circleMap 0 (1 / 2) θ).im = 1 / 2 * Real.sin θ := by
  rw [circleMap_zero, im_ofReal_mul, exp_ofReal_mul_I_im]

/-- On a full turn `[0, 2π]`, the cosine and sine are both nonnegative only on `[0, π/2]` and at
`2π`. -/
private theorem mem_of_cos_nonneg_of_sin_nonneg {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
    (hc : 0 ≤ Real.cos θ) (hs : 0 ≤ Real.sin θ) : θ ∈ Icc 0 (π / 2) ∪ {2 * π} := by
  by_contra h
  simp only [mem_union, mem_Icc, mem_singleton_iff, not_or, not_and_or, not_le] at h
  have h1 : π / 2 < θ := h.1.resolve_left hθ.1.not_gt
  have h2 : θ < 2 * π := lt_of_le_of_ne hθ.2 h.2
  rcases lt_or_ge θ (π + π / 2) with h3 | h3
  · exact (Real.cos_neg_of_pi_div_two_lt_of_lt h1 h3).not_ge hc
  · have := Real.sin_neg_of_neg_of_neg_pi_lt (x := θ - 2 * π) (by linarith) (by linarith)
    rw [Real.sin_sub_two_pi] at this
    exact this.not_ge hs

/-- The parameters on `[0, 2π]` of the open quarter arc are `(0, π/2)`. -/
private theorem Icc_inter_preimage_circleMap_quadrant :
    Icc 0 (2 * π) ∩ circleMap 0 (1 / 2) ⁻¹' {z | 0 < z.re ∧ 0 < z.im} = Ioo 0 (π / 2) := by
  ext θ
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, re_circleMap, im_circleMap,
    mem_Ioo]
  constructor
  · rintro ⟨hθ, hc, hs⟩
    have hc' : 0 < Real.cos θ := by linarith
    have hs' : 0 < Real.sin θ := by linarith
    rcases mem_of_cos_nonneg_of_sin_nonneg hθ hc'.le hs'.le with h | h
    · refine ⟨lt_of_le_of_ne h.1 ?_, lt_of_le_of_ne h.2 ?_⟩
      · rintro rfl
        simp at hs'
      · rintro rfl
        simp at hc'
    · rw [mem_singleton_iff] at h
      subst h
      simp at hs'
  · rintro ⟨h0, h1⟩
    refine ⟨⟨h0.le, by linarith [pi_pos]⟩, ?_, ?_⟩
    · have := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
      positivity
    · have := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
      positivity

/-- `H¹` of the open quarter arc of `sphere 0 (1/2)` is `π/4`. -/
private theorem euclideanHausdorffMeasure_sphere_inter_quadrant :
    μHE[1] (sphere 0 (1 / 2) ∩ {z : ℂ | 0 < z.re ∧ 0 < z.im}) = ENNReal.ofReal (π / 4) := by
  rw [euclideanHausdorffMeasure_sphere_inter (T := {z : ℂ | 0 < z.re ∧ 0 < z.im})
      ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_const continuous_im)).measurableSet,
    Icc_inter_preimage_circleMap_quadrant, Real.volume_Ioo, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- `H¹` of the closed quarter arc of `sphere 0 (1/2)` is `π/4`. -/
private theorem euclideanHausdorffMeasure_sphere_inter_closedQuadrant :
    μHE[1] (sphere 0 (1 / 2) ∩ {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im}) = ENNReal.ofReal (π / 4) := by
  rw [euclideanHausdorffMeasure_sphere_inter (T := {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im})
    ((isClosed_le continuous_const continuous_re).inter
      (isClosed_le continuous_const continuous_im)).measurableSet]
  have hsub : Icc 0 (2 * π) ∩ circleMap 0 (1 / 2) ⁻¹' {z | 0 ≤ z.re ∧ 0 ≤ z.im} ⊆
      Icc 0 (π / 2) ∪ {2 * π} := by
    rintro θ ⟨hθ, hz⟩
    simp only [mem_preimage, mem_ofPred_eq, re_circleMap, im_circleMap] at hz
    exact mem_of_cos_nonneg_of_sin_nonneg hθ (by linarith) (by linarith)
  have hsup : Ioo 0 (π / 2) ⊆ Icc 0 (2 * π) ∩ circleMap 0 (1 / 2) ⁻¹' {z | 0 ≤ z.re ∧ 0 ≤ z.im} :=
    fun θ hθ ↦ by
      rw [← Icc_inter_preimage_circleMap_quadrant] at hθ
      exact ⟨hθ.1, hθ.2.1.le, hθ.2.2.le⟩
  have hle : volume (Icc 0 (2 * π) ∩ circleMap 0 (1 / 2) ⁻¹' {z | 0 ≤ z.re ∧ 0 ≤ z.im}) ≤
      ENNReal.ofReal (π / 2) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (by simp [Real.volume_Icc]))
  have hge : ENNReal.ofReal (π / 2) ≤
      volume (Icc 0 (2 * π) ∩ circleMap 0 (1 / 2) ⁻¹' {z | 0 ≤ z.re ∧ 0 ≤ z.im}) := by
    simpa [Real.volume_Ioo] using measure_mono (μ := volume) hsup
  rw [le_antisymm hle hge, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-! ### The pieces of the boundary -/

/-- The radius `[0, 1/2)` on the real axis. -/
def radiusRe : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re ∧ z.re < 1 / 2}

/-- The radius `(0, 1/2) i` on the imaginary axis. -/
def radiusIm : Set ℂ := {z | z.re = 0 ∧ 0 < z.im ∧ z.im < 1 / 2}

/-- The closed quarter arc of `sphere 0 (1/2)` in the closed first quadrant. -/
def quarterArc : Set ℂ := sphere 0 (1 / 2) ∩ {z | 0 ≤ z.re ∧ 0 ≤ z.im}

private theorem norm_eq_abs_re {z : ℂ} (h : z.im = 0) : ‖z‖ = |z.re| := by
  conv_lhs => rw [← re_add_im z, h]
  simp

private theorem norm_eq_abs_im {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  conv_lhs => rw [← re_add_im z, h]
  simp

/-- The radius `[0, 1/2)` on the real axis has length `1/2`. -/
theorem euclideanHausdorffMeasure_radiusRe : μHE[1] radiusRe = ENNReal.ofReal (1 / 2) := by
  have : radiusRe = ((↑) : ℝ → ℂ) '' Ico 0 (1 / 2) := by
    ext z
    refine ⟨fun ⟨him, h0, h1⟩ ↦ ⟨z.re, ⟨h0, h1⟩, ext (by simp) (by simp [him])⟩, ?_⟩
    rintro ⟨t, ht, rfl⟩
    simpa [radiusRe] using ht
  rw [this, euclideanHausdorffMeasure_image_ofReal, Real.volume_Ico, sub_zero]

/-- The radius `(0, 1/2) i` on the imaginary axis has length `1/2`. -/
theorem euclideanHausdorffMeasure_radiusIm : μHE[1] radiusIm = ENNReal.ofReal (1 / 2) := by
  have : radiusIm = (fun t : ℝ ↦ (t : ℂ) * I) '' Ioo 0 (1 / 2) := by
    ext z
    refine ⟨fun ⟨hre, h0, h1⟩ ↦ ⟨z.im, ⟨h0, h1⟩, ext (by simp [hre]) (by simp)⟩, ?_⟩
    rintro ⟨t, ht, rfl⟩
    simpa [radiusIm] using ht
  rw [this, euclideanHausdorffMeasure_image_mul_I, Real.volume_Ioo, sub_zero]

/-- The closed quarter arc of `sphere 0 (1/2)` has length `π/4`. -/
theorem euclideanHausdorffMeasure_quarterArc : μHE[1] quarterArc = ENNReal.ofReal (π / 4) :=
  euclideanHausdorffMeasure_sphere_inter_closedQuadrant

/-! ### The quarter disc -/

private theorem mem_quarterDisc {z : ℂ} : z ∈ quarterDisc ↔ 0 < z.re ∧ 0 < z.im ∧ ‖z‖ < 1 / 2 := by
  simp only [quarterDisc, unitSquare, mem_inter_iff, mem_reProdIm, mem_Ioo, mem_ball_zero_iff]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have := abs_re_le_norm z
    have := abs_im_le_norm z
    exact ⟨⟨⟨h1, by linarith [le_abs_self z.re]⟩, h2, by linarith [le_abs_self z.im]⟩, h3⟩

/-- The open unit square is convex. -/
theorem convex_unitSquare : Convex ℝ unitSquare :=
  ((convex_Ioo 0 1).linear_preimage reLm).inter ((convex_Ioo 0 1).linear_preimage imLm)

/-- The open unit square is open. -/
theorem isOpen_unitSquare : IsOpen unitSquare :=
  isOpen_Ioo.reProdIm isOpen_Ioo

/-- The quarter disc is convex. -/
theorem convex_quarterDisc : Convex ℝ quarterDisc :=
  convex_unitSquare.inter (convex_ball 0 _)

/-- The quarter disc is open. -/
theorem isOpen_quarterDisc : IsOpen quarterDisc :=
  isOpen_unitSquare.inter isOpen_ball

private theorem mem_quarterDisc_eighth : (⟨1 / 8, 1 / 8⟩ : ℂ) ∈ quarterDisc := by
  refine mem_quarterDisc.2 ⟨by norm_num, by norm_num, ?_⟩
  refine (norm_le_abs_re_add_abs_im _).trans_lt ?_
  norm_num [abs_of_pos]

/-- The closure of the quarter disc is the closed quarter disc. -/
theorem closure_quarterDisc :
    closure quarterDisc = {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ ‖z‖ ≤ 1 / 2} := by
  refine subset_antisymm (closure_minimal (fun z hz ↦ ?_) ?_) fun z hz ↦ ?_
  · obtain ⟨h1, h2, h3⟩ := mem_quarterDisc.1 hz
    exact ⟨h1.le, h2.le, h3.le⟩
  · exact (isClosed_le continuous_const continuous_re).inter
      ((isClosed_le continuous_const continuous_im).inter
        (isClosed_le continuous_norm continuous_const))
  · obtain ⟨h1, h2, h3⟩ := hz
    refine closure_mono ?_ (segment_subset_closure_openSegment (left_mem_segment ℝ z
      (⟨1 / 8, 1 / 8⟩ : ℂ)))
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    have hw := mem_quarterDisc.1 mem_quarterDisc_eighth
    refine mem_quarterDisc.2 ⟨?_, ?_, ?_⟩
    · simp only [add_re, smul_re, smul_eq_mul]
      nlinarith
    · simp only [add_im, smul_im, smul_eq_mul]
      nlinarith
    · refine (norm_add_le _ _).trans_lt ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
      nlinarith

/-- The boundary of the quarter disc is the union of the two radii and the closed quarter arc,
which are pairwise disjoint. -/
theorem frontier_quarterDisc : frontier quarterDisc = radiusRe ∪ radiusIm ∪ quarterArc := by
  rw [isOpen_quarterDisc.frontier_eq, closure_quarterDisc]
  ext z
  simp only [mem_sdiff, mem_ofPred_eq, mem_quarterDisc, mem_union, radiusRe, radiusIm, quarterArc,
    mem_inter_iff, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h⟩
    rcases h3.lt_or_eq with h3 | h3
    · rcases h1.lt_or_eq with h1 | h1
      · have him : z.im = 0 := le_antisymm (not_lt.1 fun h' ↦ h ⟨h1, h', h3⟩) h2
        rw [norm_eq_abs_re him, abs_of_pos h1] at h3
        exact Or.inl (Or.inl ⟨him, h1.le, h3⟩)
      · rcases h2.lt_or_eq with h2 | h2
        · rw [norm_eq_abs_im h1.symm, abs_of_pos h2] at h3
          exact Or.inl (Or.inr ⟨h1.symm, h2, h3⟩)
        · rw [norm_eq_abs_re h2.symm, ← h1, abs_zero] at h3
          exact Or.inl (Or.inl ⟨h2.symm, h1.le, by linarith⟩)
    · exact Or.inr ⟨h3, h1, h2⟩
  · rintro ((⟨him, h1, h2⟩ | ⟨hre, h1, h2⟩) | ⟨h3, h1, h2⟩)
    · rw [norm_eq_abs_re him, abs_of_nonneg h1]
      exact ⟨⟨h1, him.ge, h2.le⟩, fun h ↦ h.2.1.ne' him⟩
    · rw [norm_eq_abs_im hre, abs_of_pos h1]
      exact ⟨⟨hre.ge, h1.le, h2.le⟩, fun h ↦ h.1.ne' hre⟩
    · exact ⟨⟨h1, h2, h3.le⟩, fun h ↦ h.2.2.ne h3⟩

private theorem measurableSet_radiusIm : MeasurableSet radiusIm :=
  (measurableSet_eq_fun measurable_re measurable_const).inter
    ((measurableSet_lt measurable_const measurable_im).inter
      (measurableSet_lt measurable_im measurable_const))

private theorem measurableSet_quarterArc : MeasurableSet quarterArc :=
  (isClosed_sphere.inter ((isClosed_le continuous_const continuous_re).inter
    (isClosed_le continuous_const continuous_im))).measurableSet

private theorem disjoint_radiusRe_radiusIm : Disjoint radiusRe radiusIm :=
  disjoint_left.2 fun _ h h' ↦ h'.2.1.ne' h.1

private theorem disjoint_radius_quarterArc : Disjoint (radiusRe ∪ radiusIm) quarterArc := by
  refine disjoint_left.2 fun z h h' ↦ ?_
  have h3 : ‖z‖ = 1 / 2 := mem_sphere_zero_iff_norm.1 h'.1
  rcases h with ⟨him, h1, h2⟩ | ⟨hre, h1, h2⟩
  · rw [norm_eq_abs_re him, abs_of_nonneg h1] at h3
    exact h2.ne h3
  · rw [norm_eq_abs_im hre, abs_of_pos h1] at h3
    exact h2.ne h3

private theorem two_le_finrank : 2 ≤ Module.finrank ℝ ℂ := by
  rw [finrank_real_complex]

/-- **The perimeter of the quarter disc** `(0, 1)² ∩ ball 0 (1/2)` is `1/2 + 1/2 + π/4`. -/
theorem perimeter_quarterDisc : perimeter volume ⊤ quarterDisc = ENNReal.ofReal (1 + π / 4) := by
  rw [convex_quarterDisc.perimeter_eq_euclideanHausdorffMeasure_frontier_of_two_le_finrank
      two_le_finrank (by rw [isOpen_quarterDisc.interior_eq]; exact ⟨_, mem_quarterDisc_eighth⟩),
    finrank_real_complex, frontier_quarterDisc,
    measure_union disjoint_radius_quarterArc measurableSet_quarterArc,
    measure_union disjoint_radiusRe_radiusIm measurableSet_radiusIm,
    euclideanHausdorffMeasure_radiusRe, euclideanHausdorffMeasure_radiusIm,
    euclideanHausdorffMeasure_quarterArc, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  norm_num

/-- **The perimeter of the square in the ball** `ball 0 (1/2)` is `1`, the two edges of the
square inside the ball. -/
theorem perimeter_unitSquare_ball : perimeter volume halfBall unitSquare = 1 := by
  rw [convex_unitSquare.perimeter_eq_euclideanHausdorffMeasure_frontier_inter two_le_finrank
      (by rw [isOpen_unitSquare.interior_eq]; exact ⟨_, mem_quarterDisc_eighth.1⟩) halfBall,
    finrank_real_complex]
  have : frontier unitSquare ∩ halfBall = radiusRe ∪ radiusIm := by
    ext z
    simp only [halfBall, Opens.coe_mk, unitSquare, frontier_reProdIm, closure_Ioo zero_ne_one,
      frontier_Ioo zero_lt_one, mem_inter_iff, mem_union, mem_reProdIm, mem_Icc,
      mem_insert_iff, mem_singleton_iff, mem_ball_zero_iff, radiusRe, radiusIm, mem_ofPred_eq]
    have hre := abs_re_le_norm z
    have him := abs_im_le_norm z
    have hre' := le_abs_self z.re
    have him' := le_abs_self z.im
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2 | h2⟩ | ⟨h1 | h1, h2, -⟩, h3⟩
      · rw [norm_eq_abs_re h2, abs_of_nonneg h1] at h3
        exact Or.inl ⟨h2, h1, h3⟩
      · linarith
      · rcases h2.lt_or_eq with h2 | h2
        · rw [norm_eq_abs_im h1, abs_of_pos h2] at h3
          exact Or.inr ⟨h1, h2, h3⟩
        · rw [norm_eq_abs_re h2.symm, h1, abs_zero] at h3
          exact Or.inl ⟨h2.symm, h1.ge, by linarith⟩
      · linarith
    · rintro (⟨h2, h1, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨Or.inl ⟨⟨h1, by linarith⟩, Or.inl h2⟩, ?_⟩
        rwa [norm_eq_abs_re h2, abs_of_nonneg h1]
      · refine ⟨Or.inr ⟨Or.inl h1, h2.le, by linarith⟩, ?_⟩
        rwa [norm_eq_abs_im h1, abs_of_pos h2]
  rw [this, measure_union disjoint_radiusRe_radiusIm measurableSet_radiusIm,
    euclideanHausdorffMeasure_radiusRe, euclideanHausdorffMeasure_radiusIm,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- **The boundary term**: the part of the circle `sphere 0 (1/2)` inside the square is an open
quarter arc, of length `π/4`. -/
theorem euclideanHausdorffMeasure_unitSquare_inter_sphere :
    μHE[1] (unitSquare ∩ sphere 0 (1 / 2)) = ENNReal.ofReal (π / 4) := by
  have : unitSquare ∩ sphere 0 (1 / 2) = sphere 0 (1 / 2) ∩ {z : ℂ | 0 < z.re ∧ 0 < z.im} := by
    ext z
    simp only [unitSquare, mem_inter_iff, mem_reProdIm, mem_Ioo, mem_sphere_zero_iff_norm,
      mem_ofPred_eq]
    have hre := abs_re_le_norm z
    have him := abs_im_le_norm z
    have hre' := le_abs_self z.re
    have him' := le_abs_self z.im
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, h3⟩
      exact ⟨h3, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨⟨h1, by linarith⟩, h2, by linarith⟩, h3⟩
  rw [this, euclideanHausdorffMeasure_sphere_inter_quadrant]

/-- **The truncation inequality is an equality for the square and `ball 0 (1/2)`**:
`P(s ∩ ball 0 (1/2)) = P(s; ball 0 (1/2)) + H¹(s ∩ sphere 0 (1/2))` for `s = (0, 1)²`. -/
theorem perimeter_quarterDisc_eq_add :
    perimeter volume ⊤ quarterDisc =
      perimeter volume halfBall unitSquare + μHE[1] (unitSquare ∩ sphere 0 (1 / 2)) := by
  rw [perimeter_quarterDisc, perimeter_unitSquare_ball,
    euclideanHausdorffMeasure_unitSquare_inter_sphere, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity)]

/-- **The boundary term is needed**: `P(s; ball 0 (1/2)) < P(s ∩ ball 0 (1/2))` for
`s = (0, 1)²`, so the truncation inequality fails without `H¹(s ∩ sphere 0 (1/2))`. -/
theorem perimeter_unitSquare_ball_lt :
    perimeter volume halfBall unitSquare < perimeter volume ⊤ quarterDisc := by
  rw [perimeter_quarterDisc, perimeter_unitSquare_ball, ← ENNReal.ofReal_one,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  linarith [pi_pos]

end TauCeti.Examples.QuarterDisc
