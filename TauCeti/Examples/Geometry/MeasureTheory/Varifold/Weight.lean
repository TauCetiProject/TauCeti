/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.Euclidean
public import TauCeti.Geometry.MeasureTheory.Varifold.LineVarifold
public import TauCeti.Topology.Algebra.Module.Trace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Checks for the weight of a varifold

Examples in the plane `ℝ² = EuclideanSpace ℝ (Fin 2)` of `1`-varifolds on `W = ℝ²` in the
Euclidean form `Measure (W × G(ℝ², 1))`. The line `ℝ e₀` (the `x`-axis), parametrized by Lebesgue
measure, is lifted with the horizontal plane `ℝ e₀` (`horizontalLift`) and with the vertical
plane `ℝ e₁` (`Euclidean.verticalLift 0 (e 0) (e 1) _`).

* *The weight does not determine the varifold.* The two lifts have the same weight
  (`weight_horizontalLift_eq_weight_verticalLift`) but are different
  (`horizontalLift_ne_verticalLift`): the test function `χ(x) tr(P ∘ diag(1, 0))`, where
  `diag(1, 0)` is the projection onto `ℝ e₀`, integrates to `∫ χ(t e₀) dt` against the first and
  to `0` against the second (`integral_mul_traceDiag_horizontalLift`,
  `integral_mul_traceDiag_verticalLift`).
* *Mass on the unit disc.* The horizontal lift has mass `2` on the open unit disc
  (`weight_horizontalLift_ball`).
* *The support of a restriction is relative.* The horizontal lift of the segment `[0, 1] e₀`
  (`segmentLift`), restricted to the open disc `W'` of radius `½` about `0`, has support
  `[0, ½) e₀ = spt ‖V‖ ∩ W'` relative to `W'`, a set that is not closed in `ℝ²`: its closure
  adds the point `½ e₀` outside `W'` (`support_restrictOpens_segmentLift`).
* *Dirac varifolds and trivial restrictions.* `spt ‖δ_{(x, P)}‖ = {x}`
  (`support_weight_dirac`), `V⌞∅ = 0` and `V⌞W = V` (`restrict_preimage_empty`,
  `restrict_preimage_opens`).
-/

open MeasureTheory Set TopologicalSpace Metric Module Euclidean
open scoped ENNReal

public noncomputable section

namespace TauCeti.Examples.VarifoldWeight

/-! ### Dirac varifolds and trivial restrictions -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {k : ℕ}

/-- The weight of the Dirac varifold `δ_{(x, P)}` has support `{x}`. -/
theorem support_weight_dirac [OpensMeasurableSpace E] {W : Opens E}
    (p : W × grassmannian ℝ E k) : (weight (Measure.dirac p)).support = {(p.1 : E)} := by
  simp

/-- Restricting a varifold to the pairs over the empty set gives `0`. -/
theorem restrict_preimage_empty {W : Opens E} (V : Measure (W × grassmannian ℝ E k)) :
    V.restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' (∅ : Set E))) = 0 := by
  simp

/-- Restricting a varifold on `W` to the pairs over `W` does nothing. -/
theorem restrict_preimage_opens {W : Opens E} (V : Measure (W × grassmannian ℝ E k)) :
    V.restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' (W : Set E))) = V := by
  rw [Subtype.coe_preimage_self, preimage_univ, Measure.restrict_univ]

end General

/-! ### The horizontal and the vertical lift of the `x`-axis -/

/-- The plane `ℝ²`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The `i`-th standard basis vector of `ℝ²`. -/
abbrev e (i : Fin 2) : Plane :=
  EuclideanSpace.single i 1

/-- The standard basis vectors are nonzero. -/
theorem e_ne_zero (i : Fin 2) : e i ≠ 0 := by
  simp [e]

/-- The standard basis vectors are unit vectors. -/
theorem norm_e (i : Fin 2) : ‖e i‖ = 1 := by
  simp [e]

/-- The line `ℝ eᵢ` as a point of `G(ℝ², 1)`, the orthogonal projection onto it. -/
abbrev line (i : Fin 2) : grassmannian ℝ Plane 1 :=
  grassmannian.spanLine ℝ (e i) (e_ne_zero i)

/-- The value of `line i` is the orthogonal projection onto `ℝ eᵢ`. -/
theorem coe_line (i : Fin 2) : (line i : Plane →L[ℝ] Plane) =
    (ℝ ∙ e i).starProjection :=
  grassmannian.coe_spanLine _ _

/-- The horizontal lift of the `x`-axis: the line `ℝ e₀`, parametrized by Lebesgue measure, with
the horizontal plane `ℝ e₀` at every point. -/
def horizontalLift : Measure ((⊤ : Opens Plane) ×
    grassmannian ℝ Plane 1) :=
  verticalLift 0 (e 0) (e 0) (e_ne_zero 0)

/-- The two lifts have the same weight. -/
theorem weight_horizontalLift_eq_weight_verticalLift :
    weight horizontalLift = weight (verticalLift 0 (e 0) (e 1) (e_ne_zero 1)) := by
  rw [horizontalLift, verticalLift_def, verticalLift_def, weight_lineVarifold,
    weight_lineVarifold]

/-- The two lines are different points of `G(ℝ², 1)`. -/
theorem line_zero_ne_line_one : line 0 ≠ line 1 := by
  intro h
  have h' := congrArg (fun P : grassmannian ℝ Plane 1 => (P : Plane →L[ℝ] Plane) (e 0))
    h
  simp only [coe_line] at h'
  rw [Submodule.starProjection_eq_self_iff.2 (Submodule.mem_span_singleton_self _),
    Submodule.starProjection_singleton] at h'
  have := congrArg (fun v : Plane => v 0) h'
  simp [e] at this

/-- **The weight does not determine the varifold**: the horizontal and the vertical lift of the
`x`-axis have the same weight but are different. -/
theorem horizontalLift_ne_verticalLift :
    horizontalLift ≠ verticalLift 0 (e 0) (e 1) (e_ne_zero 1) := by
  intro h
  have hS : MeasurableSet (univ ×ˢ {line 1} : Set ((⊤ : Opens Plane) ×
      grassmannian ℝ Plane 1)) :=
    MeasurableSet.univ.prod (measurableSet_singleton _)
  have h' := congrArg (fun V : Measure _ => V (univ ×ˢ {line 1})) h
  simp only [horizontalLift, verticalLift_def, lineVarifold_apply _ _ _ hS] at h'
  have h₀ : lineVarifoldParam 0 (e 0) (line 0) ⁻¹' (univ ×ˢ {line 1}) = ∅ := by
    ext t
    simp [line_zero_ne_line_one]
  have h₁ : lineVarifoldParam 0 (e 0) (line 1) ⁻¹' (univ ×ˢ {line 1}) = univ := by
    ext t
    simp
  rw [h₀, h₁, measure_empty, Real.volume_univ] at h'
  exact ENNReal.zero_ne_top h'

/-- `tr (P ∘ diag(1, 0))`, where `diag(1, 0)` is the projection onto `ℝ e₀`. -/
def traceDiag (P : Plane →L[ℝ] Plane) : ℝ :=
  TauCeti.traceCLM ℝ Plane (P ∘L (line 0 : Plane →L[ℝ] Plane))

/-- `tr (P ∘ diag(1, 0))` for the horizontal plane `P = ℝ e₀` is `1`. -/
theorem traceDiag_line_zero : traceDiag (line 0) = 1 := by
  have hidem := (isStarProjection_starProjection (U := ℝ ∙ e 0)).isIdempotentElem
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def] at hidem
  rw [traceDiag, coe_line, hidem, TauCeti.traceCLM_apply, ← coe_line]
  exact_mod_cast grassmannian.trace_eq (line 0).property

/-- `tr (P ∘ diag(1, 0))` for the vertical plane `P = ℝ e₁` is `0`. -/
theorem traceDiag_line_one : traceDiag (line 1) = 0 := by
  have h : (ℝ ∙ e 1).starProjection ∘L (ℝ ∙ e 0).starProjection = 0 :=
    Submodule.starProjection_comp_starProjection_eq_zero_iff.2
      (Submodule.isOrtho_span.2 fun u hu v hv => by
        rw [mem_singleton_iff.1 hu, mem_singleton_iff.1 hv]
        simp [e, EuclideanSpace.inner_single_left])
  rw [traceDiag, coe_line, coe_line, h, map_zero]

/-- `P ↦ tr (P ∘ diag(1, 0))` is continuous. -/
theorem continuous_traceDiag : Continuous traceDiag :=
  (TauCeti.traceCLM ℝ Plane).continuous.comp (continuous_id.clm_comp continuous_const)

/-- The test function `χ(x) tr(P ∘ diag(1, 0))` is continuous for continuous `χ`. -/
theorem continuous_mul_traceDiag {χ : Plane → ℝ} (hχ : Continuous χ) :
    Continuous fun z : (⊤ : Opens Plane) × grassmannian ℝ Plane 1 =>
      χ z.1 * traceDiag (z.2 : Plane →L[ℝ] Plane) :=
  (hχ.comp (continuous_subtypeVal.comp continuous_fst)).mul
    (continuous_traceDiag.comp (continuous_subtypeVal.comp continuous_snd))

/-- Against the horizontal lift, `χ(x) tr(P ∘ diag(1, 0))` integrates to `∫ χ(t e₀) dt`. -/
theorem integral_mul_traceDiag_horizontalLift {χ : Plane → ℝ} (hχ : Continuous χ) :
    ∫ z, χ z.1 * traceDiag (z.2 : Plane →L[ℝ] Plane) ∂horizontalLift = ∫ t : ℝ, χ (t • e 0) := by
  rw [horizontalLift, verticalLift_def, integral_lineVarifold _ _ _
    (continuous_mul_traceDiag hχ).aestronglyMeasurable]
  simp only [lineVarifoldParam_apply, traceDiag_line_zero, mul_one, zero_add]

/-- Against the vertical lift, `χ(x) tr(P ∘ diag(1, 0))` integrates to `0`. -/
theorem integral_mul_traceDiag_verticalLift {χ : Plane → ℝ} (hχ : Continuous χ) :
    ∫ z, χ z.1 * traceDiag (z.2 : Plane →L[ℝ] Plane) ∂verticalLift 0 (e 0) (e 1) (e_ne_zero 1) =
      0 := by
  rw [verticalLift_def, integral_lineVarifold _ _ _
    (continuous_mul_traceDiag hχ).aestronglyMeasurable]
  simp only [lineVarifoldParam_apply, traceDiag_line_one, mul_zero, integral_zero]

/-- **The horizontal lift of the `x`-axis has mass `2` on the open unit disc.** -/
theorem weight_horizontalLift_ball : weight horizontalLift (ball 0 1) = 2 := by
  rw [horizontalLift, verticalLift_def, weight_lineVarifold,
    Measure.map_apply (by fun_prop) measurableSet_ball]
  have : (fun t : ℝ => (0 : Plane) + t • e 0) ⁻¹' ball 0 1 = ball 0 1 := by
    ext t
    simp [norm_smul]
  rw [this, Real.volume_ball]
  norm_num

/-! ### The support of a restriction -/

/-- The map `t ↦ t e₀` parametrizing the `x`-axis. -/
def axisMap (t : ℝ) : Plane :=
  t • e 0

/-- Unfolding lemma for `axisMap`. -/
theorem axisMap_def (t : ℝ) : axisMap t = t • e 0 :=
  (rfl)

/-- `‖t e₀‖ = |t|`. -/
theorem norm_axisMap (t : ℝ) : ‖axisMap t‖ = |t| := by
  simp [axisMap_def, norm_smul]

/-- The `x`-axis is a closed embedding of `ℝ`. -/
theorem isClosedEmbedding_axisMap : Topology.IsClosedEmbedding axisMap := by
  have h := TauCeti.isClosedEmbedding_add_smul_left (0 : Plane) (e_ne_zero 0) (𝕜 := ℝ)
  simpa only [zero_add, ← axisMap_def] using h

/-- The horizontal lift of `H¹⌞([0, 1] × {0})`: Lebesgue measure on `[0, 1]` transported to the
segment `[0, 1] e₀`, with the horizontal plane `ℝ e₀` at every point. -/
def segmentLift : Measure ((⊤ : Opens Plane) × grassmannian ℝ Plane 1) :=
  (volume.restrict (Icc (0 : ℝ) 1)).map (lineVarifoldParam 0 (e 0) (line 0))

/-- The open disc of radius `½` about `0`. -/
def halfDisc : Opens Plane :=
  ⟨ball 0 (1 / 2), isOpen_ball⟩

/-- The weight of `segmentLift` is Lebesgue measure on `[0, 1]` transported by `t ↦ t e₀`. -/
theorem weight_segmentLift :
    weight segmentLift = ((volume : Measure ℝ).restrict (Icc 0 1)).map axisMap := by
  rw [segmentLift, weight_map_lineVarifoldParam]
  congr 1
  funext t
  rw [zero_add, axisMap_def]

/-- `spt ‖V‖` is the segment `[0, 1] e₀`. -/
theorem support_weight_segmentLift : (weight segmentLift).support = axisMap '' Icc 0 1 := by
  rw [weight_segmentLift, Measure.support_map_of_isInducing_of_isClosed_range _
    isClosedEmbedding_axisMap.isInducing isClosedEmbedding_axisMap.isClosed_range,
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc, Measure.support_restrict_of_isOpen _ isOpen_Ioo,
    closure_Ioo zero_ne_one]

/-- The part of the segment `[0, 1] e₀` in the disc of radius `½` is `[0, ½) e₀`. -/
theorem image_Icc_inter_halfDisc :
    axisMap '' Icc 0 1 ∩ (halfDisc : Set Plane) = axisMap '' Ico 0 (1 / 2) := by
  ext x
  simp only [halfDisc, Opens.coe_mk, mem_inter_iff, mem_image, mem_ball_zero_iff, mem_Icc,
    mem_Ico]
  constructor
  · rintro ⟨⟨t, ⟨ht0, -⟩, rfl⟩, hx⟩
    rw [norm_axisMap, abs_of_nonneg ht0] at hx
    exact ⟨t, ⟨ht0, hx⟩, rfl⟩
  · rintro ⟨t, ⟨ht0, ht⟩, rfl⟩
    refine ⟨⟨t, ⟨ht0, by linarith⟩, rfl⟩, ?_⟩
    rwa [norm_axisMap, abs_of_nonneg ht0]

/-- **The support of a restriction is relative to the open set.** For the horizontal lift `V` of
the segment `[0, 1] e₀` and its restriction `V'` to the open disc `W'` of radius `½`, the support
of `‖V'‖` in `W'` is `[0, ½) e₀ = spt ‖V‖ ∩ W'`. This set is not closed in `ℝ²`: its closure in
`ℝ²` contains the point `½ e₀`, which lies outside `W'`. -/
theorem support_restrictOpens_segmentLift :
    (weight (restrictOpens segmentLift (le_top : halfDisc ≤ ⊤))).support ∩ halfDisc =
        axisMap '' Ico 0 (1 / 2) ∧
      (weight segmentLift).support ∩ halfDisc = axisMap '' Ico 0 (1 / 2) ∧
      axisMap (1 / 2) ∈ closure (axisMap '' Ico 0 (1 / 2)) ∧
      axisMap (1 / 2) ∉ (halfDisc : Set Plane) ∧
      ¬IsClosed (axisMap '' Ico 0 (1 / 2)) := by
  have h₁ : (weight segmentLift).support ∩ halfDisc = axisMap '' Ico 0 (1 / 2) := by
    rw [support_weight_segmentLift, image_Icc_inter_halfDisc]
  have hcl : axisMap (1 / 2) ∈ closure (axisMap '' Ico 0 (1 / 2)) := by
    refine image_closure_subset_closure_image isClosedEmbedding_axisMap.continuous
      (mem_image_of_mem _ ?_)
    rw [closure_Ico (by norm_num)]
    norm_num
  have hout : axisMap (1 / 2) ∉ (halfDisc : Set Plane) := by
    simp [halfDisc, norm_axisMap]
  refine ⟨(support_weight_restrictOpens_inter _).trans h₁, h₁, hcl, hout, fun hc => hout ?_⟩
  have := hc.closure_eq ▸ hcl
  rw [← h₁] at this
  exact this.2

end TauCeti.Examples.VarifoldWeight
