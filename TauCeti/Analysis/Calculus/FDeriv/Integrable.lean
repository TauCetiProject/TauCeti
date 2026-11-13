/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Integrability of the applied derivative and of derivative energy densities

The derivative of a `C¹` function with compact support is continuous and compactly supported,
hence bounded. So along a strongly measurable family of points `G`, the derivative applied to an
integrable family of vectors `Z` is integrable: it is dominated by a constant times `‖Z‖`. No
finiteness of the measure is needed.

Over any nontrivially normed field, squared norms of the derivative of a `C¹` map in two given
directions, and cutoff-weighted versions of them, are integrable when the map or the cutoff has
compact support. A weighted squared defect `c z * ‖fderiv w z e₁ + A z (fderiv w z e₂)‖ ^ 2` is
integrable when it vanishes off a compact set on which `c` and `A` are continuous, so they need
not be continuous elsewhere.

Precomposing with a measure-preserving continuous linear equivalence does not change whether
the squared norm of the derivative is integrable.

On a Euclidean product `ℝ × V`, the derivative of such a function in a fixed direction is also
integrable on the product of a half-line with `V`.

## Main results

* `TauCeti.integrable_fderiv_apply`: for `f` of class `C¹` with compact support, an a.e. strongly
  measurable `G` and an integrable `Z`, the map `x ↦ fderiv 𝕜 f (G x) (Z x)` is integrable.
* `TauCeti.integrable_fderiv_apply_of_tsupport_subset`: the same when `Z` is only integrable after
  cutting off to the points `x` with `G x` in a set `K` containing the topological support of `f`.
* `TauCeti.integrable_cutoff_fderiv_sq_mul_norm_sq`,
  `TauCeti.integrable_norm_fderiv_sq_add`, `TauCeti.integrable_cutoff_sq_mul_norm_fderiv_sq`,
  `TauCeti.integrable_mul_norm_defect_sq`: integrability of the derivative energy densities
  in two directions.
* `TauCeti.integrable_norm_fderiv_comp_sq_iff`: integrability of `‖fderiv (u ∘ e)‖ ^ 2` for a
  measure-preserving continuous linear equivalence `e` is that of `‖fderiv u‖ ^ 2`.
* `TauCeti.integrable_fderiv_apply_prod`: the directional derivative of a compactly supported
  `C¹` function on `ℝ × V` is integrable on the product of `Ioi a` with `V`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a `C¹` compactly supported function, evaluated along an a.e. strongly
measurable family of points `G` and applied to an integrable family of vectors `Z`, is integrable:
it is bounded by a constant times `‖Z‖`. -/
theorem integrable_fderiv_apply {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : E → F}
    (hf : ContDiff 𝕜 1 f) (hfc : HasCompactSupport f) {G : α → E} (hG : AEStronglyMeasurable G μ)
    {Z : α → E} (hZ : Integrable Z μ) :
    Integrable (fun x ↦ fderiv 𝕜 f (G x) (Z x)) μ := by
  have hDf := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hDf.bounded_above_of_compact_support (hfc.fderiv 𝕜)
  exact (hZ.norm.const_mul C).mono'
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : E →L[𝕜] F) w ↦ L w)
      (by fun_prop) (hDf.comp_aestronglyMeasurable hG) hZ.1)
    (.of_forall fun x ↦ (fderiv 𝕜 f _).le_of_opNorm_le (hC _) _)

/-- The derivative of a `C¹` compactly supported function `f`, evaluated along an a.e. strongly
measurable family of points `G` and applied to a family of vectors `Z`, is integrable as soon as
`Z` is integrable after cutting off to the points `x` with `G x ∈ K`, for a set `K` containing the
topological support of `f`: off `K` the derivative vanishes. -/
theorem integrable_fderiv_apply_of_tsupport_subset {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : E → F} (hf : ContDiff 𝕜 1 f)
    (hfc : HasCompactSupport f) {K : Set E} (hfK : tsupport f ⊆ K) {G : α → E}
    (hG : AEStronglyMeasurable G μ) {Z : α → E}
    (hZ : Integrable ({x | G x ∈ K}.indicator Z) μ) :
    Integrable (fun x ↦ fderiv 𝕜 f (G x) (Z x)) μ :=
  (integrable_fderiv_apply hf hfc hG hZ).congr
    (Filter.Eventually.of_forall fun x ↦ by
      by_cases hxK : G x ∈ K
      · simp [hxK]
      · simp [hxK, fderiv_of_notMem_tsupport 𝕜 fun h ↦ hxK (hfK h)])

section Energy

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ]

/-- The cutoff-derivative error density of a `C¹` cutoff with compact support is integrable
against the squared norm of a continuous map. -/
theorem integrable_cutoff_fderiv_sq_mul_norm_sq [NormedSpace ℝ E] {u : E → F} {χ : E → ℝ}
    (hu : Continuous u) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (e₁ e₂ : E) :
    Integrable (fun z ↦ (fderiv ℝ χ z e₁ ^ 2 + fderiv ℝ χ z e₂ ^ 2) * ‖u z‖ ^ 2) μ := by
  have := hχ.continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    (hc.fderiv ℝ).mono <| Function.support_subset_iff'.2 fun z hz ↦ by
      simp [Function.notMem_support.1 hz]

/-- The derivative energy of a compactly supported `C¹` map is integrable, in two directions. -/
theorem integrable_norm_fderiv_sq_add {w : E → F} (hw : ContDiff 𝕜 1 w) (hc : HasCompactSupport w)
    (e₁ e₂ : E) :
    Integrable (fun z ↦ ‖fderiv 𝕜 w z e₁‖ ^ 2 + ‖fderiv 𝕜 w z e₂‖ ^ 2) μ := by
  have := hw.continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    (hc.fderiv 𝕜).mono <| Function.support_subset_iff'.2 fun z hz ↦ by
      simp [Function.notMem_support.1 hz]

/-- A cutoff-weighted derivative energy density of a `C¹` map is integrable when the weight has
compact support. -/
theorem integrable_cutoff_sq_mul_norm_fderiv_sq {u : E → F} {χ : E → ℝ} (hu : ContDiff 𝕜 1 u)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (e₁ e₂ : E) :
    Integrable (fun z ↦ χ z ^ 2 * (‖fderiv 𝕜 u z e₁‖ ^ 2 + ‖fderiv 𝕜 u z e₂‖ ^ 2)) μ := by
  have := hu.continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    hc.mono <| Function.support_subset_iff'.2 fun z hz ↦ by simp [Function.notMem_support.1 hz]

/-- A weighted squared defect `c z * ‖fderiv 𝕜 w z e₁ + A z (fderiv 𝕜 w z e₂)‖ ^ 2` of a `C¹` map
is integrable once it vanishes off a compact set on which the coefficients are continuous. -/
theorem integrable_mul_norm_defect_sq (e₁ e₂ : E) {w : E → F} {c : E → ℝ} {A : E → F →L[𝕜] F}
    {S : Set E} (hw : ContDiff 𝕜 1 w) (hc : ContinuousOn c S) (hS : IsCompact S)
    (hA : ContinuousOn A S)
    (hsub : Function.support
      (fun z ↦ c z * ‖fderiv 𝕜 w z e₁ + A z (fderiv 𝕜 w z e₂)‖ ^ 2) ⊆ S) :
    Integrable (fun z ↦ c z * ‖fderiv 𝕜 w z e₁ + A z (fderiv 𝕜 w z e₂)‖ ^ 2) μ := by
  have hdw := (hw.continuous_fderiv one_ne_zero).continuousOn (s := S)
  exact (integrableOn_iff_integrable_of_support_subset hsub).mp <|
    (hc.mul (((hdw.clm_apply continuousOn_const).add
      (hA.clm_apply (hdw.clm_apply continuousOn_const))).norm.pow 2)).integrableOn_compact hS

end Energy

section CompContinuousLinearEquiv

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F}

/-- Precomposing a map with a measure-preserving continuous linear equivalence `e` does not change
whether the squared norm of its derivative is integrable: the two derivatives differ by
composition with `e` or with its inverse, which change norms by at most `‖e‖` and `‖e.symm‖`. -/
theorem integrable_norm_fderiv_comp_sq_iff (e : E ≃L[𝕜] F) (he : MeasurePreserving e μ ν)
    {u : F → G} :
    Integrable (fun w ↦ ‖fderiv 𝕜 (u ∘ e) w‖ ^ 2) μ ↔
      Integrable (fun z ↦ ‖fderiv 𝕜 u z‖ ^ 2) ν := by
  have hemb : MeasurableEmbedding e := by
    simpa only [e.coe_toHomeomorph] using e.toHomeomorph.measurableEmbedding
  rw [← he.integrable_comp_emb hemb]
  have hcomp (w : E) : fderiv 𝕜 (u ∘ e) w = (fderiv 𝕜 u (e w)).comp (e : E →L[𝕜] F) :=
    e.comp_right_fderiv
  have hsq {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b * c) : ‖a ^ 2‖ ≤ c ^ 2 * b ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow, mul_comm c]
    gcongr
  constructor
  · intro h
    refine (h.const_mul (‖(e.symm : F →L[𝕜] E)‖ ^ 2)).mono'
      (((measurable_fderiv 𝕜 u).comp he.measurable).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w ↦ hsq (norm_nonneg _) ?_)
    have h' : fderiv 𝕜 u (e w) = (fderiv 𝕜 (u ∘ e) w).comp (e.symm : F →L[𝕜] E) := by
      ext v
      simp [hcomp]
    rw [h']
    exact ContinuousLinearMap.opNorm_comp_le _ _
  · intro h
    refine (h.const_mul (‖(e : E →L[𝕜] F)‖ ^ 2)).mono'
      ((measurable_fderiv 𝕜 (u ∘ e)).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w ↦ hsq (norm_nonneg _) ?_)
    rw [hcomp]
    exact ContinuousLinearMap.opNorm_comp_le _ _

end CompContinuousLinearEquiv

section Prod

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The directional derivative of a compactly supported `C¹` function is integrable on the
product of `Ioi a` with `V`. -/
theorem integrable_fderiv_apply_prod {g : WithLp 2 (ℝ × V) → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (a : ℝ) (d : WithLp 2 (ℝ × V)) :
    Integrable (fun z : ℝ × V ↦ fderiv ℝ g (WithLp.toLp 2 z) d)
      ((volume.restrict (Ioi a)).prod volume) := by
  have hdc : Continuous fun x ↦ fderiv ℝ g x d :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h : Integrable (fun x ↦ fderiv ℝ g x d) volume :=
    hdc.integrable_of_hasCompactSupport (hgc.fderiv_apply (𝕜 := ℝ) d)
  have hprod :=
    (WithLp.volume_preserving_toLp ℝ V).integrable_comp h.aestronglyMeasurable |>.mpr h
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hprod.integrableOn

end Prod

end TauCeti
