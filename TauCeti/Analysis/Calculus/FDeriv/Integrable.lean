/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.RCLike.OperatorNorm

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

Integrability of the squared norm of the derivative implies integrability of the squared norm of
the derivative applied to any fixed vector. Conversely, for a map out of an `RCLike` field that
satisfies a Cauchy--Riemann equation `∂ₜu = A (∂ₛu)` with `‖A‖` bounded, integrability of the
squared norm of the real-direction derivative `∂ₛu` implies integrability of `‖du‖²`.
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
* `TauCeti.integrable_norm_fderiv_apply_sq`: integrability of `‖fderiv 𝕜 u z v‖ ^ 2` from
  integrability of `‖fderiv 𝕜 u z‖ ^ 2`.
* `TauCeti.memLp_norm_fderiv_of_lipschitzWith`,
  `TauCeti.integrable_norm_fderiv_sq_of_lipschitzWith`: `Lᵖ` and squared-energy integrability of
  `‖fderiv 𝕜 u‖` for a compactly supported Lipschitz map.
* `TauCeti.integrableOn_pow_mul_norm_deriv_sq_of_lipschitzWith`,
  `TauCeti.integrableOn_pow_mul_deriv_sq_of_lipschitzWith`: `Ioi 0`-integrability of
  `r ^ k * ‖deriv f r‖ ^ 2` for a Lipschitz map vanishing on `[R, ∞)`.
* `TauCeti.integral_radial_deriv_sq_le`: the polar energy of a radial compactly supported
  Lipschitz function dominates the weighted 1D ray energy.
* `TauCeti.integrableOn_norm_fderiv_sq_of_apply_I_eq`: integrability of `‖fderiv ℝ u z‖ ^ 2` from
  integrability of `‖fderiv ℝ u z 1‖ ^ 2` under a Cauchy--Riemann equation.
* `ContinuousLinearEquiv.integrable_norm_fderiv_comp_sq_iff`: integrability of
  `‖fderiv (u ∘ e)‖ ^ 2` for a measure-preserving continuous linear equivalence `e` is that of
  `‖fderiv u‖ ^ 2`.
* `TauCeti.integrable_fderiv_apply_prod`: the directional derivative of a compactly supported
  `C¹` function on `ℝ × V` is integrable on the product of `Ioi a` with `V`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

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

/-- If the squared norm of the derivative of a map into a complete space is integrable, then so is
the squared norm of the derivative applied to any fixed vector `v`: it is bounded by
`‖v‖ ^ 2 * ‖fderiv 𝕜 u z‖ ^ 2`. -/
theorem integrable_norm_fderiv_apply_sq [CompleteSpace F] {ν : Measure E} {u : E → F}
    (h : Integrable (fun z ↦ ‖fderiv 𝕜 u z‖ ^ 2) ν) (v : E) :
    Integrable (fun z ↦ ‖fderiv 𝕜 u z v‖ ^ 2) ν := by
  borelize F
  refine (h.const_mul (‖v‖ ^ 2)).mono'
    ((measurable_fderiv_apply_const 𝕜 u v).norm.pow_const 2).aestronglyMeasurable
    (.of_forall fun z ↦ ?_)
  rw [norm_pow, norm_norm, ← mul_pow, mul_comm]
  gcongr
  exact (fderiv 𝕜 u z).le_opNorm v

/-- The operator norm of the Fréchet derivative of a compactly supported `K`-Lipschitz map into
a complete space belongs to `Lᵖ` for every `p ∈ [0, ∞]`. -/
theorem memLp_norm_fderiv_of_lipschitzWith [CompleteSpace F] {p : ℝ≥0∞} {K : ℝ≥0} {u : E → F}
    (hu : LipschitzWith K u) (hsupp : HasCompactSupport u) :
    MemLp (fun x ↦ ‖fderiv 𝕜 u x‖) p μ := by
  borelize (E →L[𝕜] F)
  refine (hsupp.fderiv 𝕜).norm.memLp_of_bound
    (measurable_fderiv 𝕜 u).norm.aestronglyMeasurable K
    (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_fderiv_le_of_lipschitz 𝕜 hu

/-- The squared operator norm of the Fréchet derivative of a compactly supported `K`-Lipschitz
map into a complete space is integrable. -/
theorem integrable_norm_fderiv_sq_of_lipschitzWith [CompleteSpace F] {K : ℝ≥0} {u : E → F}
    (hu : LipschitzWith K u) (hsupp : HasCompactSupport u) :
    Integrable (fun x ↦ ‖fderiv 𝕜 u x‖ ^ 2) μ := by
  borelize (E →L[𝕜] F)
  have hmem : MemLp (fun x ↦ ‖fderiv 𝕜 u x‖) 2 μ :=
    memLp_norm_fderiv_of_lipschitzWith (𝕜 := 𝕜) hu hsupp
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using
    (memLp_two_iff_integrable_sq_norm (measurable_fderiv 𝕜 u).norm.aestronglyMeasurable).1 hmem

end Energy

section CauchyRiemann

variable {K : Type*} [RCLike K] [MeasurableSpace K] [OpensMeasurableSpace K] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Energy from the real-direction energy.** If `u : K → G` out of an `RCLike` field satisfies the
Cauchy--Riemann equation `∂ₜu = A z (∂ₛu)` on a measurable set `s`, with `‖A z‖ ≤ M` there, and
`‖∂ₛu‖²` is integrable on `s`, then so is `‖du‖²`: it is bounded by `(1 + M)² ‖∂ₛu‖²`. -/
theorem integrableOn_norm_fderiv_sq_of_apply_I_eq {ν : Measure K} {u : K → G}
    {A : K → G →L[ℝ] G} {M : ℝ} {s : Set K} (hs : MeasurableSet s)
    (hCR : ∀ z ∈ s, fderiv ℝ u z RCLike.I = A z (fderiv ℝ u z 1)) (hA : ∀ z ∈ s, ‖A z‖ ≤ M)
    (h : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) s ν) :
    IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) s ν := by
  borelize (K →L[ℝ] G)
  refine (h.const_mul ((1 + M) ^ 2)).mono'
    ((measurable_fderiv ℝ u).norm.pow_const 2).aestronglyMeasurable
    ((ae_restrict_iff' hs).2 (.of_forall fun z hz ↦ ?_))
  rw [norm_pow, norm_norm, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((fderiv ℝ u z).norm_le_of_apply_I_eq (hCR z hz) (hA z hz) le_rfl) 2

end CauchyRiemann
section CompContinuousLinearEquiv

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F}

/-- Precomposing a map with a measure-preserving continuous linear equivalence `e` does not change
whether the squared norm of its derivative is integrable: the two derivatives differ by
composition with `e` or with its inverse, which change norms by at most `‖e‖` and `‖e.symm‖`. -/
theorem _root_.ContinuousLinearEquiv.integrable_norm_fderiv_comp_sq_iff (e : E ≃L[𝕜] F)
    (he : MeasurePreserving e μ ν) {u : F → G} :
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

section RadialAndHalfLine

/-- For a `K`-Lipschitz map `f : ℝ → F` into a complete space vanishing on `[R, ∞)` with
`0 ≤ R`, the weighted squared derivative `r ↦ r ^ k * ‖deriv f r‖ ^ 2` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_norm_deriv_sq_of_lipschitzWith {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {K : ℝ≥0} {f : ℝ → F} (hf : LipschitzWith K f)
    {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ r ≥ R, f r = 0) :
    IntegrableOn (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) volume :=
    (continuous_pow k).aestronglyMeasurable.mul ((aestronglyMeasurable_deriv f volume).norm.pow 2)
  have hIoc : IntegrableOn (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) (Ioc 0 R) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict (R ^ k * (K : ℝ) ^ 2) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr ↦ ?_
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr.1.le _) (sq_nonneg _))]
    have hnorm : ‖deriv f r‖ ≤ K := norm_deriv_le_of_lipschitz hf
    exact mul_le_mul (pow_le_pow_left₀ hr.1.le hr.2 _)
      (sq_le_sq.2 (by rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg K.coe_nonneg]))
      (sq_nonneg _) (pow_nonneg hR _)
  have hIoi : IntegrableOn (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) (Ioi R) := by
    refine integrableOn_zero.congr_fun (fun r (hr : R < r) ↦ ?_) measurableSet_Ioi
    have h0 : f =ᶠ[𝓝 r] 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hr) fun x hx ↦ hfR x hx.le
    simp [h0.deriv_eq]
  rw [← Ioc_union_Ioi_eq_Ioi hR]
  exact hIoc.union hIoi

/-- For a `K`-Lipschitz real function `f : ℝ → ℝ` vanishing on `[R, ∞)` with `0 ≤ R`, the
weighted squared derivative `r ↦ r ^ k * (deriv f r) ^ 2` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_deriv_sq_of_lipschitzWith {k : ℕ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ r ≥ R, f r = 0) :
    IntegrableOn (fun r : ℝ ↦ r ^ k * (deriv f r) ^ 2) (Ioi 0) := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    integrableOn_pow_mul_norm_deriv_sq_of_lipschitzWith (k := k) hf hR hfR

open Module

/-- For a compactly supported `K`-Lipschitz radial real function `v : E → ℝ`, the weighted
one-dimensional Dirichlet energy of the scaled unit-ray profile `r ↦ c * v (max r 0 • e₀)`
on `(0, ∞)` is bounded above by `c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 ∂μ`. -/
theorem integral_radial_deriv_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {K : ℝ≥0} {v : E → ℝ} (hv_lip : LipschitzWith K v)
    (hv_supp : HasCompactSupport v) (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {e₀ : E} (he₀ : ‖e₀‖ = 1) (c : ℝ) :
    (finrank ℝ E : ℝ) * (μ.real (Metric.ball (0 : E) 1) *
        ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ E - 1) *
          (deriv (fun r ↦ c * v (max r 0 • e₀)) r) ^ 2) ≤
      c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 ∂μ := by
  set n := finrank ℝ E with hn_def
  let f : ℝ → ℝ := fun r ↦ c * v (max r 0 • e₀)
  let φ : ℝ → ℝ := fun r ↦ ‖fderiv ℝ v (max r 0 • e₀)‖ ^ 2
  have hv_grad_int := integrable_norm_fderiv_sq_of_lipschitzWith (𝕜 := ℝ) (μ := μ) hv_lip hv_supp
  have hv_grad_eq : (fun x : E ↦ ‖fderiv ℝ v x‖ ^ 2) = fun x ↦ φ ‖x‖ := funext fun x ↦ by
    have hnorm : ‖x‖ = ‖‖x‖ • e₀‖ := by rw [norm_smul, Real.norm_eq_abs, abs_norm, he₀, mul_one]
    simp only [φ, max_eq_left (norm_nonneg x), norm_fderiv_eq_of_norm_eq hv_rad hnorm]
  have hφ_int : IntegrableOn (fun r ↦ r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) (Ioi 0) := by
    rw [hv_grad_eq] at hv_grad_int
    exact ((integrable_fun_norm_addHaar μ (f := φ)).mp hv_grad_int).congr_fun
      (fun r (hr : 0 < r) ↦ by simp [φ, max_eq_left hr.le, smul_eq_mul, ← hn_def])
      measurableSet_Ioi
  have hpt : ∀ r ∈ Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 ≤
      c ^ 2 * (r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) := fun r (hr : 0 < r) ↦ by
    have hev : f =ᶠ[𝓝 r] fun s ↦ c * v (s • e₀) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hr) fun s hs ↦ by simp [f, max_eq_left hs.le]
    rw [hev.deriv_eq, deriv_const_mul_field, mul_pow, mul_left_comm]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (deriv_radial_sq_le hv_rad he₀ hr) (pow_nonneg hr.le _))
      (sq_nonneg c)
  have hderiv_f_int : IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0) :=
    (hφ_int.const_mul (c ^ 2)).mono' (((continuous_pow (n - 1)).measurable.mul
      ((measurable_deriv f).pow_const 2)).aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (mem_Ioi.1 hr).le _) (sq_nonneg _))]
        exact hpt r hr)
  have hrad_le : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 ≤
      c ^ 2 * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hderiv_f_int (hφ_int.const_mul (c ^ 2)) measurableSet_Ioi hpt
  have hgrad_polar : (n : ℝ) * (μ.real (Metric.ball (0 : E) 1) *
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) =
      ∫ x, ‖fderiv ℝ v x‖ ^ 2 ∂μ := by
    rw [hv_grad_eq, integral_fun_norm_addHaar μ φ]
    simp only [nsmul_eq_mul, smul_eq_mul, ← hn_def]; congr 2
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
      simp [φ, max_eq_left hr.le]
  calc (n : ℝ) * (μ.real (Metric.ball (0 : E) 1) *
        ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2)
      ≤ (n : ℝ) * (μ.real (Metric.ball (0 : E) 1) *
          (c ^ 2 * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad_le measureReal_nonneg)
          (Nat.cast_nonneg n)
    _ = c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 ∂μ := by rw [← hgrad_polar]; ring

end RadialAndHalfLine

end TauCeti
