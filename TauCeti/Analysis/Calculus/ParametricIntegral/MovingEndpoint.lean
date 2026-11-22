/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Order.Interval.Set.Basic
import TauCeti.Topology.Order.Interval

/-!
# Parametric integrals with a moving lower endpoint and separable kernel bounds

For a kernel `K : ℝ → ℝ → 𝕜` bounded by a separable majorant `‖K x v‖ ≤ P x * Q v` on
`{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}` and an integrand `F : ℝ → E` such that `Q * ‖F‖` is integrable
on the right tails `I ∩ Ioi x`, this file develops integrability, norm bounds, continuity, and
differentiation under the integral sign for the moving-endpoint tail integral
`x ↦ ∫ v in I ∩ Ioi x, K x v • F v`.

Rewriting `(Ioi x).indicator (fun v ↦ K x v • F v)` over a fixed tail `I ∩ Ioi c` (`c ≤ x`)
reduces continuity to dominated convergence and differentiation to
`hasDerivAt_integral_of_dominated_loc_of_lip`, using a uniform local Lipschitz bound along the
moving cutoff `x` when `K x x = 0`.

## Main results

* `ContinuousOn.aestronglyMeasurable_slice_inter_Ioi`: slice measurability of a kernel
  continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}`.
* `TauCeti.norm_kernel_smul_le`: pointwise separable bound `‖K x v • y‖ ≤ P x * (Q v * ‖y‖)`.
* `TauCeti.integrableOn_kernel_smul_inter_Ioi`: integrability of `v ↦ K x v • F v` on
  `I ∩ Ioi x`.
* `TauCeti.norm_integral_kernel_smul_inter_Ioi_le`: separable bound
  `‖∫ v in I ∩ Ioi x, K x v • F v‖ ≤ P x * ∫ v in I ∩ Ioi x, Q v * ‖F v‖`.
* `TauCeti.continuousOn_integral_kernel_smul_inter_Ioi`: continuity of
  `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` on an order-connected set `I`.
* `TauCeti.hasDerivAt_integral_kernel_smul_inter_Ioi`: differentiation of
  `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` on an open set `I` when `K x x = 0` and `∂K/∂x = K'`
  satisfies a separable bound.
-/

public section

open Filter Set MeasureTheory Function
open scoped Topology

/-- A kernel `K` continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}` has almost everywhere strongly
measurable slice `K x` on `I ∩ Ioi x` for every `x ∈ I`. -/
theorem ContinuousOn.aestronglyMeasurable_slice_inter_Ioi
    {α γ : Type*} [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace γ]
    [SecondCountableTopologyEither α γ] [TopologicalSpace.PseudoMetrizableSpace γ]
    {μ : Measure α} {I : Set α} {K : α → α → γ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hI : MeasurableSet I) {x : α} (hx : x ∈ I) :
    AEStronglyMeasurable (K x) (μ.restrict (I ∩ Ioi x)) :=
  (hK.comp (continuous_const.prodMk continuous_id).continuousOn
    fun _ (hv : _ ∈ I ∩ Ioi x) ↦ ⟨hx, hv.1, hv.2.le⟩).aestronglyMeasurable
    (hI.inter measurableSet_Ioi)

namespace TauCeti

section IntegrabilityAndBound

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- The pointwise separable bound `‖K x v • y‖ ≤ P x * (Q v * ‖y‖)` for `v ∈ I` with
`x ≤ v`. -/
theorem norm_kernel_smul_le {x : ℝ} (hKle : ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    {v : ℝ} (hv : v ∈ I) (hxv : x ≤ v) (y : E) :
    ‖K x v • y‖ ≤ P x * (Q v * ‖y‖) := by
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKle v hv hxv) (norm_nonneg _)

/-- If `K x` and `F` are almost everywhere strongly measurable on `I ∩ Ioi x`, `Q * ‖F‖` is
integrable on `I ∩ Ioi x`, and `‖K x v‖ ≤ P x * Q v` for `v ∈ I` with `x ≤ v`, then
`v ↦ K x v • F v` is integrable on `I ∩ Ioi x`. -/
theorem integrableOn_kernel_smul_inter_Ioi (hI : MeasurableSet I) {x : ℝ}
    (hKle : ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hKx : AEStronglyMeasurable (K x) (volume.restrict (I ∩ Ioi x)))
    {F : ℝ → E} (hF : AEStronglyMeasurable F (volume.restrict (I ∩ Ioi x)))
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (I ∩ Ioi x) := by
  refine Integrable.mono' (hFint.const_mul (P x)) (hKx.smul hF) ?_
  filter_upwards [ae_restrict_mem (hI.inter measurableSet_Ioi)] with v hv
  exact norm_kernel_smul_le hKle hv.1 hv.2.le _

/-- Extending `v ↦ K x v • F v` by zero from `I ∩ Ioi x` to `I ∩ Ioi c` (`c ≤ x`) preserves
integrability. -/
private lemma integrableOn_indicator_kernel_smul_inter_Ioi (hI : MeasurableSet I) {x : ℝ}
    (hKle : ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hKx : AEStronglyMeasurable (K x) (volume.restrict (I ∩ Ioi x)))
    {F : ℝ → E} (hF : AEStronglyMeasurable F (volume.restrict (I ∩ Ioi x)))
    {c : ℝ} (hcx : c ≤ x) (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    IntegrableOn ((Ioi x).indicator (fun v ↦ K x v • F v)) (I ∩ Ioi c) := by
  rw [integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet, inter_comm,
    Set.inter_Ioi_inter_Ioi_of_le hcx]
  exact integrableOn_kernel_smul_inter_Ioi hI hKle hKx hF hFint

/-- The separable bound `‖∫ v in I ∩ Ioi x, K x v • F v‖ ≤ P x * ∫ v in I ∩ Ioi x, Q v * ‖F v‖`
for the moving-endpoint integral of a separably bounded kernel. -/
theorem norm_integral_kernel_smul_inter_Ioi_le [NormedSpace ℝ E] (hI : MeasurableSet I) {x : ℝ}
    (hKle : ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E}
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    ‖∫ v in I ∩ Ioi x, K x v • F v‖ ≤ P x * ∫ v in I ∩ Ioi x, Q v * ‖F v‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hFint.const_mul (P x)) ?_
  filter_upwards [ae_restrict_mem (hI.inter measurableSet_Ioi)] with v hv
  exact norm_kernel_smul_le hKle hv.1 hv.2.le _

end IntegrabilityAndBound

section Continuity

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- If `K` is continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}` with `‖K x v‖ ≤ P x * Q v`,
`P` is continuous on `I`, `Q ≥ 0` on `I`, `F` is `AEStronglyMeasurable` on `I`, and `Q * ‖F‖` is
integrable on every right tail `I ∩ Ioi x` (`x ∈ I`), then `x ↦ ∫ v in I ∩ Ioi x, K x v • F v`
is continuous on `I`. -/
theorem continuousOn_integral_kernel_smul_inter_Ioi (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v) (hP : ContinuousOn P I)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) {F : ℝ → E} (hF : AEStronglyMeasurable F (volume.restrict I))
    (hFint : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    ContinuousOn (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) I := by
  intro x₀ hx₀
  obtain ⟨c, hcI, d, _, hcx₀, hx₀d, hcdI, hcdN⟩ := hI.exists_Icc_mem_nhdsWithin hx₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hcdI)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ ⟨hcx₀, hx₀d⟩)
  have hSmeas : MeasurableSet (I ∩ Ioi c) := hI.measurableSet.inter measurableSet_Ioi
  -- extend the integrands by zero to the fixed tail `I ∩ Ioi c`
  have heq : (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) =ᶠ[𝓝[I] x₀]
      fun x ↦ ∫ v in I ∩ Ioi c, (Ioi x).indicator (fun v ↦ K x v • F v) v := by
    filter_upwards [hcdN] with x hx
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_Ioi_inter_Ioi_of_le hx.1]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ heq ?_
  · refine continuousWithinAt_of_dominated (bound := fun v ↦ M * (Q v * ‖F v‖)) ?_ ?_
      ((hFint c hcI).const_mul M) ?_
    · -- measurability of the extended integrands
      filter_upwards [hcdN] with x hx
      have hxI : x ∈ I := hcdI hx
      exact (integrableOn_indicator_kernel_smul_inter_Ioi hI.measurableSet (hKle x hxI)
        (hK.aestronglyMeasurable_slice_inter_Ioi hI.measurableSet hxI)
        (hF.mono_set inter_subset_left) hx.1 (hFint x hxI)).aestronglyMeasurable
    · -- uniform integrable domination on `I ∩ Ioi c`
      filter_upwards [hcdN] with x hx
      refine (ae_restrict_iff' hSmeas).2 (ae_of_all _ fun v hv ↦ ?_)
      have hQF : 0 ≤ Q v * ‖F v‖ := mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
      by_cases hxv : x < v
      · rw [indicator_of_mem hxv, norm_smul]
        calc ‖K x v‖ * ‖F v‖ ≤ (P x * Q v) * ‖F v‖ :=
              mul_le_mul_of_nonneg_right (hKle x (hcdI hx) v hv.1 hxv.le) (norm_nonneg _)
          _ ≤ (M * Q v) * ‖F v‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right ((le_abs_self (P x)).trans (hM x hx)) (hQ0 v hv.1))
                (norm_nonneg _)
          _ = M * (Q v * ‖F v‖) := by ring
      · rw [indicator_of_notMem hxv, norm_zero]
        exact mul_nonneg hM0 hQF
    · -- pointwise continuity away from `x₀`
      filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae (Measure.ae_ne volume x₀)]
        with v hv hvne
      rcases hvne.lt_or_gt with hlt | hgt
      · refine continuousWithinAt_const.congr_of_eventuallyEq ?_
          (indicator_of_notMem (notMem_Ioi.2 hlt.le) _)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with x hx
        exact indicator_of_notMem (notMem_Ioi.2 hx.le) _
      · have hKv : ContinuousWithinAt (fun x ↦ K x v) (I ∩ Iio v) x₀ :=
          ContinuousWithinAt.comp (g := uncurry K) (f := fun x ↦ (x, v))
            (hK (x₀, v) ⟨hx₀, hv.1, hgt.le⟩)
            (continuous_id.prodMk continuous_const).continuousWithinAt
            fun x hx ↦ ⟨hx.1, hv.1, hx.2.le⟩
        have hKvI : ContinuousWithinAt (fun x ↦ K x v) I x₀ :=
          hKv.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgt)))
        refine (hKvI.smul continuousWithinAt_const).congr_of_eventuallyEq ?_
          (indicator_of_mem (mem_Ioi.2 hgt) _)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgt)] with x hx
        exact indicator_of_mem (mem_Ioi.2 hx) _
  · -- rewrite the value at `x₀` back to `I ∩ Ioi x₀`
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_Ioi_inter_Ioi_of_le hcx₀]

end Continuity

section Differentiability

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E]
  {I : Set ℝ} {K K' : ℝ → ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Local Lipschitz bound in `x` for the truncated integrand `x ↦ (Ioi x).indicator (K x · • F ·) v`
on an interior interval `(c, d)` when `K v v = 0` and `‖∂K/∂x‖ ≤ M₁ * Q v`. -/
private lemma lipschitzOnWith_indicator_kernel_smul
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    {c d M₁ : ℝ} (hcdI : Icc c d ⊆ I) (hM₁0 : 0 ≤ M₁)
    (hK'le : ∀ t ∈ Icc c d, ∀ v ∈ I, t ≤ v → ‖K' t v‖ ≤ M₁ * Q v)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) {F : ℝ → E} {v : ℝ} (hv : v ∈ I) :
    LipschitzOnWith (Real.nnabs (M₁ * (Q v * ‖F v‖)))
      (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • F u) v) (Ioo c d) := by
  have hL0 : 0 ≤ M₁ * (Q v * ‖F v‖) := mul_nonneg hM₁0 (mul_nonneg (hQ0 v hv) (norm_nonneg _))
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  rw [Real.coe_nnabs, abs_of_nonneg hL0]
  wlog hxy : x ≤ y generalizing x y
  · rw [norm_sub_rev, norm_sub_rev x y]
    exact this hy hx (le_of_not_ge hxy)
  rw [Real.norm_of_nonpos (sub_nonpos.2 hxy), neg_sub]
  rcases le_or_gt v x with hvx | hxv
  · rw [indicator_of_notMem (notMem_Ioi.2 hvx),
      indicator_of_notMem (notMem_Ioi.2 (hvx.trans hxy)), sub_self, norm_zero]
    exact mul_nonneg hL0 (sub_nonneg.2 hxy)
  · have htcd : ∀ w ∈ Icc x (min y v), ∀ t ∈ Icc x w, t ∈ Icc c d := fun _ hw _ ht ↦
      ⟨hx.1.le.trans ht.1, ht.2.trans (hw.2.trans ((min_le_left y v).trans hy.2.le))⟩
    have hmvt_on : ∀ w ∈ Icc x (min y v), ‖K w v - K x v‖ ≤ M₁ * Q v * (w - x) := fun w hw ↦
      norm_image_sub_le_of_norm_deriv_right_le_segment
        (hK.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht ↦
          ⟨hcdI (htcd w hw t ht), hv, ht.2.trans (hw.2.trans (min_le_right y v))⟩)
        (fun t ht ↦ (hKderiv t (hcdI (htcd w hw t ⟨ht.1, ht.2.le⟩)) v hv
          (ht.2.trans_le (hw.2.trans (min_le_right y v)))).hasDerivWithinAt)
        (fun t ht ↦ hK'le t (htcd w hw t ⟨ht.1, ht.2.le⟩) v hv
          (ht.2.le.trans (hw.2.trans (min_le_right y v))))
        w ⟨hw.1, le_rfl⟩
    rcases lt_or_ge y v with hyv | hvy
    · rw [indicator_of_mem hxv, indicator_of_mem hyv, ← sub_smul, norm_smul, norm_sub_rev]
      calc ‖K y v - K x v‖ * ‖F v‖ ≤ (M₁ * Q v * (y - x)) * ‖F v‖ :=
            mul_le_mul_of_nonneg_right (hmvt_on y ⟨hxy, le_min le_rfl hyv.le⟩) (norm_nonneg _)
        _ = M₁ * (Q v * ‖F v‖) * (y - x) := by ring
    · rw [indicator_of_mem hxv, indicator_of_notMem (notMem_Ioi.2 hvy), sub_zero, norm_smul]
      have hKxv := hmvt_on v ⟨hxv.le, le_min hvy le_rfl⟩
      rw [hKdiag v hv, zero_sub, norm_neg] at hKxv
      have hMQ : 0 ≤ M₁ * Q v := mul_nonneg hM₁0 (hQ0 v hv)
      calc ‖K x v‖ * ‖F v‖ ≤ (M₁ * Q v * (v - x)) * ‖F v‖ :=
            mul_le_mul_of_nonneg_right hKxv (norm_nonneg _)
        _ ≤ (M₁ * Q v * (y - x)) * ‖F v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hvy x) hMQ)
              (norm_nonneg _)
        _ = M₁ * (Q v * ‖F v‖) * (y - x) := by ring

/-- Differentiating `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` under the integral sign on an open set `I`
when `K x x = 0` and `∂K/∂x = K'` satisfies `‖K' x v‖ ≤ P₁ x * Q v`. -/
theorem hasDerivAt_integral_kernel_smul_inter_Ioi (hIopen : IsOpen I)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I)
    (hK'x : AEStronglyMeasurable (K' x₀) (volume.restrict (I ∩ Ioi x₀)))
    (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K' x v‖ ≤ P₁ x * Q v)
    {F : ℝ → E} (hF : AEStronglyMeasurable F (volume.restrict I))
    (hFint : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    HasDerivAt (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v)
      (∫ v in I ∩ Ioi x₀, K' x₀ v • F v) x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hIopen x₀ hx₀
  have hcx₀ : x₀ - ε / 2 < x₀ := by linarith
  have hx₀d : x₀ < x₀ + ε / 2 := by linarith
  have hcdI : Icc (x₀ - ε / 2) (x₀ + ε / 2) ⊆ I := fun t ht ↦ hball <| by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hcI : x₀ - ε / 2 ∈ I := hcdI ⟨le_rfl, (hcx₀.trans hx₀d).le⟩
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP₁.mono hcdI)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ x₀ ⟨hcx₀.le, hx₀d.le⟩)
  have hImeas : MeasurableSet I := hIopen.measurableSet
  have hSmeas : MeasurableSet (I ∩ Ioi (x₀ - ε / 2)) := hImeas.inter measurableSet_Ioi
  have hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun v ↦ (Ioi x).indicator (fun u ↦ K x u • F u) v)
        (volume.restrict (I ∩ Ioi (x₀ - ε / 2))) := by
    filter_upwards [Ioo_mem_nhds hcx₀ hx₀d] with x hx
    have hxI : x ∈ I := hcdI ⟨hx.1.le, hx.2.le⟩
    exact (integrableOn_indicator_kernel_smul_inter_Ioi hImeas (hKle x hxI)
      (hK.aestronglyMeasurable_slice_inter_Ioi hImeas hxI)
      (hF.mono_set inter_subset_left) hx.1.le (hFint x hxI)).aestronglyMeasurable
  have hF_int : IntegrableOn (fun v ↦ (Ioi x₀).indicator (fun u ↦ K x₀ u • F u) v)
      (I ∩ Ioi (x₀ - ε / 2)) :=
    integrableOn_indicator_kernel_smul_inter_Ioi hImeas (hKle x₀ hx₀)
      (hK.aestronglyMeasurable_slice_inter_Ioi hImeas hx₀)
      (hF.mono_set inter_subset_left) hcx₀.le (hFint x₀ hx₀)
  have hF'_meas : AEStronglyMeasurable (fun v ↦ (Ioi x₀).indicator (fun u ↦ K' x₀ u • F u) v)
      (volume.restrict (I ∩ Ioi (x₀ - ε / 2))) :=
    (integrableOn_indicator_kernel_smul_inter_Ioi hImeas (hK'le x₀ hx₀) hK'x
      (hF.mono_set inter_subset_left) hcx₀.le (hFint x₀ hx₀)).aestronglyMeasurable
  have h_lip : ∀ᵐ v ∂volume.restrict (I ∩ Ioi (x₀ - ε / 2)),
      LipschitzOnWith (Real.nnabs (M₁ * (Q v * ‖F v‖)))
        (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • F u) v) (Ioo (x₀ - ε / 2) (x₀ + ε / 2)) := by
    filter_upwards [ae_restrict_mem hSmeas] with v hv
    exact lipschitzOnWith_indicator_kernel_smul hK hKdiag hKderiv hcdI hM₁0
      (fun t ht u hu htu ↦ (hK'le t (hcdI ht) u hu htu).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hM₁ t ht)) (hQ0 u hu)))
      hQ0 hv.1
  have h_deriv : ∀ᵐ v ∂volume.restrict (I ∩ Ioi (x₀ - ε / 2)),
      HasDerivAt (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • F u) v)
        ((Ioi x₀).indicator (fun u ↦ K' x₀ u • F u) v) x₀ := by
    filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae (Measure.ae_ne volume x₀)]
      with v hv hvne
    rcases hvne.lt_or_gt with hlt | hgt
    · rw [indicator_of_notMem (notMem_Ioi.2 hlt.le)]
      refine (hasDerivAt_const x₀ (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hlt] with x hx
      exact indicator_of_notMem (notMem_Ioi.2 hx.le) _
    · rw [indicator_of_mem hgt]
      refine ((hKderiv x₀ hx₀ v hv.1 hgt).smul_const (F v)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hgt] with x hx
      exact indicator_of_mem (mem_Ioi.2 hx) _
  -- differentiate the truncated integral over `I ∩ Ioi (x₀ - ε / 2)`
  have hderiv_ind := hasDerivAt_integral_of_dominated_loc_of_lip
    (Ioo_mem_nhds hcx₀ hx₀d) hF_meas hF_int hF'_meas h_lip ((hFint _ hcI).const_mul M₁) h_deriv
  -- rewrite the indicator integrals back to moving tail integrals on `I ∩ Ioi x`
  have hres := hderiv_ind.2.congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hcx₀ hx₀d] with x hx
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_Ioi_inter_Ioi_of_le hx.1.le])
  rwa [setIntegral_indicator measurableSet_Ioi, Set.inter_Ioi_inter_Ioi_of_le hcx₀.le] at hres

end Differentiability

end TauCeti
