/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.Young

/-!
# Convolving a compactly supported function with a locally integrable kernel

Let `K` be a locally integrable kernel and `f` a function with compact support on a proper normed
additive group `G`, with a right-invariant s-finite measure. The kernels of potential theory, such
as the Newtonian kernel `‖x‖ ^ (2 - n)` and its derivatives, are locally integrable but not
integrable, so the convolution `K ⋆ f` is not covered by the theory of convolutions of integrable
functions. It still behaves like one locally:

* if `f` is integrable, `K ⋆ f` exists at almost every point
  (`HasCompactSupport.ae_convolutionExistsAt_right`) and is locally integrable
  (`HasCompactSupport.locallyIntegrable_convolution_right`);
* if `f ∈ Lᵖ`, `1 ≤ p`, then `K ⋆ f` lies in `Lᵖ` on every bounded set
  (`HasCompactSupport.memLp_convolution_right_of_isBounded`).

All three follow from one observation. At a point `x` of the closed ball `closedBall 0 R`, the
convolution `(K ⋆ f) x = ∫ L (K t) (f (x - t)) dt` only sees `K` on the compact set of differences
`closedBall 0 R - tsupport f`, so `K` may be replaced there by its indicator on that set
(`MeasureTheory.indicator_convolution_eq_of_forall_sub_mem`), which is integrable. The convolution
of two integrable functions exists almost everywhere and is integrable, and Young's inequality
(`MeasureTheory.eLpNorm_convolution_le`) bounds it in `Lᵖ`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Theorem 4.2 (Young's inequality).
-/

public section

namespace MeasureTheory

open Set Metric ContinuousLinearMap
open scoped Convolution

variable {𝕜 G E E' F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  (L : E →L[𝕜] E' →L[𝕜] F) {K : G → E} {f : G → E'}

section Proper

variable [NormedAddCommGroup G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G}

omit [MeasurableSpace G] [BorelSpace G] in
/-- The compact set of differences `x - y` with `‖x‖ ≤ R` and `y` in the support of `f`. -/
private theorem isCompact_image_sub_closedBall_prod (hfc : HasCompactSupport f) (R : ℝ) :
    IsCompact ((fun p : G × G ↦ p.1 - p.2) '' (closedBall 0 R ×ˢ tsupport f)) :=
  ((isCompact_closedBall 0 R).prod hfc).image (by fun_prop)

omit [ProperSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- At a point of `closedBall 0 R`, every `t` with `x - t` in the support of `f` is a difference
of a point of `closedBall 0 R` and a point of the support of `f`. -/
private theorem mem_image_sub_closedBall_prod {R : ℝ} {x : G} (hx : x ∈ closedBall 0 R) (t : G)
    (ht : x - t ∈ Function.support f) :
    t ∈ (fun p : G × G ↦ p.1 - p.2) '' (closedBall 0 R ×ˢ tsupport f) :=
  ⟨(x, x - t), mk_mem_prod hx (subset_tsupport f ht), sub_sub_cancel x t⟩

/-- The kernel restricted to the compact set `closedBall 0 R - tsupport f` is integrable. -/
private theorem integrable_indicator_image_sub (hK : LocallyIntegrable K μ)
    (hfc : HasCompactSupport f) (R : ℝ) :
    Integrable (((fun p : G × G ↦ p.1 - p.2) '' (closedBall 0 R ×ˢ tsupport f)).indicator K) μ :=
  have hS := isCompact_image_sub_closedBall_prod hfc R
  (hK.integrableOn_isCompact hS).integrable_indicator hS.measurableSet

variable [μ.IsAddRightInvariant] [SFinite μ]

omit [NormedSpace ℝ F] in
/-- **A locally integrable kernel convolves with a compactly supported integrable function almost
everywhere.** -/
theorem _root_.HasCompactSupport.ae_convolutionExistsAt_right (hfc : HasCompactSupport f)
    (hK : LocallyIntegrable K μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt K f x L μ := by
  have hk : ∀ k : ℕ, ∀ᵐ x ∂μ, ConvolutionExistsAt
      (((fun p : G × G ↦ p.1 - p.2) '' (closedBall 0 k ×ˢ tsupport f)).indicator K) f x L μ :=
    fun k ↦ (integrable_indicator_image_sub hK hfc k).ae_convolution_exists L hf
  filter_upwards [ae_all_iff.2 hk] with x hx
  obtain ⟨k, hxk⟩ := exists_nat_ge ‖x‖
  exact (convolutionExistsAt_indicator_iff_of_forall_sub_mem L
    (mem_image_sub_closedBall_prod (mem_closedBall_zero_iff.2 hxk))).1 (hx k)

/-- **The convolution of a locally integrable kernel with a compactly supported integrable
function is locally integrable.** -/
theorem _root_.HasCompactSupport.locallyIntegrable_convolution_right (hfc : HasCompactSupport f)
    (hK : LocallyIntegrable K μ) (hf : Integrable f μ) :
    LocallyIntegrable (K ⋆[L, μ] f) μ := by
  refine (locallyIntegrable_iff (μ := μ)).2 fun C hC ↦ ?_
  obtain ⟨R, hCR⟩ := hC.isBounded.subset_closedBall 0
  refine IntegrableOn.mono_set ?_ hCR
  have hint := (integrable_indicator_image_sub hK hfc R).integrable_convolution L hf
  exact hint.integrableOn.congr_fun (fun x hx ↦
    indicator_convolution_eq_of_forall_sub_mem L (mem_image_sub_closedBall_prod hx))
    measurableSet_closedBall

/-- **The convolution of a locally integrable kernel with a compactly supported `Lᵖ` function is
`Lᵖ` on bounded sets**, for `1 ≤ p`. -/
theorem _root_.HasCompactSupport.memLp_convolution_right_of_isBounded (hfc : HasCompactSupport f)
    (hK : LocallyIntegrable K μ) {p : ENNReal} (hf : MemLp f p μ) (hp : 1 ≤ p) {s : Set G}
    (hs : Bornology.IsBounded s) :
    MemLp (K ⋆[L, μ] f) p (μ.restrict s) := by
  obtain ⟨R, hsR⟩ := hs.subset_closedBall 0
  have hH := integrable_indicator_image_sub hK hfc R
  have hYoung : MemLp (((fun p : G × G ↦ p.1 - p.2) '' (closedBall 0 R ×ˢ tsupport f)).indicator K
      ⋆[L, μ] f) p μ :=
    (eLpNorm_convolution_le L hH.aestronglyMeasurable hf.aestronglyMeasurable hp).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top eNorm_lt_top
        (memLp_one_iff_integrable.2 hH).eLpNorm_lt_top) hf.eLpNorm_lt_top)
  refine ((hYoung.restrict (closedBall 0 R)).ae_eq ?_).mono_measure
    (Measure.restrict_mono hsR le_rfl)
  exact (ae_restrict_iff' measurableSet_closedBall).2 (.of_forall fun x hx ↦
    indicator_convolution_eq_of_forall_sub_mem L (mem_image_sub_closedBall_prod hx))

end Proper

end MeasureTheory
