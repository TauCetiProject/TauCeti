/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Composing an `Lᵖ` family of operators with a bounded family

If `B : α → E →L[𝕜] F` is in `Lᵖ` and `A : α → F →L[𝕜] G` is measurable and almost everywhere
bounded by `C`, then the pointwise composition `x ↦ A x ∘L B x` is in `Lᵖ`, with
`‖A ∘ B‖_p ≤ C ‖B‖_p`. A continuous family on a compact set is such a bounded family. This is
the estimate behind the chain rule `D(g ∘ u) = Dg(u) ∘ Du` for continuous `u`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {α 𝕜 E F G : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {A : α → F →L[𝕜] G} {B : α → E →L[𝕜] F}
  {p : ℝ≥0∞}

/-- The `Lᵖ` seminorm of the pointwise composition `A ∘L B` is at most `C ‖B‖_p` when `A` is
almost everywhere bounded by `C`, for every exponent. -/
theorem eLpNorm_clm_comp_le_of_ae_nnnorm_le (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ) {C : ℝ≥0} (hC : ∀ᵐ x ∂μ, ‖A x‖₊ ≤ C) (p : ℝ≥0∞) :
    eLpNorm (fun x => (A x).comp (B x)) p μ ≤ C * eLpNorm B p μ := by
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    ((ContinuousLinearMap.compL 𝕜 E F G).continuous₂.comp_aestronglyMeasurable₂ hA hB) ?_ p
  filter_upwards [hC] with x hx
  exact (ContinuousLinearMap.opNNNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hx zero_le)

/-- The pointwise composition of a measurable, almost everywhere bounded family of operators with
an `Lᵖ` family is in `Lᵖ`. -/
theorem _root_.MeasureTheory.MemLp.clm_comp_of_ae_nnnorm_le (hB : MemLp B p μ)
    (hA : AEStronglyMeasurable A μ) {C : ℝ≥0} (hC : ∀ᵐ x ∂μ, ‖A x‖₊ ≤ C) :
    MemLp (fun x => (A x).comp (B x)) p μ :=
  memLp_iff.2 <| (eLpNorm_clm_comp_le_of_ae_nnnorm_le hA hB.aestronglyMeasurable hC p).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (memLp_iff.1 hB))

/-- On a compact set where the family `A` is continuous, its pointwise composition with an `Lᵖ`
family `B` is in `Lᵖ`. -/
theorem _root_.MeasureTheory.MemLp.clm_comp_of_continuousOn [TopologicalSpace α]
    [OpensMeasurableSpace α] {K : Set α} (hK : IsCompact K) (hKm : MeasurableSet K)
    (hA : ContinuousOn A K) (hB : MemLp B p (μ.restrict K)) :
    MemLp (fun x => (A x).comp (B x)) p (μ.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  refine hB.clm_comp_of_ae_nnnorm_le (hA.aestronglyMeasurable_of_isCompact hK hKm)
    (C := C.toNNReal) ?_
  filter_upwards [ae_restrict_mem hKm] with x hx
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC x hx).trans (Real.le_coe_toNNReal C)

end TauCeti
