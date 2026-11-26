/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.ENorm

/-!
# Lower Lebesgue integrals under uniform convergence

On a set of finite measure, uniform convergence implies `L¹` convergence
(`TendstoUniformlyOn.tendsto_setLIntegral_enorm_sub`).
Combined with `L¹` convergence of a second family, uniform convergence gives `L¹` convergence of
pointwise compositions of operator families: if `Aᵢ → A` uniformly on `s` with `A` bounded there,
and `Bᵢ → B` in `L¹(s)`, then `Aᵢ ∘L Bᵢ → A ∘L B` in `L¹(s)`
(`TendstoUniformlyOn.tendsto_setLIntegral_enorm_clm_comp_sub`). This is how the weak chain rule
passes from smooth approximations to the limit.
Uniform convergence also controls `L¹` convergence by comparison: a family dominated pointwise by
an `L¹`-null family plus a uniformly convergent one converges in `L¹(s)`
(`TendstoUniformlyOn.tendsto_setLIntegral_enorm_sub_of_le`).
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {ι α : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} {s : Set α}
  {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **`L¹` convergence of compositions.** If `Aᵢ → A` uniformly on `s`, with `‖A‖ ≤ C` on `s`, and
`Bᵢ → B` in `L¹(s)` with `B` integrable on `s`, then `Aᵢ ∘L Bᵢ → A ∘L B` in `L¹(s)`. -/
theorem _root_.TendstoUniformlyOn.tendsto_setLIntegral_enorm_clm_comp_sub
    {A' : ι → α → F →L[𝕜] G} {A : α → F →L[𝕜] G} {B' : ι → α → E →L[𝕜] F} {B : α → E →L[𝕜] F}
    (hA : TendstoUniformlyOn A' A l s)
    (hs : MeasurableSet s) {C : ℝ≥0} (hAC : ∀ x ∈ s, ‖A x‖₊ ≤ C)
    (hB' : ∀ i, AEStronglyMeasurable (B' i) (μ.restrict s))
    (hBm : AEStronglyMeasurable B (μ.restrict s))
    (hB : Tendsto (fun i => ∫⁻ x in s, ‖B' i x - B x‖ₑ ∂μ) l (𝓝 0))
    (hBint : ∫⁻ x in s, ‖B x‖ₑ ∂μ ≠ ∞) :
    Tendsto (fun i => ∫⁻ x in s, ‖(A' i x).comp (B' i x) - (A x).comp (B x)‖ₑ ∂μ) l (𝓝 0) := by
  set e := fun i => ⨆ x ∈ s, ‖A' i x - A x‖ₑ
  have he : Tendsto e l (𝓝 0) := hA.tendsto_iSup_enorm_sub
  have hlim : Tendsto (fun i => (e i + C) * ∫⁻ x in s, ‖B' i x - B x‖ₑ ∂μ +
      e i * ∫⁻ x in s, ‖B x‖ₑ ∂μ) l (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul (he.add_const (C : ℝ≥0∞)) (Or.inr (by simp)) hB
      (Or.inr (by simp))
    have h2 := ENNReal.Tendsto.mul_const he (Or.inr hBint)
    simpa only [zero_add, mul_zero, zero_mul, add_zero] using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun i => ?_
  have hmeas : AEMeasurable (fun x => ‖B' i x - B x‖ₑ) (μ.restrict s) :=
    ((hB' i).sub hBm).eNorm
  calc ∫⁻ x in s, ‖(A' i x).comp (B' i x) - (A x).comp (B x)‖ₑ ∂μ
      ≤ ∫⁻ x in s, ((e i + C) * ‖B' i x - B x‖ₑ + e i * ‖B x‖ₑ) ∂μ := by
        refine setLIntegral_mono' hs fun x hx =>
          (ContinuousLinearMap.enorm_comp_sub_comp_le _ _ _ _).trans ?_
        have hex : ‖A' i x - A x‖ₑ ≤ e i :=
          le_iSup₂ (f := fun x (_ : x ∈ s) => ‖A' i x - A x‖ₑ) x hx
        have hCx : ‖A x‖ₑ ≤ C := by
          simpa only [eNorm_eq_nnNorm, ENNReal.coe_le_coe] using hAC x hx
        calc _ ≤ e i * ‖B' i x - B x‖ₑ + e i * ‖B x‖ₑ + C * ‖B' i x - B x‖ₑ := by gcongr
          _ = _ := by ring
    _ = (e i + C) * ∫⁻ x in s, ‖B' i x - B x‖ₑ ∂μ + e i * ∫⁻ x in s, ‖B x‖ₑ ∂μ := by
        rw [lintegral_add_left' (hmeas.const_mul _), lintegral_const_mul'' _ hmeas,
          lintegral_const_mul'' _ hBm.eNorm]

/-- **`L¹` convergence by comparison with a uniformly convergent family.** Let `s` be a measurable
set of finite measure. If `‖Fᵢ x - f x‖ₑ ≤ ‖rᵢ x‖ₑ + ‖Gᵢ x - g x‖ₑ` on `s`, where `Gᵢ → g`
uniformly on `s` and `rᵢ → 0` in `L¹(s)`, then `Fᵢ → f` in `L¹(s)`. No measurability of the
functions is needed: the uniform part is bounded by a constant. -/
theorem _root_.TendstoUniformlyOn.tendsto_setLIntegral_enorm_sub_of_le {X Y Z : Type*}
    [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y] [ENorm Z]
    {F : ι → α → X} {f : α → X} {G : ι → α → Y} {g : α → Y} {r : ι → α → Z}
    (hG : TendstoUniformlyOn G g l s) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hr : Tendsto (fun i => ∫⁻ x in s, ‖r i x‖ₑ ∂μ) l (𝓝 0))
    (hle : ∀ i, ∀ x ∈ s, ‖F i x - f x‖ₑ ≤ ‖r i x‖ₑ + ‖G i x - g x‖ₑ) :
    Tendsto (fun i => ∫⁻ x in s, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0) := by
  refine tendsto_lintegral_zero_of_le_add (μ := μ.restrict s)
    (g := fun i _ => ⨆ x ∈ s, ‖G i x - g x‖ₑ) (h := fun i x => ‖r i x‖ₑ)
    (.of_forall fun i => ae_restrict_of_forall_mem hs fun x hx => (hle i x hx).trans_eq
      (add_comm _ _) |>.trans (add_le_add_left
        (le_iSup₂ (f := fun x (_ : x ∈ s) => ‖G i x - g x‖ₑ) x hx) _))
    (.of_forall fun _ => aemeasurable_const) ?_ hr
  simpa [setLIntegral_const] using
    ENNReal.Tendsto.mul_const hG.tendsto_iSup_enorm_sub (Or.inr hμs)

end TauCeti
