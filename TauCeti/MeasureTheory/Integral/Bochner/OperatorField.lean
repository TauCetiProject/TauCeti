/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Convergence of integrals of bounded operator fields

Pairing integrable functions that converge in `L¹` with a fixed bounded measurable operator
field gives convergence of the Bochner integrals of the pairings, along an arbitrary filter; the
case of right multiplication by a fixed bounded measurable function in a normed ring follows.
Both rest on the fact that pairing integrable functions tending to zero in `L¹` with eventually
uniformly bounded operator fields gives integrals tending to zero. Pairing `L¹`-convergent
integrable functions with eventually bounded operator fields that converge almost everywhere
likewise gives convergence of the Bochner integrals of the pairings, along a countably generated
filter. Separating the changes of field and function avoids a pointwise bound on the
approximating functions, and no bound or measurability is assumed of the limit field.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory

variable {α ι 𝕜 E F : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]

omit [l.IsCountablyGenerated] in
/-- Pairing integrable functions tending to zero in `L¹` with operator fields that are eventually
bounded almost everywhere by a common constant gives Bochner integrals of the pairings tending to
zero, along any filter. No measurability of the operator fields is needed. -/
theorem tendsto_integral_clm_apply_of_integral_norm {ωn : ι → α → E →L[𝕜] F}
    {un : ι → α → E} {C : ℝ} (hboundn : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖ωn n x‖ ≤ C)
    (hun : ∀ᶠ n in l, Integrable (un n) μ)
    (hconv : Tendsto (fun n ↦ ∫ x, ‖un n x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ωn n x (un n x) ∂μ) l (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using hconv.const_mul C)
  filter_upwards [hboundn, hun] with n hb hi
  calc
    ‖∫ x, ωn n x (un n x) ∂μ‖ ≤ ∫ x, C * ‖un n x‖ ∂μ :=
      norm_integral_le_of_norm_le (hi.norm.const_mul C) (by
        filter_upwards [hb] with x hx
        exact (ωn n x).le_of_opNorm_le hx _)
    _ = C * ∫ x, ‖un n x‖ ∂μ := integral_const_mul _ _

omit [l.IsCountablyGenerated] in
/-- Pairing integrable functions converging in `L¹` with a fixed bounded measurable operator
field gives convergence of the Bochner integrals of the pairings, along any filter. -/
theorem tendsto_integral_clm_apply_of_integral_norm_sub {ω : α → E →L[𝕜] F}
    {vn : ι → α → E} {v : α → E} {C : ℝ}
    (hω : AEStronglyMeasurable ω μ) (hbound : ∀ᵐ x ∂μ, ‖ω x‖ ≤ C)
    (hvn : ∀ᶠ n in l, Integrable (vn n) μ) (hv : Integrable v μ)
    (hvconv : Tendsto (fun n ↦ ∫ x, ‖vn n x - v x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ω x (vn n x) ∂μ) l (𝓝 (∫ x, ω x (v x) ∂μ)) := by
  have hint {u : α → E} (hu : Integrable u μ) : Integrable (fun x ↦ ω x (u x)) μ :=
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).integrable_of_bilin_of_bdd_left C hω hbound hu
  rw [← tendsto_sub_nhds_zero_iff]
  refine (tendsto_integral_clm_apply_of_integral_norm (ωn := fun _ ↦ ω)
    (un := fun n x ↦ vn n x - v x) (.of_forall fun _ ↦ hbound)
    (hvn.mono fun _ hn ↦ hn.sub hv) hvconv).congr' ?_
  filter_upwards [hvn] with n hn
  simp only [map_sub, integral_sub (hint hn) (hint hv)]

/-- Eventually bounded operator fields converging almost everywhere, applied to a fixed
integrable vector field, have convergent integrals. -/
theorem tendsto_integral_clm_apply_of_ae_tendsto
    {ωn : ι → α → E →L[𝕜] F} {ω : α → E →L[𝕜] F} {v : α → E} {C : ℝ}
    (hωn : ∀ᶠ n in l, AEStronglyMeasurable (ωn n) μ)
    (hboundn : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖ωn n x‖ ≤ C)
    (hωconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ωn n x) l (𝓝 (ω x)))
    (hv : Integrable v μ) :
    Tendsto (fun n ↦ ∫ x, ωn n x (v x) ∂μ) l (𝓝 (∫ x, ω x (v x) ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖v x‖) ?_ ?_
    (hv.norm.const_mul C) ?_
  · filter_upwards [hωn] with n hn
    exact (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).aestronglyMeasurable_comp₂ hn hv.1
  · filter_upwards [hboundn] with n hn
    filter_upwards [hn] with x hx
    exact (ωn n x).le_of_opNorm_le hx (v x)
  · filter_upwards [hωconv] with x hx
    exact ((continuous_eval_const (v x)).tendsto (ω x)).comp hx

/-- Pairing integrable functions converging in `L¹` with eventually bounded operator fields
converging almost everywhere gives convergence of the Bochner integrals of the pairings, along a
countably generated filter. -/
theorem tendsto_integral_clm_apply_of_ae_tendsto_of_integral_norm_sub
    {ωn : ι → α → E →L[𝕜] F} {ω : α → E →L[𝕜] F}
    {vn : ι → α → E} {v : α → E} {C : ℝ}
    (hωn : ∀ᶠ n in l, AEStronglyMeasurable (ωn n) μ)
    (hboundn : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖ωn n x‖ ≤ C)
    (hωconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ωn n x) l (𝓝 (ω x)))
    (hvn : ∀ᶠ n in l, Integrable (vn n) μ) (hv : Integrable v μ)
    (hvconv : Tendsto (fun n ↦ ∫ x, ‖vn n x - v x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ωn n x (vn n x) ∂μ) l (𝓝 (∫ x, ω x (v x) ∂μ)) := by
  have hd := tendsto_integral_clm_apply_of_integral_norm (un := fun n x ↦ vn n x - v x)
    hboundn (hvn.mono fun _ hn ↦ hn.sub hv) hvconv
  have ht := (tendsto_integral_clm_apply_of_ae_tendsto hωn hboundn hωconv hv).add hd
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [hωn, hboundn, hvn] with n hm hb hi
  have hint {u : α → E} (hu : Integrable u μ) : Integrable (fun x ↦ ωn n x (u x)) μ :=
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).integrable_of_bilin_of_bdd_left C hm hb hu
  simpa using (integral_add (hint hv) (hint (hi.sub hv))).symm

omit [l.IsCountablyGenerated] in
/-- Multiplying integrable functions converging in `L¹` on the right by a fixed bounded
measurable function gives convergence of the Bochner integrals of the products, along any
filter. -/
theorem tendsto_integral_mul_of_integral_norm_sub {A : Type*} [NonUnitalNormedRing A]
    [NormedSpace ℝ A] {wn : ι → α → A} {w R : α → A} {C : ℝ}
    (hwn : ∀ᶠ n in l, Integrable (wn n) μ) (hw : Integrable w μ)
    (hR : AEStronglyMeasurable R μ) (hbound : ∀ᵐ x ∂μ, ‖R x‖ ≤ C)
    (hconv : Tendsto (fun n ↦ ∫ x, ‖wn n x - w x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, wn n x * R x ∂μ) l (𝓝 (∫ x, w x * R x ∂μ)) := by
  -- Multiplication is additive and continuous in each argument, hence automatically
  -- `ℝ`-bilinear; this makes right multiplication by `R x` a continuous `ℝ`-linear map.
  have : IsScalarTower ℝ A A := ⟨fun c u r ↦ by
    simpa only [AddMonoidHom.mulRight_apply, smul_eq_mul] using
      map_real_smul (AddMonoidHom.mulRight r) (continuous_mul_const r) c u⟩
  have : SMulCommClass ℝ A A := ⟨fun c u r ↦ by
    simpa only [AddMonoidHom.coe_mulLeft, smul_eq_mul] using
      (map_real_smul (AddMonoidHom.mulLeft u) (continuous_const_mul u) c r).symm⟩
  have hnorm (r : A) : ‖(ContinuousLinearMap.mul ℝ A).flip r‖ ≤ ‖r‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg r) fun u ↦ by
      rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_comm ‖r‖]
      exact norm_mul_le u r
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    tendsto_integral_clm_apply_of_integral_norm_sub
      ((ContinuousLinearMap.mul ℝ A).flip.continuous.comp_aestronglyMeasurable hR)
      (hbound.mono fun x hx ↦ (hnorm (R x)).trans hx) hwn hw hconv

end MeasureTheory
