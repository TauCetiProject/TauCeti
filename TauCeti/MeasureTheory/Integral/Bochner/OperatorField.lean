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

Operator fields that are eventually bounded along a countably generated filter and converge
almost everywhere preserve convergence of integrated pairings with velocities converging in
`L¹`. Separating the changes of field and velocity avoids a pointwise bound on the
approximating velocities, and no bound or measurability is assumed of the limit field.
For a fixed bounded multiplier, convergence holds along an arbitrary filter.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory

variable {α ι 𝕜 E F : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]

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

/-- Eventually bounded operator fields converging almost everywhere can be paired with
velocities converging in `L¹`. This gives convergence of the actual Bochner integrals. -/
theorem tendsto_integral_clm_apply_of_integral_norm_sub
    {ωn : ι → α → E →L[𝕜] F} {ω : α → E →L[𝕜] F}
    {vn : ι → α → E} {v : α → E} {C : ℝ}
    (hωn : ∀ᶠ n in l, AEStronglyMeasurable (ωn n) μ)
    (hboundn : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖ωn n x‖ ≤ C)
    (hωconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ωn n x) l (𝓝 (ω x)))
    (hvn : ∀ᶠ n in l, Integrable (vn n) μ) (hv : Integrable v μ)
    (hvconv : Tendsto (fun n ↦ ∫ x, ‖vn n x - v x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ωn n x (vn n x) ∂μ) l (𝓝 (∫ x, ω x (v x) ∂μ)) := by
  have hd : Tendsto (fun n ↦ ∫ x, ωn n x (vn n x - v x) ∂μ) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hvconv.const_mul C)
    filter_upwards [hboundn, hvn] with n hb hi
    calc
      ‖∫ x, ωn n x (vn n x - v x) ∂μ‖ ≤ ∫ x, C * ‖vn n x - v x‖ ∂μ :=
        norm_integral_le_of_norm_le ((hi.sub hv).norm.const_mul C) (by
          filter_upwards [hb] with x hx
          exact (ωn n x).le_of_opNorm_le hx _)
      _ = C * ∫ x, ‖vn n x - v x‖ ∂μ := integral_const_mul _ _
  have ht := (tendsto_integral_clm_apply_of_ae_tendsto hωn hboundn hωconv hv).add hd
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [hωn, hboundn, hvn] with n hm hb hi
  have hint {u : α → E} (hu : Integrable u μ) : Integrable (fun x ↦ ωn n x (u x)) μ :=
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).integrable_of_bilin_of_bdd_left C hm hb hu
  simpa using (integral_add (hint hv) (hint (hi.sub hv))).symm

omit [l.IsCountablyGenerated] in
/-- Multiplying `L¹`-convergent functions on the right by a fixed bounded measurable function
preserves convergence of their actual integrals, along any filter. -/
theorem tendsto_integral_mul_of_integral_norm_sub {A : Type*} [NonUnitalNormedRing A]
    [NormedSpace ℝ A] {wn : ι → α → A} {w R : α → A} {C : ℝ}
    (hwn : ∀ᶠ n in l, Integrable (wn n) μ) (hw : Integrable w μ)
    (hR : AEStronglyMeasurable R μ) (hbound : ∀ᵐ x ∂μ, ‖R x‖ ≤ C)
    (hconv : Tendsto (fun n ↦ ∫ x, ‖wn n x - w x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, wn n x * R x ∂μ) l (𝓝 (∫ x, w x * R x ∂μ)) := by
  have hle (u : α → A) : ∀ᵐ x ∂μ, ‖u x * R x‖ ≤ ‖u x‖ * C := by
    filter_upwards [hbound] with x hx
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hint {u : α → A} (hu : Integrable u μ) : Integrable (fun x ↦ u x * R x) μ :=
    (hu.norm.mul_const C).mono' (hu.1.mul hR) (hle u)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ (by simpa using hconv.mul_const C)
  filter_upwards [hwn] with n hn
  calc
    ‖∫ x, wn n x * R x ∂μ - ∫ x, w x * R x ∂μ‖ = ‖∫ x, (wn n x - w x) * R x ∂μ‖ := by
      simp only [sub_mul, integral_sub (hint hn) (hint hw)]
    _ ≤ ∫ x, ‖wn n x - w x‖ * C ∂μ :=
      norm_integral_le_of_norm_le ((hn.sub hw).norm.mul_const C) (hle fun x ↦ wn n x - w x)
    _ = (∫ x, ‖wn n x - w x‖ ∂μ) * C := integral_mul_const _ _

end MeasureTheory
