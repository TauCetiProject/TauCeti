/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# Set integrals under uniform convergence

On a compact measurable set `s`, for a measure that is finite on compact sets, uniform
convergence of continuous functions on `s` implies convergence of their integrals over `s`
(`TendstoUniformlyOn.tendsto_setIntegral_of_continuousOn`). This is the set-integral analogue of
Mathlib's `TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn`, and it is proved the same
way, by dominated convergence with a constant bound.
-/

public section

open Filter MeasureTheory Topology

variable {ι α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {l : Filter ι} [l.IsCountablyGenerated] {F : ι → α → E} {f : α → E} {s : Set α}

/-- **Set integrals of uniformly convergent continuous functions converge.** If continuous
functions `F i` converge uniformly on a compact measurable set `s` to `f`, then their integrals
over `s` converge to the integral of `f` over `s`, for any measure finite on compact sets. -/
theorem TendstoUniformlyOn.tendsto_setIntegral_of_continuousOn (hs : IsCompact s)
    (hs' : MeasurableSet s) (hF : ∀ᶠ i in l, ContinuousOn (F i) s)
    (h_lim : TendstoUniformlyOn F f l s) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rcases hs.bddAbove_image (h_lim.continuousOn hF.frequently).norm with ⟨C, hC⟩
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.measure_lt_top.ne
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C + 1)
    (hF.mono fun i hi ↦ hi.aestronglyMeasurable_of_isCompact hs hs') ?_ (integrable_const _)
    ((ae_restrict_iff' hs').2 (.of_forall fun x hx ↦ h_lim.tendsto_at hx))
  -- Eventually the norms `‖F i‖` are below `C + 1` on `s`, since `‖f‖ ≤ C` there.
  have hnorm : TendstoUniformlyOn (fun i x ↦ ‖F i x‖) (fun x ↦ ‖f x‖) l s :=
    uniformContinuous_norm.comp_tendstoUniformlyOn h_lim
  have := hnorm.eventually_forall_le (show C < C + 1 by simp) (by simpa [upperBounds] using hC)
  exact this.mono fun i hi ↦ (ae_restrict_iff' hs').2 (.of_forall hi)
