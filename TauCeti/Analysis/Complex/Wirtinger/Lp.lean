/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# `Lᵖ` maps through their Wirtinger parts

A real-linear map `ℂ → F` with Wirtinger parts `a` and `b` is
`TauCeti.wirtingerPartsCLM a b = (v ↦ v • a + conj v • b)`. This file combines two maps
`a b : α → F` on a measure space pointwise through `wirtingerPartsCLM` and records the
measurability, `Lᵖ` membership, `Lᵖ` norm bounds and `Lᵖ` convergence of the result in terms of
those of the parts.

## Main results

* `MeasureTheory.MemLp.wirtingerPartsCLM`: `x ↦ wirtingerPartsCLM (a x) (b x)` is in `Lᵖ` when
  `a` and `b` are.
* `TauCeti.eLpNorm_wirtingerPartsCLM_le`: its `Lᵖ` norm is at most the sum of those of `a` and `b`.
* `TauCeti.tendsto_eLpNorm_wirtingerPartsCLM_sub`: `Lᵖ` convergence of the parts gives `Lᵖ`
  convergence of the combined maps.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `x ↦ wirtingerPartsCLM (a x) (b x)` is almost everywhere strongly measurable when both parts
are. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.wirtingerPartsCLM {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {a b : α → F} (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) :
    AEStronglyMeasurable (fun x ↦ TauCeti.wirtingerPartsCLM (a x) (b x)) μ := by
  simpa only [wirtingerPartsL_apply] using
    wirtingerPartsL.continuous.comp_aestronglyMeasurable (ha.prodMk hb)

/-- Pointwise combination of two `Lᵖ` maps through `wirtingerPartsCLM` stays in `Lᵖ`. -/
theorem _root_.MeasureTheory.MemLp.wirtingerPartsCLM {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} {a b : α → F} (ha : MemLp a p μ) (hb : MemLp b p μ) :
    MemLp (fun x ↦ TauCeti.wirtingerPartsCLM (a x) (b x)) p μ :=
  (ha.norm.add hb.norm).of_le (ha.aestronglyMeasurable.wirtingerPartsCLM hb.aestronglyMeasurable)
    (.of_forall fun x ↦
      (norm_wirtingerPartsCLM_le _ _).trans_eq (Real.norm_of_nonneg (by positivity)).symm)

/-- The `Lᵖ` norm of a map built by `wirtingerPartsCLM` is at most the sum of the `Lᵖ` norms of
its parts. -/
theorem eLpNorm_wirtingerPartsCLM_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ≥0∞} (hq : 1 ≤ q) {a b : α → F} (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) :
    eLpNorm (fun x ↦ wirtingerPartsCLM (a x) (b x)) q μ ≤ eLpNorm a q μ + eLpNorm b q μ := by
  calc _ ≤ eLpNorm (fun x ↦ ‖a x‖ + ‖b x‖) q μ :=
        eLpNorm_mono_real (ha.wirtingerPartsCLM hb) fun x ↦ norm_wirtingerPartsCLM_le _ _
    _ ≤ eLpNorm a q μ + eLpNorm b q μ := by
        refine (eLpNorm_add_le (f := fun x ↦ ‖a x‖) (g := fun x ↦ ‖b x‖) hq).trans_eq ?_
        rw [eLpNorm_norm _ ha, eLpNorm_norm _ hb]

/-- The `Lᵖ` distance of two maps built by `wirtingerPartsCLM` is at most the sum of the `Lᵖ`
distances of their parts. -/
theorem eLpNorm_wirtingerPartsCLM_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ≥0∞} (hq : 1 ≤ q) {a a' b b' : α → F} (ha : AEStronglyMeasurable (a - a') μ)
    (hb : AEStronglyMeasurable (b - b') μ) :
    eLpNorm (fun x ↦ wirtingerPartsCLM (a x) (b x) - wirtingerPartsCLM (a' x) (b' x)) q μ ≤
      eLpNorm (a - a') q μ + eLpNorm (b - b') q μ := by
  simp only [← wirtingerPartsCLM_sub]
  exact eLpNorm_wirtingerPartsCLM_le hq ha hb

/-- If the parts `a' i`, `b' i` tend to `a`, `b` in `Lᵖ`, then the maps
`wirtingerPartsCLM (a' i) (b' i)` tend to `wirtingerPartsCLM a b` in `Lᵖ`. -/
theorem tendsto_eLpNorm_wirtingerPartsCLM_sub {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ≥0∞} (hq : 1 ≤ q) {l : Filter ι} {a b : α → F} {a' b' : ι → α → F}
    (ha : ∀ i, AEStronglyMeasurable (a' i - a) μ) (hb : ∀ i, AEStronglyMeasurable (b' i - b) μ)
    (ha' : Tendsto (fun i ↦ eLpNorm (a' i - a) q μ) l (𝓝 0))
    (hb' : Tendsto (fun i ↦ eLpNorm (b' i - b) q μ) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm
        (fun x ↦ wirtingerPartsCLM (a' i x) (b' i x) - wirtingerPartsCLM (a x) (b x)) q μ)
      l (𝓝 0) := by
  have hup := ha'.add hb'
  rw [add_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ zero_le)
    fun i ↦ eLpNorm_wirtingerPartsCLM_sub_le hq (ha i) (hb i)


end TauCeti
