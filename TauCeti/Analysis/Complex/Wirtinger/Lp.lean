/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# `Lᵖ` maps through their Wirtinger parts

A real-linear map `ℂ → F` with Wirtinger parts `a` and `b` is
`TauCeti.wirtingerPartsCLM a b = (v ↦ v • a + conj v • b)`. This file combines two maps
`a b : α → F` on a measure space pointwise through `wirtingerPartsCLM` and records the
measurability, `Lᵖ` membership, `Lᵖ` norm bounds and `Lᵖ` convergence of the result in terms of
those of the parts.

## Main results

* `TauCeti.Wirtinger.jetL`, `TauCeti.Wirtinger.coe_jetL`, `TauCeti.Wirtinger.jetL_smul`:
  a bounded value operator and the source field determine a global Wirtinger jet.
* `MeasureTheory.MemLp.wirtingerPartsCLM`: `x ↦ wirtingerPartsCLM (a x) (b x)` is in `Lᵖ` when
  `a` and `b` are.
* `TauCeti.eLpNorm_wirtingerPartsCLM_le`: its `Lᵖ` norm is at most the sum of those of `a` and `b`.
* `TauCeti.tendsto_eLpNorm_wirtingerPartsCLM_sub`: `Lᵖ` convergence of the parts gives `Lᵖ`
  convergence of the combined maps.
-/

public noncomputable section

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


namespace Wirtinger

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded operator on values determines a bounded global Wirtinger jet. -/
def jetL
    (B : Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ)) :
    Lp F p (volume : Measure ℂ) →L[ℝ] Lp (ℂ →L[ℝ] F) p (volume : Measure ℂ) :=
  (((wirtingerPartsL (W := F)).comp (ContinuousLinearMap.inl ℝ F F)).compLpL p (volume :
    Measure ℂ)).comp
      (B.restrictScalars ℝ) +
    ((wirtingerPartsL (W := F)).comp (ContinuousLinearMap.inr ℝ F F)).compLpL p (volume : Measure ℂ)

/-- The global jet has the Wirtinger formula. -/
theorem coe_jetL
    (B : Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ))
    (u : Lp F p (volume : Measure ℂ)) :
    jetL B u =ᵐ[(volume : Measure ℂ)] fun w ↦ wirtingerPartsCLM (B u w) (u w) := by
  let a : F →L[ℝ] ℂ →L[ℝ] F :=
    (wirtingerPartsL (W := F)).comp (ContinuousLinearMap.inl ℝ F F)
  let b : F →L[ℝ] ℂ →L[ℝ] F :=
    (wirtingerPartsL (W := F)).comp (ContinuousLinearMap.inr ℝ F F)
  -- Expose the two native component fields for their separate a.e. evaluation laws.
  change (a.compLpL p volume (B u) + b.compLpL p volume u :
    Lp (ℂ →L[ℝ] F) p volume) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add (a.compLpL p volume (B u)) (b.compLpL p volume u),
    a.coeFn_compLpL (B u), b.coeFn_compLpL u] with w hadd ha hb
  rw [hadd]
  simp only [Pi.add_apply]
  rw [ha, hb]
  ext v
  simp [a, b, wirtingerPartsCLM_apply]

/-- The global Wirtinger jet respects the complex scalar action. -/
theorem jetL_smul (B : Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ))
    (a : ℂ) (u : Lp F p (volume : Measure ℂ)) : jetL B (a • u) = a • jetL B u := by
  apply Lp.ext
  have hB := map_smul B a u
  filter_upwards [coe_jetL B (a • u), coe_jetL B u, Lp.coeFn_smul a u,
    Lp.coeFn_smul a (B u), Lp.coeFn_smul a (jetL B u)] with w h₁ h₂ h₃ h₄ h₅
  rw [hB] at h₁
  simp only [h₁, h₂, h₃, h₄, h₅, Pi.smul_apply, wirtingerPartsCLM_smul]

end Wirtinger

end TauCeti
