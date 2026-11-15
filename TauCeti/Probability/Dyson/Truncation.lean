/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Dyson.System
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.ODE.Nonautonomous

/-!
# Globally Lipschitz truncated Dyson trajectories and chamber localization

Following Anderson--Guionnet--Zeitouni (§4.3.1, Lemma 4.3.3), singular pairwise collisions are
localized by replacing `dysonDrift n` with the globally `(2 / δ²)`-Lipschitz field
`dysonDriftTrunc n δ` (`0 < δ`). Subtracting a continuous additive forcing path
`w : ℝ≥0 → Fin n → ℝ` turns the integral equation
`γ t = x + w t + ∫ s in 0..t, dysonDriftTrunc n δ (γ s.toNNReal)`
into the nonautonomous ODE `u' s = dysonDriftTrunc n δ (u s + w s.toNNReal)` with continuous time
dependence and state-uniform Lipschitz constant `2 / δ²`, solved globally on `ℝ` by
`ODE.nonautonomousGlobalSolution`.

Because `dysonDriftTrunc n δ` agrees with `dysonDrift n` on the `δ`-separated chamber
`{z | ∀ i < j, δ ≤ z i - z j}`, ODE uniqueness (`ODE.eqOn_Icc_of_hasDerivAt`) yields:

* **Consistency across thresholds** (`dysonTruncPath_eq_of_le_of_mem_chamber`): for `0 < δ₁ ≤ δ₂`,
  `dysonTruncPath` at threshold `δ₁` agrees with `dysonTruncPath` at threshold `δ₂` on `[0, T]`
  whenever the `δ₂`-trajectory remains in the `δ₂`-chamber throughout `[0, T]`.
* **Agreement with any Dyson path before exit** (`IsDysonPath.eq_dysonTruncPath_of_mem_chamber`):
  any `IsDysonPath` staying in the `δ`-chamber on `[0, T]` coincides with `dysonTruncPath` there.
* **Pasting into a global solution** (`exists_isDysonPath_of_forall_exists_trunc_mem_chamber` and
  `exists_isDysonSolution_of_ae_trunc_mem_chamber`): once every finite horizon `[0, T]` admits a
  positive gap threshold `δ` up to which `dysonTruncPath` avoids the `δ`-boundary, the truncated
  solutions paste into a global `IsDysonPath` (and almost surely into `IsDysonSolution`).

## Main declarations

* `TauCeti.Probability.dysonTruncPath`: unique global trajectory of the `δ`-truncated Dyson system
  driven by a continuous path `w`.
* `TauCeti.Probability.dysonTruncPath_apply` and `TauCeti.Probability.sum_dysonTruncPath`:
  coordinatewise integral equation and center-of-mass conservation.
* `TauCeti.Probability.dysonTruncPath_eq_of_le_of_mem_chamber`: compatibility of truncations up to
  exit from the `δ₂`-chamber.
* `TauCeti.Probability.IsDysonPath.eq_dysonTruncPath_of_mem_chamber`: local agreement between any
  `IsDysonPath` and `dysonTruncPath` on `[0, T]`.
* `TauCeti.Probability.exists_isDysonPath_of_forall_exists_trunc_mem_chamber` and
  `TauCeti.Probability.exists_isDysonSolution_of_ae_trunc_mem_chamber`: pasting non-exiting
  truncated trajectories into `IsDysonPath` and `IsDysonSolution`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1, Lemma 4.3.3.
-/

public section

open Finset Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-! ### Truncated Dyson trajectory via nonautonomous ODE -/

/-- Shifted nonautonomous vector field `v s z = dysonDriftTrunc n δ (z + w s.toNNReal)`. -/
private noncomputable def dysonTruncField (n : ℕ) (δ : ℝ) (w : ℝ≥0 → Fin n → ℝ) (s : ℝ)
    (z : Fin n → ℝ) : Fin n → ℝ :=
  dysonDriftTrunc n δ (z + w s.toNNReal)

private theorem continuous_dysonTruncField_left (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (z : Fin n → ℝ) :
    Continuous (fun s : ℝ ↦ dysonTruncField n δ w s z) :=
  (continuous_dysonDriftTrunc n hδ).comp
    (continuous_const.add (hw.comp continuous_real_toNNReal))

private theorem lipschitzWith_dysonTruncField (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (w : ℝ≥0 → Fin n → ℝ) (s : ℝ) :
    LipschitzWith (2 / Real.toNNReal δ ^ 2) (dysonTruncField n δ w s) :=
  LipschitzWith.of_dist_le_mul fun y z ↦ by
    simpa [dysonTruncField] using
      (lipschitzWith_dysonDriftTrunc n hδ).dist_le_mul (y + w s.toNNReal) (z + w s.toNNReal)

/-- Smooth drift part `u` solving `u' s = dysonDriftTrunc n δ (u s + w s.toNNReal)` from `x`. -/
private noncomputable def dysonTruncSmooth (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) : ℝ → Fin n → ℝ :=
  ODE.nonautonomousGlobalSolution (dysonTruncField n δ w)
    (continuous_dysonTruncField_left n hδ hw) (lipschitzWith_dysonTruncField n hδ w) 0 x

private theorem dysonTruncSmooth_zero (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    dysonTruncSmooth n hδ x hw 0 = x :=
  ODE.nonautonomousGlobalSolution_self _ _ _ 0 x

private theorem hasDerivAt_dysonTruncSmooth (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (s : ℝ) :
    HasDerivAt (dysonTruncSmooth n hδ x hw)
      (dysonTruncField n δ w s (dysonTruncSmooth n hδ x hw s)) s :=
  ODE.hasDerivAt_nonautonomousGlobalSolution _ _ _ 0 x s

private theorem continuous_dysonTruncSmooth (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    Continuous (dysonTruncSmooth n hδ x hw) :=
  ODE.continuous_nonautonomousGlobalSolution_apply _ _ _ 0 x

/-- **Global trajectory of the `δ`-truncated Dyson system** (`0 < δ`) started from `x` and driven
by a continuous path `w : ℝ≥0 → Fin n → ℝ`, satisfying
`dysonTruncPath n hδ x hw t i = x i + w t i + ∫ s in 0..t, dysonDriftTrunc n δ (...) i`. -/
noncomputable def dysonTruncPath (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (t : ℝ≥0) : Fin n → ℝ :=
  dysonTruncSmooth n hδ x hw t + w t

/-- At time `0`, `dysonTruncPath` evaluates to `x + w 0`. -/
@[simp]
theorem dysonTruncPath_zero (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    dysonTruncPath n hδ x hw 0 = x + w 0 := by
  simp [dysonTruncPath, dysonTruncSmooth_zero]

/-- If `w 0 = 0`, `dysonTruncPath` starts at `x`. -/
theorem dysonTruncPath_zero_of_eq_zero (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    dysonTruncPath n hδ x hw 0 = x := by
  rw [dysonTruncPath_zero, hw0, add_zero]

/-- Continuity of `dysonTruncPath` on `ℝ≥0`. -/
theorem continuous_dysonTruncPath (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    Continuous (dysonTruncPath n hδ x hw) :=
  ((continuous_dysonTruncSmooth n hδ x hw).comp NNReal.continuous_coe).add hw

/-- **Coordinatewise integral equation** satisfied by `dysonTruncPath`. -/
theorem dysonTruncPath_apply (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (t : ℝ≥0) (i : Fin n) :
    dysonTruncPath n hδ x hw t i = x i + w t i +
      ∫ s in (0 : ℝ)..t, dysonDriftTrunc n δ (dysonTruncPath n hδ x hw s.toNNReal) i := by
  set u := dysonTruncSmooth n hδ x hw
  have hcont : Continuous (fun s : ℝ ↦ dysonTruncField n δ w s (u s) i) :=
    (continuous_apply i).comp <| (continuous_dysonDriftTrunc n hδ).comp <|
      (continuous_dysonTruncSmooth n hδ x hw).add (hw.comp continuous_real_toNNReal)
  have hint := _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_pi.1 (hasDerivAt_dysonTruncSmooth n hδ x hw s) i)
    (hcont.intervalIntegrable 0 t)
  have hcongr : ∫ s in (0 : ℝ)..t, dysonTruncField n δ w s (u s) i =
      ∫ s in (0 : ℝ)..t, dysonDriftTrunc n δ (dysonTruncPath n hδ x hw s.toNNReal) i := by
    refine _root_.intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
    simp [dysonTruncField, dysonTruncPath, u, Real.coe_toNNReal s hs.1]
  rw [← hcongr, hint, dysonTruncSmooth_zero]
  simp only [dysonTruncPath, Pi.add_apply]
  ring

/-- **Center-of-mass conservation** for the truncated Dyson trajectory. -/
theorem sum_dysonTruncPath (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (t : ℝ≥0) :
    ∑ i, dysonTruncPath n hδ x hw t i = (∑ i, x i) + ∑ i, w t i := by
  have hcont : ∀ i : Fin n,
      IntervalIntegrable (fun s : ℝ ↦ dysonDriftTrunc n δ (dysonTruncPath n hδ x hw s.toNNReal) i)
        volume 0 t := fun i ↦
    ((continuous_apply i).comp <| (continuous_dysonDriftTrunc n hδ).comp <|
      (continuous_dysonTruncPath n hδ x hw).comp continuous_real_toNNReal).intervalIntegrable 0 t
  have hsum : ∑ i, dysonTruncPath n hδ x hw t i = (∑ i, x i) + (∑ i, w t i) +
      ∑ i, ∫ s in (0 : ℝ)..t, dysonDriftTrunc n δ (dysonTruncPath n hδ x hw s.toNNReal) i := by
    simp_rw [dysonTruncPath_apply n hδ x hw t]
    simp [sum_add_distrib, add_assoc]
  rw [hsum, ← _root_.intervalIntegral.integral_finsetSum fun i _ ↦ hcont i]
  simp [sum_dysonDriftTrunc]

/-! ### Local compatibility and pasting before chamber exit -/

/-- **Threshold compatibility up to chamber exit.** For `0 < δ₁ ≤ δ₂`, if `dysonTruncPath` at
threshold `δ₂` stays inside `{z | ∀ i < j, δ₂ ≤ z i - z j}` throughout `[0, T]`, then
`dysonTruncPath` at threshold `δ₁` agrees with it throughout `[0, T]`. -/
theorem dysonTruncPath_eq_of_le_of_mem_chamber {n : ℕ} {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hle : δ₁ ≤ δ₂) {x : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hch : ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
      δ₂ ≤ dysonTruncPath n (hδ₁.trans_le hle) x hw t i -
        dysonTruncPath n (hδ₁.trans_le hle) x hw t j) :
    ∀ t ∈ Icc (0 : ℝ≥0) T,
      dysonTruncPath n hδ₁ x hw t = dysonTruncPath n (hδ₁.trans_le hle) x hw t := by
  set hδ₂ : 0 < δ₂ := hδ₁.trans_le hle
  have hu : EqOn (dysonTruncSmooth n hδ₁ x hw) (dysonTruncSmooth n hδ₂ x hw) (Icc 0 (T : ℝ)) := by
    refine ODE.eqOn_Icc_of_hasDerivAt (a := 0) (b := T) (c := 0)
      (fun s _ ↦ lipschitzWith_dysonTruncField n hδ₁ w s) le_rfl (NNReal.coe_nonneg T)
      (fun s _ ↦ hasDerivAt_dysonTruncSmooth n hδ₁ x hw s) (fun s hs ↦ ?_)
      (by rw [dysonTruncSmooth_zero, dysonTruncSmooth_zero])
    have hs_nn : s.toNNReal ∈ Icc (0 : ℝ≥0) T :=
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
    have hst : dysonTruncSmooth n hδ₂ x hw s + w s.toNNReal =
        dysonTruncPath n hδ₂ x hw s.toNNReal := by
      simp [dysonTruncPath, Real.coe_toNNReal s hs.1]
    have htr : dysonTruncField n δ₂ w s (dysonTruncSmooth n hδ₂ x hw s) =
        dysonTruncField n δ₁ w s (dysonTruncSmooth n hδ₂ x hw s) := by
      simp only [dysonTruncField, hst]
      rw [dysonDriftTrunc_eq_dysonDrift (hch s.toNNReal hs_nn),
        dysonDriftTrunc_eq_dysonDrift fun i j hij ↦ hle.trans (hch s.toNNReal hs_nn hij)]
    rw [← htr]
    exact hasDerivAt_dysonTruncSmooth n hδ₂ x hw s
  intro t ht
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.2 ht.2⟩
  simp only [dysonTruncPath, hu ht']

/-- **Local agreement of any Dyson path with `dysonTruncPath` before chamber exit.** If `γ` solves
`IsDysonPath n x w γ` for continuous `w` and stays inside the `δ`-chamber
`{z | ∀ i < j, δ ≤ z i - z j}` on `[0, T]` (`0 < δ`), then `γ` coincides with
`dysonTruncPath n hδ x hw` on `[0, T]`. -/
theorem IsDysonPath.eq_dysonTruncPath_of_mem_chamber {n : ℕ} {x : Fin n → ℝ}
    {w γ : ℝ≥0 → Fin n → ℝ} (hγ : IsDysonPath n x w γ) (hw : Continuous w) {δ : ℝ} (hδ : 0 < δ)
    {T : ℝ≥0} (hch : ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j → δ ≤ γ t i - γ t j) :
    ∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t := by
  have hdr_cont : Continuous (fun r : ℝ ↦ dysonDrift n (γ r.toNNReal)) := by
    refine continuous_iff_continuousAt.2 fun v ↦ ?_
    have hinj : Function.Injective (γ v.toNNReal) := by
      rcases le_or_gt v 0 with hv | hv
      · rw [Real.toNNReal_of_nonpos hv]
        exact (StrictAnti.injective fun i j hij ↦
          sub_pos.1 (hδ.trans_le (hch 0 ⟨le_rfl, zero_le⟩ hij)))
      · exact (hγ.strictAnti (Real.toNNReal_pos.2 hv)).injective
    exact ContinuousAt.comp (continuousAt_dysonDrift hinj)
      (hγ.continuous.comp continuous_real_toNNReal).continuousAt
  set g : ℝ → Fin n → ℝ := fun s i ↦ x i + ∫ r in (0 : ℝ)..s, dysonDrift n (γ r.toNNReal) i
  have hgc : ∀ s : ℝ, 0 ≤ s → g s + w s.toNNReal = γ s.toNNReal := fun s hs ↦ by
    ext i
    have heq := hγ.apply_eq s.toNNReal i
    rw [Real.coe_toNNReal s hs] at heq
    simp only [g, Pi.add_apply, heq]
    ring
  have hg_eq : EqOn g (dysonTruncSmooth n hδ x hw) (Icc 0 (T : ℝ)) := by
    refine ODE.eqOn_Icc_of_hasDerivAt (a := 0) (b := T) (c := 0)
      (fun s _ ↦ lipschitzWith_dysonTruncField n hδ w s) le_rfl (NNReal.coe_nonneg T)
      (fun s hs ↦ ?_) (fun s _ ↦ hasDerivAt_dysonTruncSmooth n hδ x hw s)
      (by ext i; simp [g, dysonTruncSmooth_zero])
    have htr : dysonTruncField n δ w s (g s) = dysonDrift n (γ s.toNNReal) := by
      have hs_nn : s.toNNReal ∈ Icc (0 : ℝ≥0) T :=
        ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
      rw [dysonTruncField, hgc s hs.1, dysonDriftTrunc_eq_dysonDrift (hch s.toNNReal hs_nn)]
    rw [htr]
    refine hasDerivAt_pi.2 fun i ↦ ?_
    have hfi : Continuous (fun r : ℝ ↦ dysonDrift n (γ r.toNNReal) i) :=
      (continuous_apply i).comp hdr_cont
    exact (_root_.intervalIntegral.integral_hasDerivAt_right (hfi.intervalIntegrable 0 s)
      (hfi.stronglyMeasurableAtFilter volume (𝓝 s)) hfi.continuousAt).const_add (x i)
  intro t ht
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.2 ht.2⟩
  have hgt := hgc t (NNReal.coe_nonneg t)
  simp only [Real.toNNReal_coe] at hgt
  rw [← hgt, hg_eq ht', dysonTruncPath]

/-- Any trajectory `γ` that agrees on every compact horizon `[0, T]` with some `δ`-truncated Dyson
trajectory staying inside the `δ`-chamber on `[0, T]` is a global `IsDysonPath`. -/
theorem isDysonPath_of_forall_exists_eq_dysonTruncPath {n : ℕ} {x : Fin n → ℝ}
    {w γ : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hloc : ∀ T : ℝ≥0, ∃ (δ : ℝ) (hδ : 0 < δ),
      (∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t) ∧
      (∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j → δ ≤ γ t i - γ t j)) :
    IsDysonPath n x w γ := by
  have hγ_cont : Continuous γ := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    obtain ⟨δ, hδ, heq, -⟩ := hloc (t + 1)
    refine ((continuous_dysonTruncPath n hδ x hw).continuousAt).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds (lt_add_one t)] with s (hs : s < t + 1)
    exact heq s ⟨zero_le, hs.le⟩
  have hγ_strict : ∀ t : ℝ≥0, 0 < t → StrictAnti (γ t) := fun t _ i j hij ↦ by
    obtain ⟨δ, hδ, -, hgap⟩ := hloc t
    exact sub_pos.1 (hδ.trans_le (hgap t ⟨zero_le, le_rfl⟩ hij))
  refine isDysonPath_iff.2 ⟨hγ_cont, hγ_strict, fun t i ↦ ?_⟩
  obtain ⟨δ, hδ, heq, hgap⟩ := hloc t
  have hs_mem : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) t → s.toNNReal ∈ Icc (0 : ℝ≥0) t :=
    fun hs ↦ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
  have hsum_cont : ContinuousOn
      (fun s : ℝ ↦ ∑ j ∈ univ.erase i, (γ s.toNNReal i - γ s.toNNReal j)⁻¹) (Icc 0 (t : ℝ)) := by
    refine continuousOn_finsetSum _ fun j hj ↦ ?_
    refine (((continuous_apply i).comp (hγ_cont.comp continuous_real_toNNReal)).sub
      ((continuous_apply j).comp (hγ_cont.comp continuous_real_toNNReal))).continuousOn.inv₀
        fun s hs ↦ sub_ne_zero.2 ?_
    rcases lt_or_gt_of_ne (ne_of_mem_erase hj).symm with hij | hji
    · exact (sub_pos.1 (hδ.trans_le (hgap s.toNNReal (hs_mem hs) hij))).ne'
    · exact (sub_pos.1 (hδ.trans_le (hgap s.toNNReal (hs_mem hs) hji))).ne
  refine ⟨hsum_cont.intervalIntegrable_of_Icc (NNReal.coe_nonneg t), ?_⟩
  rw [heq t ⟨zero_le, le_rfl⟩, dysonTruncPath_apply]
  congr 1
  refine _root_.intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
  rw [← heq s.toNNReal (hs_mem hs), dysonDriftTrunc_eq_dysonDrift (hgap s.toNNReal (hs_mem hs))]

/-- **Pasting truncated trajectories into a global `IsDysonPath`.** If for every finite horizon
`T : ℝ≥0` there exists `δ > 0` such that `dysonTruncPath n hδ x hw` remains in the `δ`-chamber on
`[0, T]`, then the truncated trajectories paste into a global `IsDysonPath n x w γ` agreeing on
each `[0, T]` with every non-exiting truncation. -/
theorem exists_isDysonPath_of_forall_exists_trunc_mem_chamber {n : ℕ} {x : Fin n → ℝ}
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hch : ∀ T : ℝ≥0, ∃ (δ : ℝ) (hδ : 0 < δ),
      ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
        δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) :
    ∃ γ : ℝ≥0 → Fin n → ℝ, IsDysonPath n x w γ ∧
      ∀ (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ),
        (∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
          δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) →
        ∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t := by
  let δT : ℝ≥0 → ℝ := fun T ↦ (hch T).choose
  have hδT : ∀ T : ℝ≥0, 0 < δT T := fun T ↦ (hch T).choose_spec.1
  have hchT : ∀ T : ℝ≥0, ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
      δT T ≤ dysonTruncPath n (hδT T) x hw t i - dysonTruncPath n (hδT T) x hw t j :=
    fun T ↦ (hch T).choose_spec.2
  let γ : ℝ≥0 → Fin n → ℝ := fun t ↦ dysonTruncPath n (hδT t) x hw t
  have hcompat : ∀ (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ),
      (∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
        δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) →
      ∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t := by
    intro T δ hδ hδ_ch t ht
    have hm : 0 < min δ (δT t) := lt_min hδ (hδT t)
    have heq₁ := dysonTruncPath_eq_of_le_of_mem_chamber hm (min_le_right δ (δT t)) hw
      (hchT t) t ⟨zero_le, le_rfl⟩
    have heq₂ := dysonTruncPath_eq_of_le_of_mem_chamber hm (min_le_left δ (δT t)) hw
      hδ_ch t ht
    exact heq₁.symm.trans heq₂
  refine ⟨γ, isDysonPath_of_forall_exists_eq_dysonTruncPath hw fun T ↦
    ⟨δT T, hδT T, hcompat T (hδT T) (hchT T), fun t ht i j hij ↦ ?_⟩, hcompat⟩
  rw [hcompat T (hδT T) (hchT T) t ht]
  exact hchT T t ht hij

/-- **Stochastic localization-to-global bridge for `IsDysonSolution`.** Whenever `B` has
`P`-almost-surely continuous paths and on `P`-almost every sample path each finite horizon `[0, T]`
admits a positive threshold `δ` up to which `dysonTruncPath` stays in the `δ`-chamber, the
truncated trajectories assemble into an `IsDysonSolution β n x P B X`. -/
theorem exists_isDysonSolution_of_ae_trunc_mem_chamber {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω) (B : Fin n → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, ∀ᵐ ω ∂P, Continuous (B i · ω))
    (hch : ∀ᵐ ω ∂P, ∀ (hw : Continuous (fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω)) (T : ℝ≥0),
      ∃ (δ : ℝ) (hδ : 0 < δ), ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
        δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) :
    ∃ X : ℝ≥0 → Ω → Fin n → ℝ, IsDysonSolution β n x P B X := by
  classical
  let w : Ω → ℝ≥0 → Fin n → ℝ := fun ω t i ↦ Real.sqrt (2 / (β * n)) * B i t ω
  let good : Ω → Prop := fun ω ↦ ∃ γ : ℝ≥0 → Fin n → ℝ, IsDysonPath n x (w ω) γ
  let X : ℝ≥0 → Ω → Fin n → ℝ := fun t ω ↦
    if h : good ω then h.choose t else x
  refine ⟨X, ?_⟩
  rw [isDysonSolution_iff_ae_isDysonPath]
  rw [← ae_all_iff] at hB
  filter_upwards [hB, hch] with ω hωB hωch
  have hw : Continuous (w ω) := continuous_pi fun i ↦ continuous_const.mul (hωB i)
  obtain ⟨γ, hγ, -⟩ := exists_isDysonPath_of_forall_exists_trunc_mem_chamber hw (hωch hw)
  have hg : good ω := ⟨γ, hγ⟩
  have hX : (fun t ↦ X t ω) = hg.choose := by
    ext t i
    simp [X, hg]
  rw [hX]
  exact hg.choose_spec

end TauCeti.Probability
