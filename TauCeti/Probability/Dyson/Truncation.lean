/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Dyson.System
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall
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
`{z | ∀ i < j, δ ≤ z i - z j}`, interior-derivative ODE uniqueness (`ODE.eqOn_Icc_of_hasDerivAt`)
yields:

* **Consistency across thresholds** (`dysonTruncPath_eq_of_le_of_mem_chamber`): for `0 < δ₁ ≤ δ₂`,
  `dysonTruncPath` at threshold `δ₁` agrees with `dysonTruncPath` at threshold `δ₂` on `[0, T]`
  whenever the `δ₂`-trajectory remains in the `δ₂`-chamber on `(0, T)`.
* **Agreement with any Dyson path before exit** (`IsDysonPath.eq_dysonTruncPath_of_mem_chamber`):
  any `IsDysonPath` staying in the `δ`-chamber on `(0, T)` coincides with `dysonTruncPath` on
  `[0, T]`.
* **Pasting into a global solution** (`exists_isDysonPath_of_forall_exists_trunc_mem_chamber` and
  `exists_isDysonSolution_of_ae_trunc_mem_chamber`): once every finite horizon `[0, T]` admits a
  positive gap threshold `δ` up to which `dysonTruncPath` avoids the `δ`-boundary, the truncated
  solutions paste into a global `IsDysonPath` (and almost surely into `IsDysonSolution`).

## Main declarations

* `TauCeti.Probability.dysonTruncPath`: unique global trajectory of the `δ`-truncated Dyson system
  driven by a continuous path `w`.
* `TauCeti.Probability.dysonTruncPath_apply`, `TauCeti.Probability.eqOn_dysonTruncPath`, and
  `TauCeti.Probability.eq_dysonTruncPath`: coordinatewise integral equation and uniqueness.
* `TauCeti.Probability.dist_dysonTruncPath_le` and
  `TauCeti.Probability.eqOn_dysonTruncPath_of_eqOn`: Grönwall continuous dependence in `(x, w)` and
  prefix congruence in `w` on `[0, T]`.
* `TauCeti.Probability.sum_dysonTruncPath`: center-of-mass conservation.
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

/-- **Local uniqueness for the `δ`-truncated Dyson integral equation.** Any trajectory `γ`
continuous on `[0, T]` that satisfies the coordinatewise `δ`-truncated integral equation on
`[0, T]` equals `dysonTruncPath n hδ x hw` on `[0, T]`. -/
theorem eqOn_dysonTruncPath {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x : Fin n → ℝ}
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0} {γ : ℝ≥0 → Fin n → ℝ}
    (hγc : ContinuousOn γ (Icc 0 T))
    (hγ : ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ i : Fin n,
      γ t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDriftTrunc n δ (γ s.toNNReal) i) :
    EqOn γ (dysonTruncPath n hδ x hw) (Icc 0 T) := by
  set g : ℝ → Fin n → ℝ := fun s i ↦ x i + ∫ r in (0 : ℝ)..s, dysonDriftTrunc n δ (γ r.toNNReal) i
  have hmap : MapsTo Real.toNNReal (Icc 0 (T : ℝ)) (Icc (0 : ℝ≥0) T) :=
    fun _ hs ↦ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
  have hdr : ContinuousOn (fun r : ℝ ↦ dysonDriftTrunc n δ (γ r.toNNReal)) (Icc 0 (T : ℝ)) :=
    (continuous_dysonDriftTrunc n hδ).comp_continuousOn
      (hγc.comp continuous_real_toNNReal.continuousOn hmap)
  have hgc : ∀ s ∈ Icc (0 : ℝ) T, g s + w s.toNNReal = γ s.toNNReal := fun s hs ↦ by
    ext i
    have heq := hγ s.toNNReal (hmap hs) i
    rw [Real.coe_toNNReal s hs.1] at heq
    simp only [g, Pi.add_apply, heq]
    ring
  have hg_cont : ContinuousOn g (Icc 0 (T : ℝ)) := by
    refine ((hγc.comp continuous_real_toNNReal.continuousOn hmap).sub
      (hw.comp continuous_real_toNNReal).continuousOn).congr fun s hs ↦ ?_
    simp only [Pi.sub_apply, Function.comp_apply, ← hgc s hs, add_sub_cancel_right]
  have hg_eq : EqOn g (dysonTruncSmooth n hδ x hw) (Icc 0 (T : ℝ)) := by
    refine ODE.eqOn_Icc_of_hasDerivAt (a := 0) (b := T) (c := 0)
      (fun s _ ↦ lipschitzWith_dysonTruncField n hδ w s) ⟨le_rfl, NNReal.coe_nonneg T⟩
      hg_cont (fun s hs ↦ ?_) (continuous_dysonTruncSmooth n hδ x hw).continuousOn
      (fun s _ ↦ hasDerivAt_dysonTruncSmooth n hδ x hw s)
      (by ext i; simp [g, dysonTruncSmooth_zero])
    rw [dysonTruncField, hgc s (Ioo_subset_Icc_self hs)]
    refine hasDerivAt_pi.2 fun i ↦ ?_
    have hfi : ContinuousOn (fun r : ℝ ↦ dysonDriftTrunc n δ (γ r.toNNReal) i) (Icc 0 (T : ℝ)) :=
      (continuous_apply i).comp_continuousOn hdr
    have hint : IntervalIntegrable (fun r : ℝ ↦ dysonDriftTrunc n δ (γ r.toNNReal) i) volume 0 s :=
      (hfi.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1.le
    have hca : ∀ v ∈ Ioo (0 : ℝ) T,
        ContinuousAt (fun r : ℝ ↦ dysonDriftTrunc n δ (γ r.toNNReal) i) v :=
      fun _ hv ↦ hfi.continuousAt (Icc_mem_nhds hv.1 hv.2)
    exact (_root_.intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hca s hs) (hca s hs)).const_add (x i)
  intro t ht
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.2 ht.2⟩
  have hgt := hgc t ht'
  simp only [Real.toNNReal_coe] at hgt
  rw [← hgt, hg_eq ht', dysonTruncPath]

/-- **Global uniqueness for the `δ`-truncated Dyson integral equation.** Any continuous trajectory
`γ : ℝ≥0 → Fin n → ℝ` satisfying the coordinatewise `δ`-truncated integral equation equals
`dysonTruncPath n hδ x hw`. -/
theorem eq_dysonTruncPath {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x : Fin n → ℝ}
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {γ : ℝ≥0 → Fin n → ℝ} (hγc : Continuous γ)
    (hγ : ∀ (t : ℝ≥0) (i : Fin n),
      γ t i = x i + w t i + ∫ s in (0 : ℝ)..t, dysonDriftTrunc n δ (γ s.toNNReal) i) :
    γ = dysonTruncPath n hδ x hw := by
  ext t i
  exact congr_fun (eqOn_dysonTruncPath hδ hw hγc.continuousOn
    (fun s _ ↦ hγ s) ⟨zero_le, le_rfl⟩) i

/-- **Continuous dependence of `dysonTruncPath` on initial configuration and driving path.** If
`dist (w₁ s) (w₂ s) ≤ ε` on `[0, T]`, then for all `t ∈ [0, T]`,
`dist (dysonTruncPath n hδ x₁ hw₁ t) (dysonTruncPath n hδ x₂ hw₂ t) ≤
  (dist x₁ x₂ + ε) * exp ((2 / δ²) * t)`. -/
theorem dist_dysonTruncPath_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {x₁ x₂ : Fin n → ℝ}
    {w₁ w₂ : ℝ≥0 → Fin n → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {T : ℝ≥0} {ε : ℝ}
    (hw : ∀ s ∈ Icc (0 : ℝ≥0) T, dist (w₁ s) (w₂ s) ≤ ε) {t : ℝ≥0} (ht : t ∈ Icc (0 : ℝ≥0) T) :
    dist (dysonTruncPath n hδ x₁ hw₁ t) (dysonTruncPath n hδ x₂ hw₂ t) ≤
      (dist x₁ x₂ + ε) * Real.exp ((2 / δ ^ 2) * t) := by
  set K : ℝ≥0 := 2 / Real.toNNReal δ ^ 2
  have hK_coe : (K : ℝ) = 2 / δ ^ 2 := by
    simp [K, Real.coe_toNNReal δ hδ.le]
  have hK_ne : (K : ℝ) ≠ 0 := by
    rw [hK_coe]
    positivity
  set u₁ := dysonTruncSmooth n hδ x₁ hw₁
  set u₂ := dysonTruncSmooth n hδ x₂ hw₂
  have hu_dist : ∀ s ∈ Icc (0 : ℝ) T,
      dist (u₁ s) (u₂ s) ≤ gronwallBound (dist x₁ x₂) K (0 + (K : ℝ) * ε) (s - 0) := by
    refine dist_le_of_approx_trajectories_ODE (v := dysonTruncField n δ w₁) (K := K)
      (f := u₁) (g := u₂)
      (f' := fun s ↦ dysonTruncField n δ w₁ s (u₁ s))
      (g' := fun s ↦ dysonTruncField n δ w₂ s (u₂ s))
      (lipschitzWith_dysonTruncField n hδ w₁)
      (continuous_dysonTruncSmooth n hδ x₁ hw₁).continuousOn
      (fun s _ ↦ (hasDerivAt_dysonTruncSmooth n hδ x₁ hw₁ s).hasDerivWithinAt)
      (fun _ _ ↦ by simp)
      (continuous_dysonTruncSmooth n hδ x₂ hw₂).continuousOn
      (fun s _ ↦ (hasDerivAt_dysonTruncSmooth n hδ x₂ hw₂ s).hasDerivWithinAt)
      (fun s hs ↦ ?_) (by simp [u₁, u₂, dysonTruncSmooth_zero])
    have hs_nn : s.toNNReal ∈ Icc (0 : ℝ≥0) T :=
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2.le⟩
    calc dist (dysonTruncField n δ w₂ s (u₂ s)) (dysonTruncField n δ w₁ s (u₂ s))
        ≤ (K : ℝ) * dist (u₂ s + w₂ s.toNNReal) (u₂ s + w₁ s.toNNReal) :=
          (lipschitzWith_dysonDriftTrunc n hδ).dist_le_mul _ _
      _ = (K : ℝ) * dist (w₁ s.toNNReal) (w₂ s.toNNReal) := by
          rw [dist_add_left, dist_comm]
      _ ≤ (K : ℝ) * ε := mul_le_mul_of_nonneg_left (hw s.toNNReal hs_nn) K.2
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.2 ht.2⟩
  have hu_t := hu_dist t ht'
  rw [gronwallBound_of_K_ne_0 hK_ne, zero_add, sub_zero, mul_div_cancel_left₀ ε hK_ne,
    hK_coe] at hu_t
  calc dist (dysonTruncPath n hδ x₁ hw₁ t) (dysonTruncPath n hδ x₂ hw₂ t)
      ≤ dist (u₁ t) (u₂ t) + dist (w₁ t) (w₂ t) := dist_add_add_le _ _ _ _
    _ ≤ (dist x₁ x₂ * Real.exp ((2 / δ ^ 2) * t) + ε * (Real.exp ((2 / δ ^ 2) * t) - 1)) + ε :=
        add_le_add hu_t (hw t ht)
    _ = (dist x₁ x₂ + ε) * Real.exp ((2 / δ ^ 2) * t) := by ring

/-- **Prefix congruence in the driving path.** Two continuous driving paths `w₁` and `w₂` that
agree on `[0, T]` produce the same `dysonTruncPath` throughout `[0, T]`. -/
theorem eqOn_dysonTruncPath_of_eqOn {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (x : Fin n → ℝ)
    {w₁ w₂ : ℝ≥0 → Fin n → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {T : ℝ≥0}
    (hw : EqOn w₁ w₂ (Icc 0 T)) :
    EqOn (dysonTruncPath n hδ x hw₁) (dysonTruncPath n hδ x hw₂) (Icc 0 T) := fun t ht ↦ by
  refine dist_le_zero.1 ?_
  simpa using dist_dysonTruncPath_le hδ hw₁ hw₂
    (x₁ := x) (x₂ := x) (ε := 0) (fun s hs ↦ by simp [hw hs]) ht

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
threshold `δ₂` stays inside `{z | ∀ i < j, δ₂ ≤ z i - z j}` on `(0, T)`, then `dysonTruncPath` at
threshold `δ₁` agrees with it throughout `[0, T]`. -/
theorem dysonTruncPath_eq_of_le_of_mem_chamber {n : ℕ} {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hle : δ₁ ≤ δ₂) {x : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hch : ∀ t ∈ Ioo (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
      δ₂ ≤ dysonTruncPath n (hδ₁.trans_le hle) x hw t i -
        dysonTruncPath n (hδ₁.trans_le hle) x hw t j) :
    ∀ t ∈ Icc (0 : ℝ≥0) T,
      dysonTruncPath n hδ₁ x hw t = dysonTruncPath n (hδ₁.trans_le hle) x hw t := by
  set hδ₂ : 0 < δ₂ := hδ₁.trans_le hle
  have hu : EqOn (dysonTruncSmooth n hδ₁ x hw) (dysonTruncSmooth n hδ₂ x hw) (Icc 0 (T : ℝ)) := by
    refine ODE.eqOn_Icc_of_hasDerivAt (a := 0) (b := T) (c := 0)
      (fun s _ ↦ lipschitzWith_dysonTruncField n hδ₁ w s) ⟨le_rfl, NNReal.coe_nonneg T⟩
      (continuous_dysonTruncSmooth n hδ₁ x hw).continuousOn
      (fun s _ ↦ hasDerivAt_dysonTruncSmooth n hδ₁ x hw s)
      (continuous_dysonTruncSmooth n hδ₂ x hw).continuousOn
      (fun s hs ↦ ?_) (by rw [dysonTruncSmooth_zero, dysonTruncSmooth_zero])
    have hs_nn : s.toNNReal ∈ Ioo (0 : ℝ≥0) T :=
      ⟨Real.toNNReal_pos.2 hs.1,
        NNReal.coe_lt_coe.1 (by rw [Real.coe_toNNReal s hs.1.le]; exact hs.2)⟩
    have hst : dysonTruncSmooth n hδ₂ x hw s + w s.toNNReal =
        dysonTruncPath n hδ₂ x hw s.toNNReal := by
      simp [dysonTruncPath, Real.coe_toNNReal s hs.1.le]
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
`{z | ∀ i < j, δ ≤ z i - z j}` on `(0, T)` (`0 < δ`), then `γ` coincides with
`dysonTruncPath n hδ x hw` throughout `[0, T]`. -/
theorem IsDysonPath.eq_dysonTruncPath_of_mem_chamber {n : ℕ} {x : Fin n → ℝ}
    {w γ : ℝ≥0 → Fin n → ℝ} (hγ : IsDysonPath n x w γ) (hw : Continuous w) {δ : ℝ} (hδ : 0 < δ)
    {T : ℝ≥0} (hch : ∀ t ∈ Ioo (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j → δ ≤ γ t i - γ t j) :
    ∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t := by
  set f : ℝ → Fin n → ℝ := fun s ↦ γ s.toNNReal - w s.toNNReal
  have hf_cont : Continuous f := (hγ.continuous.sub hw).comp continuous_real_toNNReal
  have hf_eq : EqOn f (dysonTruncSmooth n hδ x hw) (Icc 0 (T : ℝ)) := by
    refine ODE.eqOn_Icc_of_hasDerivAt (a := 0) (b := T) (c := 0)
      (fun s _ ↦ lipschitzWith_dysonTruncField n hδ w s) ⟨le_rfl, NNReal.coe_nonneg T⟩
      hf_cont.continuousOn (fun s hs ↦ ?_)
      (continuous_dysonTruncSmooth n hδ x hw).continuousOn
      (fun s _ ↦ hasDerivAt_dysonTruncSmooth n hδ x hw s)
      (by simp [f, hγ.eval_zero, dysonTruncSmooth_zero])
    have hs_nn : s.toNNReal ∈ Ioo (0 : ℝ≥0) T :=
      ⟨Real.toNNReal_pos.2 hs.1,
        NNReal.coe_lt_coe.1 (by rw [Real.coe_toNNReal s hs.1.le]; exact hs.2)⟩
    have htr : dysonTruncField n δ w s (f s) = dysonDrift n (γ s.toNNReal) := by
      simp only [dysonTruncField, f, sub_add_cancel]
      exact dysonDriftTrunc_eq_dysonDrift (hch s.toNNReal hs_nn)
    rw [htr]
    exact hasDerivAt_pi.2 fun i ↦ hγ.hasDerivAt_sub_drive i hs.1
  intro t ht
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.2 ht.2⟩
  have hft : γ t - w t = dysonTruncSmooth n hδ x hw t := by simpa [f] using hf_eq ht'
  rw [dysonTruncPath, ← hft, sub_add_cancel]

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
each `[0, T]` with every truncation that stays in its chamber on `(0, T)`. -/
theorem exists_isDysonPath_of_forall_exists_trunc_mem_chamber {n : ℕ} {x : Fin n → ℝ}
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hch : ∀ T : ℝ≥0, ∃ (δ : ℝ) (hδ : 0 < δ),
      ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
        δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) :
    ∃ γ : ℝ≥0 → Fin n → ℝ, IsDysonPath n x w γ ∧
      ∀ (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ),
        (∀ t ∈ Ioo (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
          δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) →
        ∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t := by
  let δT : ℝ≥0 → ℝ := fun T ↦ (hch T).choose
  have hδT : ∀ T : ℝ≥0, 0 < δT T := fun T ↦ (hch T).choose_spec.1
  have hchT : ∀ T : ℝ≥0, ∀ t ∈ Icc (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
      δT T ≤ dysonTruncPath n (hδT T) x hw t i - dysonTruncPath n (hδT T) x hw t j :=
    fun T ↦ (hch T).choose_spec.2
  let γ : ℝ≥0 → Fin n → ℝ := fun t ↦ dysonTruncPath n (hδT t) x hw t
  have hcompat : ∀ (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ),
      (∀ t ∈ Ioo (0 : ℝ≥0) T, ∀ ⦃i j : Fin n⦄, i < j →
        δ ≤ dysonTruncPath n hδ x hw t i - dysonTruncPath n hδ x hw t j) →
      ∀ t ∈ Icc (0 : ℝ≥0) T, γ t = dysonTruncPath n hδ x hw t := by
    intro T δ hδ hδ_ch t ht
    have hm : 0 < min δ (δT t) := lt_min hδ (hδT t)
    have heq₁ := dysonTruncPath_eq_of_le_of_mem_chamber hm (min_le_right δ (δT t)) hw
      (fun s hs ↦ hchT t s (Ioo_subset_Icc_self hs)) t ⟨zero_le, le_rfl⟩
    have heq₂ := dysonTruncPath_eq_of_le_of_mem_chamber hm (min_le_left δ (δT t)) hw
      hδ_ch t ht
    exact heq₁.symm.trans heq₂
  refine ⟨γ, isDysonPath_of_forall_exists_eq_dysonTruncPath hw fun T ↦
    ⟨δT T, hδT T, hcompat T (hδT T) (fun s hs ↦ hchT T s (Ioo_subset_Icc_self hs)),
      fun t ht i j hij ↦ ?_⟩, hcompat⟩
  rw [hcompat T (hδT T) (fun s hs ↦ hchT T s (Ioo_subset_Icc_self hs)) t ht]
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
