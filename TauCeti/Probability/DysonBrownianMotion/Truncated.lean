/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Defs.Filter
public import TauCeti.Probability.DysonBrownianMotion.Pathwise
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Globally Lipschitz truncated Dyson trajectories and pasting to the Dyson system

To construct solutions of the singular Dyson system (AGZ Lemma 4.3.3), one first regularizes the
repulsive drift `(x_i - x_j)⁻¹` (`i < j`) to `(max (x_i - x_j) ε)⁻¹` for `ε > 0`. Subtracting the
continuous additive driving path `w` turns the integral equation
`X t i = x i + w t i + ∫ s in (0 : ℝ)..t, truncatedDysonDrift ε (X s.toNNReal) i`
into a non-autonomous ordinary differential equation `Y' t = truncatedDysonDrift ε (Y t + w t)`
with globally bounded (`≤ ε⁻¹`) and globally Lipschitz (`2 * ε⁻¹ ^ 2`) vector field.

This file applies Mathlib's Picard–Lindelöf theorem to construct the global trajectory
`truncatedDysonPath ε x w : ℝ≥0 → Fin n → ℝ` and establishes the deterministic toolkit needed to
pass from truncated trajectories to `IsPathwiseDysonSolution` and `IsDysonSolution`:

* **Global existence, local uniqueness, and causality:** `truncatedDysonPath ε x w` is continuous
  on `ℝ≥0` and uniquely solves the `ε`-truncated integral equation on every `[0, T]`; in
  particular, its restriction to `[0, T]` depends on `w` only through `Iic T`.
* **Trace conservation and global `ℓ²`-contraction:** `∑ i, truncatedDysonPath ε x w t i =
  ∑ i, x i + ∑ i, w t i`, and `∑ i, (truncatedDysonPath ε x w t i - truncatedDysonPath ε y w t i)²
  ≤ ∑ i, (x i - y i)²` for all configurations `x, y : Fin n → ℝ`.
* **Truncation consistency and short-time separation:** if `truncatedDysonPath ε x w` remains
  `ε`-separated on `[0, T]`, then it coincides on `[0, T]` with `truncatedDysonPath ε' x w` for
  every `0 < ε' ≤ ε`; moreover, from any `StrictAnti x` (with `w 0 = 0`), continuity yields `ε > 0`
  and `T > 0` for which `ε`-separation holds on `[0, T]`.
* **Pasting across diverging collision horizons:** for strictly separated initial configurations
  (the open-chamber step of AGZ Lemma 4.3.3), if every horizon `T : ℝ≥0` admits `ε > 0` for which
  `truncatedDysonPath ε x w` stays `ε`-separated on `[0, T]`, then the sequence
  `m ↦ truncatedDysonPath ((m + 1 : ℝ)⁻¹) x w t` stabilizes at every `t` and its `limUnder` solves
  `IsPathwiseDysonSolution` (and almost surely solves `IsDysonSolution`). Boundary initial data
  `Antitone x` then connect via the `ℓ²`-contraction `IsPathwiseDysonSolution.sum_sq_sub_le`.

## Main definitions

* `TauCeti.Probability.IsTruncatedDysonOn`: local solution predicate on `Iic T` for the
  `ε`-truncated Dyson integral equation.
* `TauCeti.Probability.truncatedDysonPath`: global trajectory of the `ε`-truncated Dyson system.

## Main results

* `TauCeti.Probability.isTruncatedDysonOn_truncatedDysonPath` and
  `TauCeti.Probability.eqOn_truncatedDysonPath_of_isTruncatedDysonOn`: global existence and local
  uniqueness on `[0, T]`.
* `TauCeti.Probability.truncatedDysonPath_congr_Iic`: causality on `[0, T]`.
* `TauCeti.Probability.sum_sq_truncatedDysonPath_sub_le`: global `ℓ²`-contraction in initial data.
* `TauCeti.Probability.truncatedDysonPath_eq_of_le_sub`: consistency across truncation levels
  `0 < ε' ≤ ε` before the `ε`-separation exit.
* `TauCeti.Probability.isPathwiseDysonSolution_limUnder_truncatedDysonPath` and
  `TauCeti.Probability.isDysonSolution_limUnder_truncatedDysonPath`: global pasting into
  `IsPathwiseDysonSolution` and `IsDysonSolution`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Lemma 4.3.3.
-/

public section

noncomputable section

open Finset Filter Function MeasureTheory Metric Set
open scoped NNReal Topology Interval

namespace TauCeti.Probability

section LocalTheory

variable {n : ℕ}

/-- `IsTruncatedDysonOn ε x w X T` states that `X : ℝ≥0 → Fin n → ℝ` is continuous on `Iic T` and
solves the `ε`-truncated Dyson integral equation driven by `w` from `x` on `[0, T]`. -/
structure IsTruncatedDysonOn (ε : ℝ) (x : Fin n → ℝ) (w X : ℝ≥0 → Fin n → ℝ) (T : ℝ≥0) : Prop where
  continuousOn_Iic : ContinuousOn X (Iic T)
  eq_add_integral : ∀ ⦃t : ℝ≥0⦄, t ≤ T → ∀ i : Fin n,
    X t i = x i + w t i + ∫ s in (0 : ℝ)..t, truncatedDysonDrift ε (X s.toNNReal) i

namespace IsTruncatedDysonOn

variable {ε : ℝ} {x y : Fin n → ℝ} {w X Y : ℝ≥0 → Fin n → ℝ} {T T' : ℝ≥0}

/-- Restricting a local truncated Dyson solution from `[0, T]` to a subhorizon `[0, T']`. -/
theorem mono (hX : IsTruncatedDysonOn ε x w X T) (hT : T' ≤ T) :
    IsTruncatedDysonOn ε x w X T' where
  continuousOn_Iic := hX.continuousOn_Iic.mono (Iic_subset_Iic.2 hT)
  eq_add_integral _ ht i := hX.eq_add_integral (ht.trans hT) i

/-- Initial value `X 0 = x + w 0` of a local truncated Dyson solution. -/
theorem apply_zero (hX : IsTruncatedDysonOn ε x w X T) : X 0 = x + w 0 := by
  ext i
  simpa using hX.eq_add_integral (zero_le : (0 : ℝ≥0) ≤ T) i

/-- For `ε > 0`, the truncated drift along a local solution on `Iic T` is interval integrable on
`0..t` for every `t ≤ T`. -/
theorem intervalIntegrable_truncatedDysonDrift (hX : IsTruncatedDysonOn ε x w X T) (hε : 0 < ε)
    {t : ℝ≥0} (ht : t ≤ T) (i : Fin n) :
    IntervalIntegrable (fun s : ℝ ↦ truncatedDysonDrift ε (X s.toNNReal) i) volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le t.coe_nonneg]
  have htoNN : MapsTo Real.toNNReal (Icc 0 (t : ℝ)) (Iic T) := by
    intro s hs
    exact (Real.toNNReal_le_iff_le_coe.2 (hs.2.trans (NNReal.coe_le_coe.2 ht)))
  exact (((continuous_apply i).comp (continuous_truncatedDysonDrift hε)).continuousOn.comp
    (hX.continuousOn_Iic.comp continuous_real_toNNReal.continuousOn htoNN) (mapsTo_univ _ _))

/-- Coordinate sum conservation for a local truncated Dyson solution on `[0, T]`. -/
theorem sum_apply (hX : IsTruncatedDysonOn ε x w X T) (hε : 0 < ε) {t : ℝ≥0} (ht : t ≤ T) :
    ∑ i, X t i = ∑ i, x i + ∑ i, w t i := by
  simp_rw [hX.eq_add_integral ht, sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦
    hX.intervalIntegrable_truncatedDysonDrift hε ht i]
  simp

/-- **`ℓ²`-energy identity for local solutions of the truncated Dyson system.** For two solutions on
`Iic T` driven by the same path `w`, the change in squared Euclidean distance on `[0, t]` (`t ≤ T`)
equals twice the integrated truncated-drift difference pairing. -/
theorem sum_sq_sub_eq (hX : IsTruncatedDysonOn ε x w X T) (hY : IsTruncatedDysonOn ε y w Y T)
    (hε : 0 < ε) {t : ℝ≥0} (ht : t ≤ T) :
    ∑ i, (X t i - Y t i) ^ 2 - ∑ i, (x i - y i) ^ 2 =
      2 * ∫ s in (0 : ℝ)..t,
        ∑ i, (truncatedDysonDrift ε (X s.toNNReal) i - truncatedDysonDrift ε (Y s.toNNReal) i) *
          (X s.toNNReal i - Y s.toNNReal i) := by
  let f : Fin n → ℝ → ℝ := fun i s ↦
    truncatedDysonDrift ε (X s.toNNReal) i - truncatedDysonDrift ε (Y s.toNNReal) i
  let g : Fin n → ℝ → ℝ := fun i u ↦ (x i - y i) + ∫ s in (0 : ℝ)..u, f i s
  have hf_int (i : Fin n) : IntervalIntegrable (f i) volume 0 t :=
    (hX.intervalIntegrable_truncatedDysonDrift hε ht i).sub
      (hY.intervalIntegrable_truncatedDysonDrift hε ht i)
  have hg_val (i : Fin n) {u : ℝ≥0} (hu : u ≤ t) : g i u = X u i - Y u i := by
    simp only [g, f]
    rw [intervalIntegral.integral_sub
      (hX.intervalIntegrable_truncatedDysonDrift hε (hu.trans ht) i)
      (hY.intervalIntegrable_truncatedDysonDrift hε (hu.trans ht) i)]
    linarith [hX.eq_add_integral (hu.trans ht) i, hY.eq_add_integral (hu.trans ht) i]
  have hg_ac (i : Fin n) : AbsolutelyContinuousOnInterval (g i) 0 t :=
    ((LipschitzWith.const (x i - y i)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      ((hf_int i).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hg_deriv (i : Fin n) : ∀ᵐ u, u ∈ uIoc (0 : ℝ) (t : ℝ) → HasDerivAt (g i) (f i u) u := by
    filter_upwards [(hf_int i).ae_hasDerivAt_integral] with u hu hmem
    exact (hu (uIoc_subset_uIcc hmem) 0 left_mem_uIcc).const_add (x i - y i)
  have htoNN : MapsTo Real.toNNReal (uIcc (0 : ℝ) (t : ℝ)) (Iic T) := by
    rw [uIcc_of_le t.coe_nonneg]
    intro s hs
    exact Real.toNNReal_le_iff_le_coe.2 (hs.2.trans (NNReal.coe_le_coe.2 ht))
  have hcont_diff (i : Fin n) :
      ContinuousOn (fun s : ℝ ↦ X s.toNNReal i - Y s.toNNReal i) (uIcc 0 (t : ℝ)) := by
    have hXi : ContinuousOn (fun s : ℝ ↦ X s.toNNReal i) (uIcc 0 (t : ℝ)) :=
      (continuous_apply i).continuousOn.comp
        (hX.continuousOn_Iic.comp continuous_real_toNNReal.continuousOn htoNN) (mapsTo_univ _ _)
    have hYi : ContinuousOn (fun s : ℝ ↦ Y s.toNNReal i) (uIcc 0 (t : ℝ)) :=
      (continuous_apply i).continuousOn.comp
        (hY.continuousOn_Iic.comp continuous_real_toNNReal.continuousOn htoNN) (mapsTo_univ _ _)
    exact hXi.sub hYi
  have hcoord (i : Fin n) :
      (X t i - Y t i) ^ 2 - (x i - y i) ^ 2 =
        2 * ∫ s in (0 : ℝ)..t, f i s * (X s.toNNReal i - Y s.toNNReal i) := by
    have hibp := (hg_ac i).integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt (hg_ac i)
      (hg_deriv i) (hg_deriv i)
    have hcomm : (∫ s in (0 : ℝ)..t, g i s * f i s) = ∫ s in (0 : ℝ)..t, f i s * g i s :=
      intervalIntegral.integral_congr fun s _ ↦ mul_comm _ _
    have hcongr : (∫ s in (0 : ℝ)..t, f i s * g i s) =
        ∫ s in (0 : ℝ)..t, f i s * (X s.toNNReal i - Y s.toNNReal i) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le t.coe_nonneg]
      refine Eventually.of_forall fun s hs ↦ ?_
      have hle : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
      have hgs : g i s = X s.toNNReal i - Y s.toNNReal i := by
        simpa [Real.coe_toNNReal s hs.1.le] using hg_val i hle
      rw [hgs]
    have hg0 : g i 0 = x i - y i := by simp [g]
    rw [← hg_val i le_rfl, ← hg0]
    linarith [hibp, hcomm, hcongr]
  have hint_prod (i : Fin n) :
      IntervalIntegrable (fun s : ℝ ↦ f i s * (X s.toNNReal i - Y s.toNNReal i)) volume 0 t :=
    (hf_int i).mul_continuousOn (hcont_diff i)
  rw [← sum_sub_distrib, sum_congr rfl fun i _ ↦ hcoord i, ← mul_sum,
    ← intervalIntegral.integral_finsetSum fun i _ ↦ hint_prod i]

/-- **`ℓ²`-contraction for local solutions of the truncated Dyson system.** Any two solutions on
`Iic T` with the same driving path `w` satisfy `∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2` for
`t ≤ T`. -/
theorem sum_sq_sub_le (hX : IsTruncatedDysonOn ε x w X T) (hY : IsTruncatedDysonOn ε y w Y T)
    (hε : 0 < ε) {t : ℝ≥0} (ht : t ≤ T) :
    ∑ i, (X t i - Y t i) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  have hid := hX.sum_sq_sub_eq hY hε ht
  have htoNN : MapsTo Real.toNNReal (uIcc (0 : ℝ) (t : ℝ)) (Iic T) := by
    rw [uIcc_of_le t.coe_nonneg]
    intro s hs
    exact Real.toNNReal_le_iff_le_coe.2 (hs.2.trans (NNReal.coe_le_coe.2 ht))
  have hint_prod (i : Fin n) :
      IntervalIntegrable
        (fun s : ℝ ↦
          (truncatedDysonDrift ε (X s.toNNReal) i - truncatedDysonDrift ε (Y s.toNNReal) i) *
            (X s.toNNReal i - Y s.toNNReal i)) volume 0 t := by
    refine ((hX.intervalIntegrable_truncatedDysonDrift hε ht i).sub
      (hY.intervalIntegrable_truncatedDysonDrift hε ht i)).mul_continuousOn ?_
    exact ((continuous_apply i).continuousOn.comp
      (hX.continuousOn_Iic.comp continuous_real_toNNReal.continuousOn htoNN)
      (mapsTo_univ _ _)).sub
      ((continuous_apply i).continuousOn.comp
        (hY.continuousOn_Iic.comp continuous_real_toNNReal.continuousOn htoNN) (mapsTo_univ _ _))
  have hint_sum : IntervalIntegrable
      (fun s : ℝ ↦ ∑ i,
        (truncatedDysonDrift ε (X s.toNNReal) i - truncatedDysonDrift ε (Y s.toNNReal) i) *
          (X s.toNNReal i - Y s.toNNReal i)) volume 0 t :=
    (IntervalIntegrable.sum univ fun i _ ↦ hint_prod i).congr fun u _ ↦ Finset.sum_apply u univ _
  have hint_nonpos :
      ∫ s in (0 : ℝ)..t, ∑ i,
        (truncatedDysonDrift ε (X s.toNNReal) i - truncatedDysonDrift ε (Y s.toNNReal) i) *
          (X s.toNNReal i - Y s.toNNReal i) ≤ 0 := by
    calc
      ∫ s in (0 : ℝ)..t, ∑ i,
          (truncatedDysonDrift ε (X s.toNNReal) i - truncatedDysonDrift ε (Y s.toNNReal) i) *
            (X s.toNNReal i - Y s.toNNReal i)
        ≤ ∫ _s in (0 : ℝ)..t, (0 : ℝ) :=
          intervalIntegral.integral_mono_on_of_le_Ioo t.coe_nonneg
            hint_sum intervalIntegrable_const
            fun s _ ↦ sum_sub_mul_truncatedDysonDrift_sub_nonpos hε (X s.toNNReal) (Y s.toNNReal)
      _ = 0 := intervalIntegral.integral_zero
  linarith

/-- Local uniqueness on `Iic T` for the `ε`-truncated Dyson integral equation. -/
theorem eqOn_Iic (hX : IsTruncatedDysonOn ε x w X T) (hY : IsTruncatedDysonOn ε x w Y T)
    (hε : 0 < ε) :
    EqOn X Y (Iic T) := by
  intro t ht
  ext i
  have hle : ∑ j, (X t j - Y t j) ^ 2 ≤ 0 := by
    simpa using hX.sum_sq_sub_le hY hε ht
  have hsingle : (X t i - Y t i) ^ 2 ≤ ∑ j, (X t j - Y t j) ^ 2 :=
    single_le_sum (f := fun j ↦ (X t j - Y t j) ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i)
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 (le_antisymm (hsingle.trans hle) (sq_nonneg _)))

end IsTruncatedDysonOn

/-- **Existence of `IsTruncatedDysonOn` on arbitrary horizons `[0, T]`.** For every `ε > 0`, initial
configuration `x : Fin n → ℝ`, continuous driving path `w`, and horizon `T : ℝ≥0`, there exists a
continuous trajectory solving the `ε`-truncated Dyson integral equation on `[0, T]`. -/
theorem exists_isTruncatedDysonOn {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (T : ℝ≥0) :
    ∃ X : ℝ≥0 → Fin n → ℝ, IsTruncatedDysonOn ε x w X T := by
  -- 1. Solve the shifted ODE `α' = F_ε(α + w)` on `[0, T]` via Picard–Lindelöf (`a = L * T`).
  let εnn : ℝ≥0 := ⟨ε, hε.le⟩
  have hεnn : 0 < εnn := hε
  have hε_coe : (εnn : ℝ) = ε := rfl
  let L : ℝ≥0 := εnn⁻¹
  let K : ℝ≥0 := 2 * εnn⁻¹ ^ 2
  let a : ℝ≥0 := L * T
  let t₀ : Icc (0 : ℝ) (T : ℝ) := ⟨0, ⟨le_rfl, T.coe_nonneg⟩⟩
  let v : ℝ → (Fin n → ℝ) → (Fin n → ℝ) := fun s z ↦ truncatedDysonDrift ε (z + w s.toNNReal)
  have hpl : IsPicardLindelof v t₀ x a 0 L K := by
    refine
      { lipschitzOnWith := fun s _ ↦ ?_
        continuousOn := fun z _ ↦ ?_
        norm_le := fun s _ z _ ↦ ?_
        mul_max_le := ?_ }
    · have hadd : LipschitzWith 1 (fun z : Fin n → ℝ ↦ z + w s.toNNReal) :=
        (Isometry.of_dist_eq fun z₁ z₂ ↦ dist_add_right z₁ z₂ (w s.toNNReal)).lipschitzWith
      have hlip : LipschitzWith K (v s) := by
        have hcomp := (lipschitzWith_truncatedDysonDrift (n := n) hεnn).comp hadd
        rw [hε_coe] at hcomp
        simpa only [mul_one, K, v, Function.comp_def] using hcomp
      exact (lipschitzOnWith_univ.2 hlip).mono (subset_univ _)
    · exact ((continuous_truncatedDysonDrift hε).comp
        (continuous_const.add (hw.comp continuous_real_toNNReal))).continuousOn
    · exact norm_truncatedDysonDrift_le hε (z + w s.toNNReal)
    · simp only [t₀, sub_zero, max_eq_left T.coe_nonneg, NNReal.coe_zero, a, NNReal.coe_mul, le_rfl]
  obtain ⟨α, hα0, hα_deriv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα_cont : ContinuousOn α (Icc 0 (T : ℝ)) := HasDerivWithinAt.continuousOn hα_deriv
  -- 2. Add back `w` and pass from the vector-valued Picard fixed-point equation to coordinates.
  have hv_cont : Continuous (uncurry v) :=
    (continuous_truncatedDysonDrift hε).comp
      (continuous_snd.add (hw.comp (continuous_real_toNNReal.comp continuous_fst)))
  refine ⟨fun t ↦ α t + w t, ?_, ?_⟩
  · refine (hα_cont.comp NNReal.continuous_coe.continuousOn ?_).add hw.continuousOn
    intro t ht
    exact ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  · intro t ht i
    have hsub : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc 0 (T : ℝ) := by
      rw [uIcc_of_le t.coe_nonneg]
      exact Icc_subset_Icc le_rfl (NNReal.coe_le_coe.2 ht)
    have hpic := ODE.picard_eq_of_hasDerivAt (f := v) (t₀ := 0) (t := (t : ℝ)) (u := univ)
      hv_cont.continuousOn (fun s hs ↦ (hα_deriv s (hsub hs)).mono hsub) (mapsTo_univ _ _)
    simp only [t₀] at hα0
    rw [ODE.picard_apply, hα0] at hpic
    have hval : α t i = x i + (∫ s in (0 : ℝ)..t, v s (α s)) i := by
      simpa only [Pi.add_apply] using congrFun hpic.symm i
    have hint_v : IntervalIntegrable (fun s : ℝ ↦ v s (α s)) volume 0 t :=
      (ODE.continuousOn_comp hv_cont.continuousOn (hα_cont.mono hsub)
        (mapsTo_univ _ _)).intervalIntegrable
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ)
      i).intervalIntegral_comp_comm hint_v
    simp only [ContinuousLinearMap.proj_apply] at hproj
    have hcongr : (∫ s in (0 : ℝ)..t, v s (α s) i) =
        ∫ s in (0 : ℝ)..t, truncatedDysonDrift ε (α s.toNNReal + w s.toNNReal) i := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le t.coe_nonneg]
      exact Eventually.of_forall fun s hs ↦ by simp [v, Real.coe_toNNReal s hs.1.le]
    rw [Pi.add_apply, hval, ← hproj, hcongr]
    ring

end LocalTheory

section GlobalPath

variable {n : ℕ}

/-- The global trajectory `truncatedDysonPath ε x w : ℝ≥0 → Fin n → ℝ` of the `ε`-truncated Dyson
system started at `x` and driven by `w`. Outside the well-posed regime `0 < ε ∧ Continuous w`, it
defaults to `fun t ↦ x + w t`. -/
def truncatedDysonPath (ε : ℝ) (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) : Fin n → ℝ :=
  open Classical in
  if h : 0 < ε ∧ Continuous w then
    Classical.choose (exists_isTruncatedDysonOn h.1 x h.2 (t + 1)) t
  else
    x + w t

/-- On every compact horizon `Iic T`, `truncatedDysonPath ε x w` is a local solution of the
`ε`-truncated Dyson integral equation. -/
theorem isTruncatedDysonOn_truncatedDysonPath {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (T : ℝ≥0) :
    IsTruncatedDysonOn ε x w (truncatedDysonPath ε x w) T := by
  let X_T := Classical.choose (exists_isTruncatedDysonOn hε x hw (T + 1))
  have hX_T : IsTruncatedDysonOn ε x w X_T (T + 1) :=
    Classical.choose_spec (exists_isTruncatedDysonOn hε x hw (T + 1))
  have heq : EqOn (truncatedDysonPath ε x w) X_T (Iic T) := by
    intro t ht
    have hcond : 0 < ε ∧ Continuous w := ⟨hε, hw⟩
    simp only [truncatedDysonPath, dite_eq_left hcond]
    let X_t := Classical.choose (exists_isTruncatedDysonOn hε x hw (t + 1))
    have hX_t : IsTruncatedDysonOn ε x w X_t (t + 1) :=
      Classical.choose_spec (exists_isTruncatedDysonOn hε x hw (t + 1))
    have ht1 : t + 1 ≤ T + 1 := add_le_add_left ht 1
    exact hX_t.eqOn_Iic (hX_T.mono ht1) hε (le_self_add : t ≤ t + 1)
  refine ⟨(hX_T.mono (le_self_add : T ≤ T + 1)).continuousOn_Iic.congr heq, ?_⟩
  intro t ht i
  rw [heq ht, hX_T.eq_add_integral (ht.trans le_self_add) i]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le t.coe_nonneg]
  refine Eventually.of_forall fun s hs ↦ ?_
  have hs_le : s.toNNReal ≤ T :=
    (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
  rw [heq hs_le]

/-- For `ε > 0` and continuous `w`, `truncatedDysonPath ε x w` is continuous on `ℝ≥0`. -/
theorem continuous_truncatedDysonPath {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) :
    Continuous (truncatedDysonPath ε x w) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (isTruncatedDysonOn_truncatedDysonPath hε x hw (t + 1)).continuousOn_Iic.continuousAt
    (Iic_mem_nhds (lt_add_of_pos_right t zero_lt_one))

/-- For `ε > 0` and continuous `w`, `truncatedDysonPath ε x w` satisfies the global `ε`-truncated
Dyson integral equation at every `t : ℝ≥0`. -/
theorem truncatedDysonPath_eq_add_integral {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (t : ℝ≥0) (i : Fin n) :
    truncatedDysonPath ε x w t i =
      x i + w t i +
        ∫ s in (0 : ℝ)..t, truncatedDysonDrift ε (truncatedDysonPath ε x w s.toNNReal) i :=
  (isTruncatedDysonOn_truncatedDysonPath hε x hw t).eq_add_integral le_rfl i

/-- Initial value of `truncatedDysonPath ε x w` at `t = 0`, valid unconditionally. -/
@[simp]
theorem truncatedDysonPath_zero (ε : ℝ) (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) :
    truncatedDysonPath ε x w 0 = x + w 0 := by
  by_cases h : 0 < ε ∧ Continuous w
  · exact (isTruncatedDysonOn_truncatedDysonPath h.1 x h.2 0).apply_zero
  · simp [truncatedDysonPath, h]

/-- For `n ≤ 1`, the truncated drift vanishes identically, so `truncatedDysonPath ε x w` reduces
to `fun t ↦ x + w t` for all `ε` and `w`. -/
@[simp]
theorem truncatedDysonPath_of_subsingleton [Subsingleton (Fin n)] (ε : ℝ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) :
    truncatedDysonPath ε x w = fun t ↦ x + w t := by
  ext t i
  by_cases h : 0 < ε ∧ Continuous w
  · simp [truncatedDysonPath_eq_add_integral h.1 x h.2 t i]
  · simp [truncatedDysonPath, h]

/-- **Center-of-mass conservation** for `truncatedDysonPath`, valid unconditionally for all `ε`,
`x`, and `w`. -/
theorem sum_truncatedDysonPath (ε : ℝ) (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) (t : ℝ≥0) :
    ∑ i, truncatedDysonPath ε x w t i = ∑ i, x i + ∑ i, w t i := by
  by_cases h : 0 < ε ∧ Continuous w
  · exact (isTruncatedDysonOn_truncatedDysonPath h.1 x h.2 t).sum_apply h.1 le_rfl
  · simp [truncatedDysonPath, h, sum_add_distrib]

/-- Any local solution of `IsTruncatedDysonOn ε x w X T` coincides with `truncatedDysonPath ε x w`
on `Iic T`. -/
theorem eqOn_truncatedDysonPath_of_isTruncatedDysonOn {ε : ℝ} (hε : 0 < ε) {x : Fin n → ℝ}
    {w X : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hX : IsTruncatedDysonOn ε x w X T) :
    EqOn X (truncatedDysonPath ε x w) (Iic T) :=
  hX.eqOn_Iic (isTruncatedDysonOn_truncatedDysonPath hε x hw T) hε

/-- **Causality on `[0, T]`.** If two continuous driving paths `w₁` and `w₂` agree on `Iic T`, then
`truncatedDysonPath ε x w₁` and `truncatedDysonPath ε x w₂` agree on `Iic T`. -/
theorem truncatedDysonPath_congr_Iic {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ)
    {w₁ w₂ : ℝ≥0 → Fin n → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {T : ℝ≥0}
    (hw : EqOn w₁ w₂ (Iic T)) :
    EqOn (truncatedDysonPath ε x w₁) (truncatedDysonPath ε x w₂) (Iic T) := by
  have hloc : IsTruncatedDysonOn ε x w₂ (truncatedDysonPath ε x w₁) T := by
    have h₁ := isTruncatedDysonOn_truncatedDysonPath hε x hw₁ T
    refine ⟨h₁.continuousOn_Iic, fun t ht i ↦ ?_⟩
    rw [← hw ht]
    exact h₁.eq_add_integral ht i
  exact eqOn_truncatedDysonPath_of_isTruncatedDysonOn hε hw₂ hloc

/-- **Global `ℓ²`-contraction in initial data** for `truncatedDysonPath`. -/
theorem sum_sq_truncatedDysonPath_sub_le (ε : ℝ) (x y : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ)
    (t : ℝ≥0) :
    ∑ i, (truncatedDysonPath ε x w t i - truncatedDysonPath ε y w t i) ^ 2 ≤
      ∑ i, (x i - y i) ^ 2 := by
  by_cases h : 0 < ε ∧ Continuous w
  · exact (isTruncatedDysonOn_truncatedDysonPath h.1 x h.2 t).sum_sq_sub_le
      (isTruncatedDysonOn_truncatedDysonPath h.1 y h.2 t) h.1 le_rfl
  · refine le_of_eq (sum_congr rfl fun i _ ↦ ?_)
    simp only [truncatedDysonPath, dite_eq_right h, Pi.add_apply]
    ring

/-- **Truncation consistency across thresholds `0 < ε' ≤ ε`.** While `truncatedDysonPath ε x w`
remains `ε`-separated on `[0, T]`, lowering the truncation threshold from `ε` to any `ε' ∈ (0, ε]`
does not change the trajectory on `[0, T]`. -/
theorem truncatedDysonPath_eq_of_le_sub {ε ε' : ℝ} (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    {x : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hsep : ∀ ⦃t : ℝ≥0⦄, t ≤ T → ∀ ⦃i j : Fin n⦄, i < j →
      ε ≤ truncatedDysonPath ε x w t i - truncatedDysonPath ε x w t j) :
    EqOn (truncatedDysonPath ε' x w) (truncatedDysonPath ε x w) (Iic T) := by
  have hε : 0 < ε := hε'.trans_le hε'ε
  have hloc : IsTruncatedDysonOn ε' x w (truncatedDysonPath ε x w) T := by
    have h₁ := isTruncatedDysonOn_truncatedDysonPath hε x hw T
    refine ⟨h₁.continuousOn_Iic, fun t ht i ↦ ?_⟩
    rw [h₁.eq_add_integral ht i]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le t.coe_nonneg]
    refine Eventually.of_forall fun s hs ↦ ?_
    have hs_le : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
    rw [truncatedDysonDrift_eq_dysonDrift (fun a b hab ↦ hsep hs_le hab),
      truncatedDysonDrift_eq_dysonDrift (fun a b hab ↦ hε'ε.trans (hsep hs_le hab))]
  exact (eqOn_truncatedDysonPath_of_isTruncatedDysonOn hε' hw hloc).symm

/-- **Unconditional short-time separation from the open chamber.** From any `StrictAnti x` and
continuous `w` with `w 0 = 0`, there exist `ε > 0` and `T > 0` such that `truncatedDysonPath ε x w`
remains `ε`-separated on `[0, T]`. -/
theorem exists_pos_forall_le_sub_truncatedDysonPath {x : Fin n → ℝ} (hx : StrictAnti x)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    ∃ ε > 0, ∃ T : ℝ≥0, 0 < T ∧
      ∀ ⦃t : ℝ≥0⦄, t ≤ T → ∀ ⦃i j : Fin n⦄, i < j →
        ε ≤ truncatedDysonPath ε x w t i - truncatedDysonPath ε x w t j := by
  let S : Finset (Fin n × Fin n) := {p ∈ (univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n)) |
    p.1 < p.2}
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, fun _ _ i j hij ↦ ?_⟩
    have hmem : (i, j) ∈ S := by simp [S, hij]
    rw [hS] at hmem
    exact False.elim (notMem_empty _ hmem)
  · set δ : ℝ := S.inf' hS (fun p ↦ x p.1 - x p.2)
    have hδ : 0 < δ := by
      rw [lt_inf'_iff]
      intro p hp
      have hlt : p.1 < p.2 := by simpa [S] using hp
      exact sub_pos.2 (hx hlt)
    let ε : ℝ := 2⁻¹ * δ
    have hε : 0 < ε := by positivity
    let U : Set ℝ≥0 :=
      ⋂ p ∈ S, {t : ℝ≥0 | ε < truncatedDysonPath ε x w t p.1 - truncatedDysonPath ε x w t p.2}
    have hU_open : IsOpen U := by
      refine isOpen_biInter_finset fun p _ ↦ isOpen_lt continuous_const ?_
      exact ((continuous_apply p.1).comp (continuous_truncatedDysonPath hε x hw)).sub
        ((continuous_apply p.2).comp (continuous_truncatedDysonPath hε x hw))
    have h0_mem : (0 : ℝ≥0) ∈ U := by
      simp only [U, mem_iInter, mem_ofPred_eq, truncatedDysonPath_zero, hw0, add_zero]
      intro p hp
      have hle : δ ≤ x p.1 - x p.2 := inf'_le _ hp
      dsimp only [ε]
      linarith
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU_open 0 h0_mem
    let T : ℝ≥0 := ⟨r / 2, by positivity⟩
    have hT_pos : 0 < T := NNReal.coe_pos.1 (div_pos hr zero_lt_two)
    refine ⟨ε, hε, T, hT_pos, fun t ht i j hij ↦ ?_⟩
    have ht_ball : t ∈ ball (0 : ℝ≥0) r := by
      rw [mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
      have hle : (t : ℝ) ≤ r / 2 := NNReal.coe_le_coe.2 ht
      linarith
    have htU := hball ht_ball
    simp only [U, mem_iInter, mem_ofPred_eq] at htU
    have hmem : (i, j) ∈ S := by simp [S, hij]
    exact (htU (i, j) hmem).le

/-- **Finite-stage stabilization of the `(m + 1)⁻¹`-truncated Dyson path.** If `w` is continuous
and `truncatedDysonPath ε x w` remains `ε`-separated on `[0, T]` for some `ε > 0`, then the
pointwise `limUnder` of `m ↦ truncatedDysonPath ((m + 1 : ℝ)⁻¹) x w t` agrees with
`truncatedDysonPath ε x w` throughout `Iic T`. -/
theorem eqOn_limUnder_truncatedDysonPath {ε : ℝ} (hε : 0 < ε) {x : Fin n → ℝ}
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hT : ∀ ⦃t : ℝ≥0⦄, t ≤ T → ∀ ⦃i j : Fin n⦄, i < j →
      ε ≤ truncatedDysonPath ε x w t i - truncatedDysonPath ε x w t j) :
    EqOn (fun t ↦ limUnder atTop fun m : ℕ ↦ truncatedDysonPath (((m : ℝ) + 1)⁻¹) x w t)
      (truncatedDysonPath ε x w) (Iic T) := by
  intro t ht
  obtain ⟨M, hM⟩ := exists_nat_gt ε⁻¹
  have hev : (fun _ : ℕ ↦ truncatedDysonPath ε x w t) =ᶠ[atTop]
      fun m : ℕ ↦ truncatedDysonPath (((m : ℝ) + 1)⁻¹) x w t := by
    filter_upwards [eventually_ge_atTop M] with m hm
    have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hinv_pos : 0 < ((m : ℝ) + 1)⁻¹ := inv_pos.2 hm_pos
    have hinv_le : ((m : ℝ) + 1)⁻¹ ≤ ε := by
      rw [inv_le_comm₀ hm_pos hε]
      have hM' : ε⁻¹ < (m : ℝ) := hM.trans_le (by exact_mod_cast hm)
      linarith
    exact (truncatedDysonPath_eq_of_le_sub hinv_pos hinv_le hw hT ht).symm
  exact (tendsto_const_nhds.congr' hev).limUnder_eq

/-- **Global deterministic pasting of truncated Dyson paths (AGZ Lemma 4.3.3).** If `w` is
continuous and every horizon `T : ℝ≥0` admits `ε > 0` for which `truncatedDysonPath ε x w` stays
`ε`-separated on `[0, T]`, then `m ↦ truncatedDysonPath ((m + 1 : ℝ)⁻¹) x w t` stabilizes at every
`t` and its pointwise `limUnder` solves `IsPathwiseDysonSolution x w`. -/
theorem isPathwiseDysonSolution_limUnder_truncatedDysonPath {x : Fin n → ℝ}
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hsep : ∀ T : ℝ≥0, ∃ ε > 0, ∀ ⦃t : ℝ≥0⦄, t ≤ T → ∀ ⦃i j : Fin n⦄, i < j →
      ε ≤ truncatedDysonPath ε x w t i - truncatedDysonPath ε x w t j) :
    IsPathwiseDysonSolution x w
      (fun t ↦ limUnder atTop fun m : ℕ ↦ truncatedDysonPath (((m : ℝ) + 1)⁻¹) x w t) := by
  set X : ℝ≥0 → Fin n → ℝ :=
    fun t ↦ limUnder atTop fun m : ℕ ↦ truncatedDysonPath (((m : ℝ) + 1)⁻¹) x w t
  refine
    { continuous_path := ?_
      strictAnti := ?_
      intervalIntegrable_sum_inv_sub := ?_
      eq_add_integral := ?_ }
  · rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨ε, hε, hT⟩ := hsep (t₀ + 1)
    have hEq : EqOn X (truncatedDysonPath ε x w) (Iic (t₀ + 1)) :=
      eqOn_limUnder_truncatedDysonPath hε hw hT
    have hcont : ContinuousOn X (Iic (t₀ + 1)) :=
      (continuous_truncatedDysonPath hε x hw).continuousOn.congr hEq
    exact hcont.continuousAt (Iic_mem_nhds (lt_add_of_pos_right t₀ zero_lt_one))
  · intro t _ i j hij
    obtain ⟨ε, hε, hT⟩ := hsep t
    have hEq : X t = truncatedDysonPath ε x w t :=
      eqOn_limUnder_truncatedDysonPath hε hw hT le_rfl
    have hle := hT le_rfl hij
    rw [← hEq] at hle
    linarith
  · intro t i
    obtain ⟨ε, hε, hT⟩ := hsep t
    have hEq : EqOn X (truncatedDysonPath ε x w) (Iic t) :=
      eqOn_limUnder_truncatedDysonPath hε hw hT
    have hcont_sum : ContinuousOn
        (fun s : ℝ ↦ ∑ j ∈ univ.erase i,
          (truncatedDysonPath ε x w s.toNNReal i - truncatedDysonPath ε x w s.toNNReal j)⁻¹)
        (uIcc 0 (t : ℝ)) := by
      refine continuousOn_finsetSum _ fun j hj ↦ ?_
      have hdiff : Continuous (fun s : ℝ ↦
          truncatedDysonPath ε x w s.toNNReal i - truncatedDysonPath ε x w s.toNNReal j) :=
        (((continuous_apply i).comp (continuous_truncatedDysonPath hε x hw)).comp
          continuous_real_toNNReal).sub
          (((continuous_apply j).comp (continuous_truncatedDysonPath hε x hw)).comp
            continuous_real_toNNReal)
      refine hdiff.continuousOn.inv₀ fun s hs ↦ sub_ne_zero.2 ?_
      rw [uIcc_of_le t.coe_nonneg] at hs
      have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
      rcases lt_or_gt_of_ne (mem_erase.1 hj).1.symm with hij | hji
      · linarith [hT hs_le hij]
      · linarith [hT hs_le hji]
    refine hcont_sum.intervalIntegrable.congr ?_
    rw [uIoc_of_le t.coe_nonneg]
    intro s hs
    have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    simp only [hEq hs_le]
  · intro t i
    obtain ⟨ε, hε, hT⟩ := hsep t
    have hEq : EqOn X (truncatedDysonPath ε x w) (Iic t) :=
      eqOn_limUnder_truncatedDysonPath hε hw hT
    rw [hEq (le_rfl : t ≤ t), truncatedDysonPath_eq_add_integral hε x hw t i]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le t.coe_nonneg]
    refine Eventually.of_forall fun s hs ↦ ?_
    have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    rw [truncatedDysonDrift_eq_dysonDrift (fun a b hab ↦ hT hs_le hab), hEq hs_le]

/-- **Probabilistic pasting of truncated Dyson paths into `IsDysonSolution`.** If each coordinate
of `B` has almost surely continuous sample paths and almost every sample path admits an
`ε`-separated truncation on every horizon `[0, T]`, then the pointwise `limUnder` of the
`(m + 1)⁻¹`-truncated trajectories satisfies `IsDysonSolution β n x P B`. -/
theorem isDysonSolution_limUnder_truncatedDysonPath {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) {n : ℕ} (x : Fin n → ℝ) (P : Measure Ω) {B : Fin n → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t ↦ B i t ω))
    (hsep : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε > 0, ∀ ⦃t : ℝ≥0⦄, t ≤ T → ∀ ⦃i j : Fin n⦄, i < j →
      ε ≤ truncatedDysonPath ε x (fun s k ↦ Real.sqrt (2 / (β * n)) * B k s ω) t i -
        truncatedDysonPath ε x (fun s k ↦ Real.sqrt (2 / (β * n)) * B k s ω) t j) :
    IsDysonSolution β n x P B
      (fun t ω ↦ limUnder atTop fun m : ℕ ↦
        truncatedDysonPath (((m : ℝ) + 1)⁻¹) x
          (fun s k ↦ Real.sqrt (2 / (β * n)) * B k s ω) t) := by
  rw [isDysonSolution_iff_ae_isPathwiseDysonSolution]
  have hB_all : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t ↦ B i t ω) := ae_all_iff.2 hB
  filter_upwards [hB_all, hsep] with ω hω hsep_ω
  have hw : Continuous (fun s k ↦ Real.sqrt (2 / (β * n)) * B k s ω) :=
    continuous_pi fun k ↦ continuous_const.mul (hω k)
  exact isPathwiseDysonSolution_limUnder_truncatedDysonPath hw hsep_ω

end GlobalPath

end TauCeti.Probability
