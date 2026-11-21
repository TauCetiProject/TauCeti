/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Oscillatory

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Asymptotics
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.Exp.Laplace
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Abelian Laplace-moment theorems for iterated improper tail integrals

This file relates the repeated improper tail integrals `TauCeti.iteratedTailIntegral f (n + 1) 0` of
a function `f : ℝ → E` on `[0, ∞)` to the `p → 0⁺` limit of its Laplace moments
`∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t` and of the `n`-th derivatives of its Laplace
transform `p ↦ ∫ t in Ioi 0, exp (-(p * t)) • f t`.

Crucially, `f` and its intermediate tail integrals are **not** required to be absolutely integrable
on `(0, ∞)`: the Abelian theorems assume Bochner integrability of `t ↦ exp (-(p * t)) • f t` on
`(0, ∞)` for every `p > 0` together with conditional convergence of the improper integrals
`R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` as `R → ∞` for `m ≤ n`. For functions locally
integrable on `[0, ∞)` satisfying `TauCeti.HasOscillatoryDecay c q α₀ f` with `c ≠ 0`, `1 ≤ q`, and
`0 < α₀ + q - 1`, those Laplace-integrability and improper-convergence hypotheses are discharged
automatically, yielding Laplace-moment and Laplace-derivative limits for oscillatory functions such
as Fresnel integrals and negative-axis oscillatory special functions.

General real Laplace moment integrability and parametric differentiation live in
`TauCeti.MeasureTheory.Integral.Exp.Laplace`.

## Main results

* `TauCeti.tendsto_integral_exp_neg_mul_smul_nhdsGT_zero` and
  `TauCeti.tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero`: if `t ↦ exp (-(p * t)) • f t` is
  Bochner integrable on `(0, ∞)` for every `p > 0` and all improper integrals
  `R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge as `R → ∞`, then
  `∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t → n ! • iteratedTailIntegral f (n + 1) 0` as
  `p → 0⁺`.
* `TauCeti.tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero`: `n`-th derivative form
  `iteratedDeriv n L p → ((-1) ^ n * n !) • iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`.
* `TauCeti.HasOscillatoryDecay.integrableOn_exp_neg_mul_mul`,
  `TauCeti.HasOscillatoryDecay.tendsto_integral_exp_neg_mul_mul_pow_mul_nhdsGT_zero`, and
  `TauCeti.HasOscillatoryDecay.tendsto_iteratedDeriv_integral_exp_neg_mul_mul_nhdsGT_zero`:
  Abelian Laplace-moment and Laplace-derivative limits for functions locally integrable on `[0, ∞)`
  satisfying `HasOscillatoryDecay c q α₀ f` (`c ≠ 0`, `1 ≤ q`, `0 < α₀ + q - 1`).
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology
open scoped Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Improper integration by parts on `(0, ∞)` -/

/-- Improper integration by parts on `(0, ∞)` for a conditionally convergent improper tail integral
`G := iteratedTailIntegral g 1` against a `C¹` weight `φ` whose derivative is integrable on
`(0, ∞)`. -/
private theorem integral_Ioi_smul_eq_of_tendsto [CompleteSpace E] {φ : ℝ → ℝ} {g : ℝ → E}
    (hg_loc : LocallyIntegrableOn g (Ici 0))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, g t) atTop (𝓝 L))
    (hφ : ContDiff ℝ 1 φ) (hφ'_int : IntegrableOn (deriv φ) (Ioi 0))
    (hφg_int : IntegrableOn (fun t ↦ φ t • g t) (Ioi 0)) :
    IntegrableOn (fun s ↦ deriv φ s • iteratedTailIntegral g 1 s) (Ioi 0) ∧
      ∫ t in Ioi 0, φ t • g t =
        φ 0 • iteratedTailIntegral g 1 0 +
          ∫ s in Ioi 0, deriv φ s • iteratedTailIntegral g 1 s := by
  obtain ⟨L, hL⟩ := hg_conv
  set G := iteratedTailIntegral g 1
  have hG_cont : ContinuousOn G (Ici 0) := continuousOn_iteratedTailIntegral_one hg_loc
  have hG_top : Tendsto G atTop (𝓝 0) := tendsto_iteratedTailIntegral_one_atTop hg_loc hL
  have hφ'G_int : IntegrableOn (fun s ↦ deriv φ s • G s) (Ioi 0) :=
    hφ'_int.smul_of_continuousOn_of_isBigO_one Ioi_subset_Ici_self hG_cont (hG_top.isBigO_one ℝ)
  have hφ_eq (R : ℝ) : ∫ s in 0..R, deriv φ s = φ R - φ 0 :=
    _root_.intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ hφ.differentiable one_ne_zero s)
      ((hφ.continuous_deriv le_rfl).intervalIntegrable 0 R)
  have hφ_top : Tendsto φ atTop (𝓝 (φ 0 + ∫ s in Ioi 0, deriv φ s)) := by
    simpa only [id_eq, hφ_eq, add_sub_cancel] using
      (intervalIntegral_tendsto_integral_Ioi 0 hφ'_int tendsto_id).const_add (φ 0)
  have hRHS : Tendsto (fun R : ℝ ↦
      φ 0 • G 0 - φ R • G R + ∫ s in 0..R, deriv φ s • G s) atTop
      (𝓝 (φ 0 • G 0 + ∫ s in Ioi 0, deriv φ s • G s)) := by
    simpa using (tendsto_const_nhds.sub (hφ_top.smul hG_top)).add
      (intervalIntegral_tendsto_integral_Ioi 0 hφ'G_int tendsto_id)
  refine ⟨hφ'G_int, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hφg_int tendsto_id)
    (hRHS.congr' ?_)⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hibp := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hR hφ
    (hg_loc.intervalIntegrable (by rw [uIcc_of_le hR]; exact Icc_subset_Ici_self))
  have hφ'G_sub : ∫ s in 0..R, deriv φ s • (∫ t in 0..s, g t) =
      (φ R - φ 0) • G 0 - ∫ s in 0..R, deriv φ s • G s := by
    rw [← hφ_eq, ← _root_.intervalIntegral.integral_smul_const,
      ← _root_.intervalIntegral.integral_sub
        ((hφ.continuous_deriv le_rfl).continuousOn.fun_smul continuousOn_const).intervalIntegrable
        (((hφ.continuous_deriv le_rfl).continuousOn.fun_smul
          (hG_cont.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc hR)]
    refine _root_.intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le hR] at hs
    rw [← iteratedTailIntegral_one_sub_eq_intervalIntegral hg_loc le_rfl le_rfl hs.1 hL, smul_sub]
  have hlhs : ∫ t in 0..R, φ t • g t = φ R • (G 0 - G R) -
      ((φ R - φ 0) • G 0 - ∫ s in 0..R, deriv φ s • G s) := by
    rw [iteratedTailIntegral_one_sub_eq_intervalIntegral hg_loc le_rfl le_rfl hR hL, ← hφ'G_sub,
      hibp, sub_sub_cancel]
  rw [id, hlhs, smul_sub, sub_smul]
  abel

/-- Improper integration by parts for `∫ t in Ioi 0, exp (-(p * t)) • g t` (`0 < p`). -/
private theorem integral_Ioi_exp_neg_mul_smul_eq [CompleteSpace E] {g : ℝ → E} {p : ℝ} (hp : 0 < p)
    (hg_loc : LocallyIntegrableOn g (Ici 0))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, g t) atTop (𝓝 L))
    (hg_int : IntegrableOn (fun t ↦ Real.exp (-(p * t)) • g t) (Ioi 0)) :
    ∫ t in Ioi 0, Real.exp (-(p * t)) • g t =
      iteratedTailIntegral g 1 0 -
        p • ∫ s in Ioi 0, Real.exp (-(p * s)) • iteratedTailIntegral g 1 s := by
  have hderiv (s : ℝ) :
      deriv (fun t : ℝ ↦ Real.exp (-(p * t))) s = -p * Real.exp (-(p * s)) :=
    ((((hasDerivAt_id s).const_mul p).neg.exp).congr_deriv (by simp; ring)).deriv
  have hφ'_int : IntegrableOn (deriv fun t : ℝ ↦ Real.exp (-(p * t))) (Ioi 0) :=
    IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi 0 hp).const_mul (-p))
      (fun s _ ↦ by simp [hderiv, neg_mul]) measurableSet_Ioi
  obtain ⟨_, heq⟩ := integral_Ioi_smul_eq_of_tendsto hg_loc hg_conv (by fun_prop) hφ'_int hg_int
  rw [heq]
  simp [hderiv, mul_smul, integral_neg, integral_smul, sub_eq_add_neg]

/-- Improper integration by parts for `∫ t in Ioi 0, (exp (-(p * t)) * t ^ (m + 1)) • g t`
(`0 < p`). -/
private theorem integral_Ioi_exp_neg_mul_mul_pow_succ_smul_eq [CompleteSpace E] {g : ℝ → E} {p : ℝ}
    (hp : 0 < p) (m : ℕ) (hg_loc : LocallyIntegrableOn g (Ici 0))
    (hg_conv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, g t) atTop (𝓝 L))
    (hg_int : IntegrableOn (fun t ↦ (Real.exp (-(p * t)) * t ^ (m + 1)) • g t) (Ioi 0)) :
    ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ (m + 1)) • g t =
      ((m + 1 : ℝ) • ∫ s in Ioi 0, (Real.exp (-(p * s)) * s ^ m) • iteratedTailIntegral g 1 s) -
        p • ∫ s in Ioi 0, (Real.exp (-(p * s)) * s ^ (m + 1)) • iteratedTailIntegral g 1 s := by
  obtain ⟨L, hL⟩ := hg_conv
  let φ : ℝ → ℝ := fun t ↦ Real.exp (-(p * t)) * t ^ (m + 1)
  let φ' : ℝ → ℝ := fun s ↦
    (m + 1 : ℝ) * (Real.exp (-(p * s)) * s ^ m) - p * (Real.exp (-(p * s)) * s ^ (m + 1))
  have hderiv (s : ℝ) : deriv φ s = φ' s :=
    (((((hasDerivAt_id s).const_mul p).neg.exp).mul
      (hasDerivAt_pow (m + 1) s)).congr_deriv (by simp [φ']; ring)).deriv
  have hpow_int (k : ℕ) : IntegrableOn (fun s : ℝ ↦ Real.exp (-(p * s)) * s ^ k) (Ioi 0) := by
    simpa only [mul_comm] using integrableOn_pow_mul_exp_neg_mul_Ioi k hp
  have hφ'_int : IntegrableOn (deriv φ) (Ioi 0) :=
    IntegrableOn.congr_fun
      (((hpow_int m).const_mul (m + 1 : ℝ)).sub ((hpow_int (m + 1)).const_mul p))
      (fun s _ ↦ (hderiv s).symm) measurableSet_Ioi
  obtain ⟨_, heq⟩ := integral_Ioi_smul_eq_of_tendsto hg_loc ⟨L, hL⟩ (by fun_prop) hφ'_int hg_int
  have hG_int (k : ℕ) : IntegrableOn
      (fun s : ℝ ↦ (Real.exp (-(p * s)) * s ^ k) • iteratedTailIntegral g 1 s) (Ioi 0) :=
    (hpow_int k).smul_of_continuousOn_of_isBigO_one Ioi_subset_Ici_self
      (continuousOn_iteratedTailIntegral_one hg_loc)
      ((tendsto_iteratedTailIntegral_one_atTop hg_loc hL).isBigO_one ℝ)
  have hpt : (fun s : ℝ ↦ deriv φ s • iteratedTailIntegral g 1 s) =
      ((m + 1 : ℝ) • fun s : ℝ ↦ (Real.exp (-(p * s)) * s ^ m) • iteratedTailIntegral g 1 s) -
        (p • fun s : ℝ ↦ (Real.exp (-(p * s)) * s ^ (m + 1)) • iteratedTailIntegral g 1 s) := by
    ext s; simp only [hderiv, φ', Pi.sub_apply, Pi.smul_apply]
    rw [sub_smul, mul_smul (m + 1 : ℝ), mul_smul p]
  rw [heq, hpt, Pi.sub_def, integral_sub ((hG_int m).smul (m + 1 : ℝ)) ((hG_int (m + 1)).smul p),
    Pi.smul_def, Pi.smul_def, integral_smul, integral_smul]
  simp [φ]

/-! ### Vanishing of rescaled Laplace moments and the Abelian theorem -/

/-- Inductive vanishing lemma (`k ≤ j`): if `h` is continuous on `[0, ∞)`, `h(t) → 0` as `t → ∞`,
and all repeated improper tail integrals `R ↦ ∫ t in 0..R, iteratedTailIntegral h r t` (`r < k`)
converge as `R → ∞`, then
`p ^ (j + 1 - k) • ∫ t in Ioi 0, (exp (-(p * t)) * t ^ j) • h t → 0` as `p → 0⁺`. -/
private theorem tendsto_pow_sub_smul_integral_exp_neg_mul_mul_pow_smul_zero [CompleteSpace E] :
    ∀ {k j : ℕ}, k ≤ j → ∀ {h : ℝ → E}, ContinuousOn h (Ici 0) → Tendsto h atTop (𝓝 0) →
      (∀ r < k, ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral h r t) atTop (𝓝 L)) →
      Tendsto (fun p : ℝ ↦ p ^ (j + 1 - k) • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t)
        (𝓝[>] 0) (𝓝 0)
  | 0, j, _, _, hh_cont, hh_top, _ => by
      simpa using tendsto_pow_succ_smul_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero
        (hh_cont.locallyIntegrableOn measurableSet_Ici) hh_top j
  | k + 1, j, hkj, h, hh_cont, hh_top, hh_conv => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hkm : k ≤ m := Nat.le_of_succ_le_succ hkj
      have hloc : LocallyIntegrableOn h (Ici 0) := hh_cont.locallyIntegrableOn measurableSet_Ici
      obtain ⟨L0, hL0⟩ := hh_conv 0 (Nat.zero_lt_succ k)
      have hL0' : Tendsto (fun R : ℝ ↦ ∫ t in 0..R, h t) atTop (𝓝 L0) := by simpa using hL0
      have hH_cont := continuousOn_iteratedTailIntegral_one hloc
      have hH_top := tendsto_iteratedTailIntegral_one_atTop hloc hL0'
      have hH_conv : ∀ r < k, ∃ L, Tendsto
          (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral (iteratedTailIntegral h 1) r t)
          atTop (𝓝 L) := fun r hr ↦ by
        simpa only [← iteratedTailIntegral_succ'] using hh_conv (r + 1) (Nat.succ_lt_succ hr)
      have hdiff := ((tendsto_pow_sub_smul_integral_exp_neg_mul_mul_pow_smul_zero hkm hH_cont
        hH_top hH_conv).const_smul (m + 1 : ℝ)).sub
        (tendsto_pow_sub_smul_integral_exp_neg_mul_mul_pow_smul_zero (Nat.le_succ_of_le hkm)
          hH_cont hH_top hH_conv)
      rw [smul_zero, sub_self] at hdiff
      refine hdiff.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
      have hw : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ (m + 1)) (Ioi 0) := by
        simpa only [mul_comm] using integrableOn_pow_mul_exp_neg_mul_Ioi (m + 1) hp
      have hh_int : IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ (m + 1)) • h t) (Ioi 0) :=
        hw.smul_of_continuousOn_of_isBigO_one Ioi_subset_Ici_self hh_cont (hh_top.isBigO_one ℝ)
      have hk₁ : m + 1 + 1 - (k + 1) = m + 1 - k := by omega
      have hk₂ : m + 2 - k = m + 1 - k + 1 := by omega
      rw [hk₁, integral_Ioi_exp_neg_mul_mul_pow_succ_smul_eq hp m hloc ⟨L0, hL0'⟩ hh_int,
        smul_sub, smul_comm, hk₂, pow_succ, mul_smul]

/-- Base case (`n = 0`) of the Abelian Laplace theorem assuming `[CompleteSpace E]`. -/
private theorem tendsto_integral_exp_neg_mul_smul_nhdsGT_zero_aux [CompleteSpace E] {f : ℝ → E}
    (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, f t) atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) • f t) (𝓝[>] 0)
      (𝓝 (iteratedTailIntegral f 1 0)) := by
  have hloc := locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul (hf 1 one_pos)
  obtain ⟨L0, hL0⟩ := hconv
  have hlim : Tendsto (fun p : ℝ ↦ iteratedTailIntegral f 1 0 -
      p • ∫ s in Ioi 0, Real.exp (-(p * s)) • iteratedTailIntegral f 1 s)
      (𝓝[>] 0) (𝓝 (iteratedTailIntegral f 1 0)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_succ_smul_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero
        (locallyIntegrableOn_iteratedTailIntegral hloc 1)
        (tendsto_iteratedTailIntegral_one_atTop hloc hL0) 0)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  exact (integral_Ioi_exp_neg_mul_smul_eq hp hloc ⟨L0, hL0⟩ (hf p hp)).symm

/-- **Abelian Laplace-moment theorem for `iteratedTailIntegral`.** If `t ↦ exp (-(p * t)) • f t` is
Bochner integrable on `(0, ∞)` for every `p > 0` and all improper tail integrals
`R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge as `R → ∞`, then
`∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t → n ! • iteratedTailIntegral f (n + 1) 0` as
`p → 0⁺`. -/
theorem tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero {f : ℝ → E} {n : ℕ}
    (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∀ m ≤ n, ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral f m t)
      atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ n) • f t) (𝓝[>] 0)
      (𝓝 ((n.factorial : ℝ) • iteratedTailIntegral f (n + 1) 0)) := by
  by_cases hE : CompleteSpace E
  swap
  · simp_rw [integral_of_not_completeSpace hE, iteratedTailIntegral_succ_of_not_completeSpace hE,
      smul_zero]
    exact tendsto_const_nhds
  induction n generalizing f with
  | zero =>
    simpa using tendsto_integral_exp_neg_mul_smul_nhdsGT_zero_aux hf (by simpa using hconv 0 le_rfl)
  | succ n ih =>
    have hloc := locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul (hf 1 one_pos)
    obtain ⟨L0, hL0⟩ := hconv 0 (Nat.zero_le _)
    have hL0' : Tendsto (fun R : ℝ ↦ ∫ t in 0..R, f t) atTop (𝓝 L0) := by simpa using hL0
    have hG_cont := continuousOn_iteratedTailIntegral_one hloc
    have hG_top := tendsto_iteratedTailIntegral_one_atTop hloc hL0'
    have hG_lap : ∀ p > 0, IntegrableOn
        (fun s : ℝ ↦ Real.exp (-(p * s)) • iteratedTailIntegral f 1 s) (Ioi 0) := fun p hp ↦ by
      have hw : IntegrableOn (fun s : ℝ ↦ Real.exp (-(p * s))) (Ioi 0) := by
        simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hp
      exact hw.smul_of_continuousOn_of_isBigO_one Ioi_subset_Ici_self hG_cont (hG_top.isBigO_one ℝ)
    have hG_conv : ∀ m ≤ n, ∃ L, Tendsto
        (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral (iteratedTailIntegral f 1) m t)
        atTop (𝓝 L) := fun m hm ↦ by
      simpa only [← iteratedTailIntegral_succ'] using hconv (m + 1) (Nat.succ_le_succ hm)
    have hlim := ((ih hG_lap hG_conv).const_smul (n + 1 : ℝ)).sub
      (tendsto_pow_sub_smul_integral_exp_neg_mul_mul_pow_smul_zero (le_rfl : n + 1 ≤ n + 1)
        hG_cont hG_top fun r hr ↦ hG_conv r (Nat.le_of_lt_succ hr))
    rw [sub_zero, ← iteratedTailIntegral_succ' f (n + 1), smul_smul] at hlim
    push_cast [Nat.factorial_succ]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
    simpa using (integral_Ioi_exp_neg_mul_mul_pow_succ_smul_eq hp n hloc ⟨L0, hL0'⟩
      (integrableOn_exp_neg_mul_mul_pow_smul_of_lt (half_lt_self hp) (hf (p / 2) (half_pos hp))
        (n + 1))).symm

/-- **Abel's theorem for conditionally convergent Laplace integrals.** If
`t ↦ exp (-(p * t)) • f t` is Bochner integrable on `(0, ∞)` for every `p > 0` and the improper
integral `R ↦ ∫ t in 0..R, f t` converges as `R → ∞`, then
`∫ t in Ioi 0, exp (-(p * t)) • f t → iteratedTailIntegral f 1 0` as `p → 0⁺`. -/
theorem tendsto_integral_exp_neg_mul_smul_nhdsGT_zero {f : ℝ → E}
    (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, f t) atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) • f t) (𝓝[>] 0)
      (𝓝 (iteratedTailIntegral f 1 0)) := by
  simpa using tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero (n := 0) hf fun m hm ↦ by
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    simpa using hconv

/-- **Abelian Laplace-derivative theorem for `iteratedTailIntegral`.** Under the hypotheses of
`tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero`, the `n`-th derivative of the Laplace
integral `q ↦ ∫ t in Ioi 0, exp (-(q * t)) • f t` converges to
`((-1) ^ n * n !) • iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`. -/
theorem tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero {f : ℝ → E}
    {n : ℕ} (hf : ∀ p > 0, IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi 0))
    (hconv : ∀ m ≤ n, ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in 0..R, iteratedTailIntegral f m t)
      atTop (𝓝 L)) :
    Tendsto (fun p : ℝ ↦
        iteratedDeriv n (fun q : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(q * t)) • f t) p)
      (𝓝[>] 0) (𝓝 (((-1 : ℝ) ^ n * n.factorial) • iteratedTailIntegral f (n + 1) 0)) := by
  have hm := (tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero hf hconv).const_smul
    ((-1 : ℝ) ^ n)
  rw [smul_smul] at hm
  refine hm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  exact (iteratedDeriv_integral_exp_neg_mul_smul (half_lt_self hp)
    (hf (p / 2) (half_pos hp)) n).symm

/-! ### Oscillatory Abelian Laplace corollaries -/

namespace HasOscillatoryDecay

/-- Every locally integrable function on `[a, ∞)` satisfying `HasOscillatoryDecay c q α₀ f` has an
absolutely convergent Laplace integral on `(a, ∞)` for every `p > 0`. -/
theorem integrableOn_exp_neg_mul_mul {c q α₀ a p : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici a)) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * f t) (Ioi a) := by
  have hexp : f =O[atTop] fun t : ℝ ↦ Real.exp ((p / 2) * t) :=
    hf.isBigO_rpow_neg.trans (isLittleO_rpow_exp_pos_mul_atTop (-α₀) (half_pos hp)).isBigO
  have hIci := integrableOn_exp_neg_mul_of_isBigO_exp hloc hexp (half_lt_self hp)
  simpa only [neg_mul] using hIci.mono_set Ioi_subset_Ici_self

/-- **Oscillatory Abelian Laplace-moment theorem.** If `f` is locally integrable on `[0, ∞)` and
satisfies `HasOscillatoryDecay c q α₀ f` with `c ≠ 0`, `1 ≤ q`, and `0 < α₀ + q - 1`, then for
every `n : ℕ`,
`∫ t in Ioi 0, exp (-(p * t)) * t ^ n * f t → n ! * iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`.
-/
theorem tendsto_integral_exp_neg_mul_mul_pow_mul_nhdsGT_zero {c q α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hq : 1 ≤ q) (hα : 0 < α₀ + q - 1)
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) * t ^ n * f t) (𝓝[>] 0)
      (𝓝 ((n.factorial : ℝ) * TauCeti.iteratedTailIntegral f (n + 1) 0)) := by
  simpa only [smul_eq_mul] using tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero
    (fun p hp ↦ hf.integrableOn_exp_neg_mul_mul hloc hp)
    (fun m _ ↦ ⟨_, hf.tendsto_intervalIntegral_iteratedTailIntegral hc hq hα m 0⟩)

/-- **Oscillatory Abelian Laplace-derivative theorem.** Under the hypotheses of
`HasOscillatoryDecay.tendsto_integral_exp_neg_mul_mul_pow_mul_nhdsGT_zero`, the `n`-th derivative of
the Laplace integral `r ↦ ∫ t in Ioi 0, exp (-(r * t)) * f t` tends to
`(-1) ^ n * n ! * iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`. -/
theorem tendsto_iteratedDeriv_integral_exp_neg_mul_mul_nhdsGT_zero {c q α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hq : 1 ≤ q) (hα : 0 < α₀ + q - 1)
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    Tendsto (fun p : ℝ ↦
        iteratedDeriv n (fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) * f t) p)
      (𝓝[>] 0) (𝓝 ((-1 : ℝ) ^ n * n.factorial * TauCeti.iteratedTailIntegral f (n + 1) 0)) := by
  simpa only [smul_eq_mul] using tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero
    (fun p hp ↦ hf.integrableOn_exp_neg_mul_mul hloc hp)
    (fun m _ ↦ ⟨_, hf.tendsto_intervalIntegral_iteratedTailIntegral hc hq hα m 0⟩)

end HasOscillatoryDecay

end TauCeti
