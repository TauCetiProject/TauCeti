/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Basic

import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.Analysis.LaplaceTransform.Real
import TauCeti.MeasureTheory.Integral.Asymptotics
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.IntegrationByParts

/-!
# Abelian Laplace-moment theorems for iterated improper tail integrals

This file relates the repeated improper tail integrals `TauCeti.iteratedTailIntegral f (n + 1) 0` of
a function `f : ℝ → E` on `[0, ∞)` to the `p → 0⁺` limit of its Laplace moments
`∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t` and of the `n`-th derivatives of its Laplace
transform `p ↦ ∫ t in Ioi 0, exp (-(p * t)) • f t`.

Crucially, `f` and its intermediate tail integrals are **not** required to be absolutely integrable
on `(0, ∞)`: the Abelian theorems assume that the exponentially weighted Laplace integrals
`t ↦ exp (-(p * t)) • f t` (`p > 0`) are Bochner integrable on `(0, ∞)` and that the unweighted
improper integrals `R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge (not
necessarily absolutely) as `R → ∞`.

General real Laplace moment integrability, parametric differentiation, and the rescaled Abelian
limit live in `TauCeti.Analysis.LaplaceTransform.Real`. Specializations to oscillatory functions
satisfying `TauCeti.HasOscillatoryDecay` live in `TauCeti.Analysis.LaplaceTransform.Oscillatory`.

## Main results

* `TauCeti.tendsto_integral_exp_neg_mul_smul_nhdsGT_zero` and
  `TauCeti.tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero`: if `t ↦ exp (-(p * t)) • f t` is
  Bochner integrable on `(0, ∞)` for every `p > 0` and all improper integrals
  `R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge as `R → ∞`, then
  `∫ t in Ioi 0, (exp (-(p * t)) * t ^ n) • f t → n ! • iteratedTailIntegral f (n + 1) 0` as
  `p → 0⁺`.
* `TauCeti.tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero`: `n`-th derivative form
  `iteratedDeriv n L p → ((-1) ^ n * n !) • iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology
open scoped Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Exponentially weighted improper integration by parts on `(0, ∞)` -/

/-- Exponential-polynomial moment integrability on `(0, ∞)` for a function continuous on
`[0, ∞)` and bounded at `+∞`. -/
private theorem integrableOn_exp_neg_mul_mul_pow_smul_of_isBigO_one {h : ℝ → E} {p : ℝ}
    (hp : 0 < p) (k : ℕ) (hh_cont : ContinuousOn h (Ici 0)) (hh_top : h =O[atTop] (1 : ℝ → ℝ)) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ k) • h t) (Ioi 0) := by
  have hw : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ k) (Ioi 0) := by
    simpa only [mul_comm] using integrableOn_pow_mul_exp_neg_mul_Ioi k hp
  exact hw.smul_of_continuousOn_of_isBigO_one Ioi_subset_Ici_self hh_cont hh_top

/-- Improper integration by parts for `∫ t in Ioi 0, exp (-(p * t)) • g t` (`0 < p`). -/
private theorem integral_Ioi_exp_neg_mul_smul_eq {g : ℝ → E} {p : ℝ} (hp : 0 < p)
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
private theorem integral_Ioi_exp_neg_mul_mul_pow_succ_smul_eq {g : ℝ → E} {p : ℝ}
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
    integrableOn_exp_neg_mul_mul_pow_smul_of_isBigO_one hp k
      (continuousOn_iteratedTailIntegral_one hg_loc)
      ((tendsto_iteratedTailIntegral_one_atTop hg_loc hL).isBigO_one ℝ)
  have hG_smul (k : ℕ) (c : ℝ) : IntegrableOn
      (fun s : ℝ ↦ c • ((Real.exp (-(p * s)) * s ^ k) • iteratedTailIntegral g 1 s)) (Ioi 0) :=
    (hG_int k).smul c
  have hpt : (fun s : ℝ ↦ deriv φ s • iteratedTailIntegral g 1 s) = fun s ↦
      (m + 1 : ℝ) • ((Real.exp (-(p * s)) * s ^ m) • iteratedTailIntegral g 1 s) -
        p • ((Real.exp (-(p * s)) * s ^ (m + 1)) • iteratedTailIntegral g 1 s) := by
    ext s
    rw [hderiv, sub_smul, mul_smul (m + 1 : ℝ), mul_smul p]
  rw [heq, hpt, integral_sub (hG_smul m (m + 1 : ℝ)) (hG_smul (m + 1) p),
    integral_smul, integral_smul]
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
      have hh_int : IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ (m + 1)) • h t) (Ioi 0) :=
        integrableOn_exp_neg_mul_mul_pow_smul_of_isBigO_one hp (m + 1) hh_cont
          (hh_top.isBigO_one ℝ)
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
`R ↦ ∫ t in 0..R, iteratedTailIntegral f m t` (`m ≤ n`) converge (not necessarily absolutely) as
`R → ∞`, then
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
      simpa only [pow_zero, mul_one] using
        integrableOn_exp_neg_mul_mul_pow_smul_of_isBigO_one hp 0 hG_cont (hG_top.isBigO_one ℝ)
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

/-- **Abel's theorem for Laplace integrals of possibly conditionally convergent improper
integrals.** If `t ↦ exp (-(p * t)) • f t` is Bochner integrable on `(0, ∞)` for every `p > 0` and
the unweighted improper integral `R ↦ ∫ t in 0..R, f t` converges (not necessarily absolutely) as
`R → ∞`, then `∫ t in Ioi 0, exp (-(p * t)) • f t → iteratedTailIntegral f 1 0` as `p → 0⁺`. -/
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

end TauCeti
