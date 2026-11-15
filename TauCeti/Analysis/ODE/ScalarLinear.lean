/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module

/-!
# Solutions of a scalar linear equation

An absolutely continuous solution of `f' = k • f` almost everywhere on a compact real interval
is the exponential solution with its prescribed initial value. No differentiability at every
point, nor an integrability assumption on a separately supplied velocity, is needed.
The product `exp (-k * t) • f t` has zero derivative almost everywhere, so the AC
fundamental theorem of calculus makes this product constant on the entire interval.

For imaginary `k`, this identifies plane curves whose velocity is a fixed rotation and scaling
of their position relative to a center. Such equations describe equality in the area–energy
inequality for closed plane curves.

For a continuous, time-dependent real coefficient `g`, a differentiable solution of `P' = g • P`
on an interval `J`, open or closed, is `P t = exp (∫ₛᵗ g) • P s` for all `s, t ∈ J`
(`TauCeti.eq_exp_integral_smul_of_hasDerivWithinAt_smul`), by the integrating factor
`exp (-∫ₛᵘ g)`. For a constant coefficient `c`, a function with `v' = c • v` at every time
`τ ≤ a` (with a two-sided derivative at `a`) is `v τ = exp (c (τ - a)) • v a` for `τ ≤ a`
(`TauCeti.eq_exp_smul_of_hasDerivAt_smul_of_le`).
-/

public section

open MeasureTheory Set Complex
open scoped Topology

namespace AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E} {a b : ℝ} {k : ℂ}

/-- An absolutely continuous solution of `f' = k • f` almost everywhere is the exponential
solution, at every point of its parameter interval. The interval may have either orientation. -/
theorem eq_exp_smul_of_ae_hasDerivAt_smul (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (k • f t) t)
    {t : ℝ} (ht : t ∈ uIcc a b) :
    f t = exp (k * (t - a)) • f a := by
  let q : ℝ → E := fun u ↦ exp (-k * u) • f u
  have he : ContDiff ℝ 1 (fun u : ℝ ↦ exp (-k * u)) :=
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hq : AbsolutelyContinuousOnInterval q a b := by
    exact (he.contDiffOn.absolutelyContinuousOnInterval.smul hf).congr
      (fun u _ ↦ by simp [q])
  have hz : ∀ᵐ u, u ∈ uIoc a b → HasDerivAt q 0 u := by
    filter_upwards [hd] with u hu hmem
    have he' := (((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-k)).cexp)
    convert he'.fun_smul (hu hmem) using 1 <;> simp only [q, ofRealCLM_apply, ofReal_one]
    simp [smul_smul]
  have hz' : ∀ᵐ u, u ∈ uIcc a b → HasDerivAt q 0 u := by
    filter_upwards [hz, volume.ae_ne (min a b)] with u hu hne hmem
    exact hu ⟨lt_of_le_of_ne hmem.1 hne.symm, hmem.2⟩
  obtain ⟨C, hC⟩ := hq.const_of_ae_hasDerivAt_zero hz'
  have hqt : q t = q a := (hC t ht).trans (hC a left_mem_uIcc).symm
  have hcancel (u : ℝ) : exp (k * u) • q u = f u := by
    simp only [q, smul_smul, ← exp_add, neg_mul, add_neg_cancel, exp_zero, one_smul]
  calc
    f t = exp (k * t) • q a := by rw [← hcancel t, hqt]
    _ = exp (k * (t - a)) • f a := by
      dsimp only [q]
      rw [smul_smul, ← exp_add]
      congr 2
      ring

/-- An absolutely continuous curve has velocity `k • (f - c)` almost everywhere exactly
when it is an exponential curve about `c`, with arbitrary amplitude in the complex normed space. -/
theorem ae_hasDerivAt_smul_sub_iff (hf : AbsolutelyContinuousOnInterval f a b) (c : E) (k : ℂ) :
    (∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (k • (f t - c)) t) ↔
      ∃ w : E, ∀ t ∈ uIcc a b, f t = c + exp (k * t) • w := by
  constructor
  · intro hd
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
      (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
    have hg := hf.fun_sub hc
    have hgd : ∀ᵐ t, t ∈ uIoc a b →
        HasDerivAt (fun u ↦ f u - c) (k • (f t - c)) t := by
      filter_upwards [hd] with t ht hmem
      exact (ht hmem).sub_const c
    refine ⟨exp (-k * a) • (f a - c), fun t ht ↦ ?_⟩
    have hsol := hg.eq_exp_smul_of_ae_hasDerivAt_smul hgd ht
    calc
      f t = c + exp (k * (t - a)) • (f a - c) := by
        exact (sub_eq_iff_eq_add.mp hsol).trans (add_comm _ _)
      _ = c + exp (k * t) • (exp (-k * a) • (f a - c)) := by
        rw [smul_smul, ← exp_add]
        congr 3
        ring
  · rintro ⟨w, hw⟩
    filter_upwards [volume.ae_ne (max a b)] with t hne ht
    have ht' : t ∈ Ioo (min a b) (max a b) := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    have heq : f =ᶠ[𝓝 t] (fun u : ℝ ↦ c + exp (k * u) • w) :=
      Filter.mem_of_superset (Ioo_mem_nhds ht'.1 ht'.2) fun u hu ↦ hw u (Ioo_subset_Icc_self hu)
    have hd := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul k).cexp.smul_const w).const_add c
    have hvalue := hw t (uIoc_subset_uIcc ht)
    convert hd.congr_of_eventuallyEq heq using 1
    simp only [ofRealCLM_apply, ofReal_one, mul_one, hvalue]
    simp [smul_smul, mul_comm]

end AbsolutelyContinuousOnInterval

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Integrating factor.** On an order-connected set `J`, a solution of the linear equation
`P' = g • P` within `J`, with real coefficient `g` continuous on `J`, satisfies
`P t = exp (∫ₛᵗ g) • P s` for all `s, t ∈ J`, in either order. -/
theorem eq_exp_integral_smul_of_hasDerivWithinAt_smul {J : Set ℝ} (hJc : J.OrdConnected)
    {g : ℝ → ℝ} (hg : ContinuousOn g J) {P : ℝ → V}
    (hP : ∀ u ∈ J, HasDerivWithinAt P (g u • P u) J u) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    P t = Real.exp (∫ u in s..t, g u) • P s := by
  -- Work on the interval `[[s, t]] ⊆ J`, and extend `g` continuously from it to all of `ℝ`, so
  -- that its primitive `G` is differentiable everywhere.
  have hsub : uIcc s t ⊆ J := hJc.uIcc_subset hs ht
  have hle : s ⊓ t ≤ s ⊔ t := inf_le_sup
  set g' : ℝ → ℝ := fun u ↦ g (projIcc (s ⊓ t) (s ⊔ t) hle u)
  have hg' : Continuous g' :=
    (hg.mono hsub).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun u ↦ Subtype.mem _
  have hgg' (u : ℝ) (hu : u ∈ uIcc s t) : g' u = g u := by
    simp only [g', projIcc_of_mem hle hu]
  set G : ℝ → ℝ := fun u ↦ ∫ τ in s..u, g' τ
  -- `u ↦ e^{-G u} P u` has zero derivative within `[[s, t]]`, so it is constant there.
  have hderiv (u : ℝ) (hu : u ∈ uIcc s t) :
      HasDerivWithinAt (fun u ↦ Real.exp (-G u) • P u) 0 (uIcc s t) u := by
    have hG := (hg'.integral_hasStrictDerivAt s u).hasDerivAt.hasDerivWithinAt (s := uIcc s t)
    refine (hG.neg.exp.smul ((hP u (hsub hu)).mono hsub)).congr_deriv ?_
    rw [hgg' u hu]
    module
  have hconst : Real.exp (-G t) • P t = Real.exp (-G s) • P s := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv (fun _ _ ↦ norm_zero.le)
      (convex_uIcc s t) left_mem_uIcc right_mem_uIcc
    rwa [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  have hGs : G s = 0 := intervalIntegral.integral_same
  have hGt : G t = ∫ u in s..t, g u := intervalIntegral.integral_congr fun u hu ↦ hgg' u hu
  rw [hGs, neg_zero, Real.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Real.exp_add, ← hGt, add_neg_cancel, Real.exp_zero, one_smul]

/-- **Constant-coefficient solutions on a closed left half-line.** If `v' = c • v` at every time
`τ ≤ a`, then `v τ = exp (c (τ - a)) • v a` for every `τ ≤ a`. The equation is only required at
times `τ ≤ a` (with a two-sided derivative at `a`), so `v` need not solve it after time `a`. -/
theorem eq_exp_smul_of_hasDerivAt_smul_of_le {v : ℝ → V} {c a : ℝ}
    (hv : ∀ τ, τ ≤ a → HasDerivAt v (c • v τ) τ) {τ : ℝ} (hτ : τ ≤ a) :
    v τ = Real.exp (c * (τ - a)) • v a := by
  have h := eq_exp_integral_smul_of_hasDerivWithinAt_smul ordConnected_Iic continuousOn_const
    (fun σ hσ ↦ (hv σ hσ).hasDerivWithinAt) (s := a) (mem_Iic.2 le_rfl) (mem_Iic.2 hτ)
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h

end TauCeti
