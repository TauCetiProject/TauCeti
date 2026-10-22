/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Absolutely continuous solutions of a complex scalar linear equation

An absolutely continuous solution of `f' = k f` almost everywhere on a compact real interval
is the exponential solution with its prescribed initial value. No differentiability at every
point, nor an integrability assumption on a separately supplied velocity, is needed.
The integrating factor has zero derivative almost everywhere, so the AC fundamental theorem
of calculus makes it constant on the entire interval.

For imaginary `k`, this identifies plane curves whose velocity is a fixed rotation and scaling
of their position relative to a center. Such equations describe equality in the area–energy
inequality for closed plane curves.
-/

public section

open MeasureTheory Set Complex
open scoped Topology

namespace AbsolutelyContinuousOnInterval

variable {f : ℝ → ℂ} {a b : ℝ} {k : ℂ}

/-- An absolutely continuous solution of `f' = k f` almost everywhere is the exponential
solution, at every point of its parameter interval. The interval may have either orientation. -/
theorem eq_mul_exp_of_ae_hasDerivAt_mul (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (k * f t) t)
    {t : ℝ} (ht : t ∈ uIcc a b) :
    f t = f a * exp (k * (t - a)) := by
  let q : ℝ → ℂ := fun u ↦ exp (-k * u) * f u
  have he : ContDiff ℝ 1 (fun u : ℝ ↦ exp (-k * u)) :=
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hq : AbsolutelyContinuousOnInterval q a b := by
    exact (he.contDiffOn.absolutelyContinuousOnInterval.smul hf).congr
      (fun u _ ↦ by simp [q])
  have hz : ∀ᵐ u, u ∈ uIoc a b → HasDerivAt q 0 u := by
    filter_upwards [hd] with u hu hmem
    have he' := (((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-k)).cexp)
    convert he'.fun_mul (hu hmem) using 1 <;> simp only [q, ofRealCLM_apply, ofReal_one]
    ring
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc ht
  have hzt : ∀ᵐ u, u ∈ uIoc a t → HasDerivAt q 0 u := by
    filter_upwards [hz, volume.ae_ne (min a b)] with u hu hne hmem
    exact hu ⟨lt_of_le_of_ne (hsub (uIoc_subset_uIcc hmem)).1 hne.symm,
      (hsub (uIoc_subset_uIcc hmem)).2⟩
  have hqt : q t = q a := by
    have h := (hq.mono hsub).integral_eq_sub_of_ae_hasDerivAt hzt
    simpa only [intervalIntegral.integral_zero, eq_comm, sub_eq_zero] using h
  have hcancel (u : ℝ) : exp (k * u) * q u = f u := by
    simp only [q, ← mul_assoc, ← exp_add, neg_mul, add_neg_cancel, exp_zero, one_mul]
  calc
    f t = exp (k * t) * q a := by rw [← hcancel t, hqt]
    _ = f a * exp (k * (t - a)) := by
      dsimp only [q]
      rw [← mul_assoc, ← exp_add, mul_comm _ (f a)]
      congr 2
      ring

/-- An absolutely continuous curve has velocity `k * (f - c)` almost everywhere exactly
when it is an exponential curve about `c`, with arbitrary complex amplitude. -/
theorem ae_hasDerivAt_mul_sub_iff (hf : AbsolutelyContinuousOnInterval f a b) (c k : ℂ) :
    (∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (k * (f t - c)) t) ↔
      ∃ w : ℂ, ∀ t ∈ uIcc a b, f t = c + w * exp (k * t) := by
  constructor
  · intro hd
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
      (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
    have hg := hf.fun_sub hc
    have hgd : ∀ᵐ t, t ∈ uIoc a b →
        HasDerivAt (fun u ↦ f u - c) (k * (f t - c)) t := by
      filter_upwards [hd] with t ht hmem
      exact (ht hmem).sub_const c
    refine ⟨(f a - c) * exp (-k * a), fun t ht ↦ ?_⟩
    have hsol := hg.eq_mul_exp_of_ae_hasDerivAt_mul hgd ht
    calc
      f t = c + (f a - c) * exp (k * (t - a)) := by
        linear_combination hsol
      _ = c + ((f a - c) * exp (-k * a)) * exp (k * t) := by
        rw [mul_assoc, ← exp_add]
        congr 3
        ring
  · rintro ⟨w, hw⟩
    filter_upwards [volume.ae_ne (max a b)] with t hne ht
    have ht' : t ∈ Ioo (min a b) (max a b) := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    have heq : f =ᶠ[𝓝 t] (fun u : ℝ ↦ c + w * exp (k * u)) :=
      Filter.mem_of_superset (Ioo_mem_nhds ht'.1 ht'.2) fun u hu ↦ hw u (Ioo_subset_Icc_self hu)
    have hd := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul k).cexp.const_mul w).const_add c
    have hvalue := hw t (uIoc_subset_uIcc ht)
    convert hd.congr_of_eventuallyEq heq using 1
    simp only [ofRealCLM_apply, ofReal_one, mul_one, hvalue]
    ring

end AbsolutelyContinuousOnInterval
