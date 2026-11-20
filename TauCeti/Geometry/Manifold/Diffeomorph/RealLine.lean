/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Germ
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Real diffeomorphisms with prescribed endpoint germs

Compactly supported germ extensions at `0` and `1` give a single real diffeomorphism with
prescribed exponential germs. The resulting logarithmic endpoint coordinates are exactly linear
on a common neighborhood.

The collar linearization needed by the sphere-complement construction in
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture), with
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) as a
supporting formalization reference, is implemented here by exponential endpoint corrections
using the native compactly supported germ-extension theorem.
-/

public section

noncomputable section

open Set Filter Metric Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- Separate compactly supported corrections realize the exponential germs at `0` and `1`. -/
theorem exists_diffeomorphs_eventuallyEq_exp_at_zero_one {c : ℝ} (hc : c ≠ 0) :
    ∃ Ψ₀ Ψ₁ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ,
      (Ψ₀ =ᶠ[𝓝 (0 : ℝ)] fun t ↦ (Real.exp (c * t) - 1) / c) ∧
      EqOn Ψ₀ id (Ioo (-1 / 4 : ℝ) (1 / 4))ᶜ ∧
      (Ψ₁ =ᶠ[𝓝 (1 : ℝ)] fun t ↦ 1 - (Real.exp (c * (1 - t)) - 1) / c) ∧
      EqOn Ψ₁ id (Ioo (3 / 4 : ℝ) (5 / 4))ᶜ := by
  let f₀ : ℝ → ℝ := fun t ↦ (Real.exp (c * t) - 1) / c
  let f₁ : ℝ → ℝ := fun t ↦ 1 - f₀ (1 - t)
  have hd₀ : HasDerivAt f₀ 1 0 := by
    convert (((Real.hasDerivAt_exp (c * 0)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_mul c)).sub_const 1).div_const c using 1 <;>
      simp [f₀, hc]
  have hd₁ : HasDerivAt f₁ 1 1 := by
    have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) 1 :=
      (hasDerivAt_id 1).const_sub 1
    have hd₀' : HasDerivAt f₀ 1 ((fun t : ℝ ↦ 1 - t) 1) := by
      simpa only [sub_self] using hd₀
    have h := (hd₀'.comp 1 hsub).const_sub 1
    simpa only [f₁, Function.comp_def, one_mul, neg_neg] using h
  have hspan : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp
  have hdet {f : ℝ → ℝ} {x : ℝ} (hd : HasDerivAt f 1 x) :
      0 < (fderiv ℝ f x).det := by
    rw [hd.hasFDerivAt.fderiv, hspan]
    simp
  obtain ⟨Ψ₀, K₀, -, hK₀, hfix₀, hΨ₀⟩ :=
    exists_diffeomorph_eventuallyEq_of_det_fderiv_pos (n := ⊤) (by simp)
      (g := f₀) (by filter_upwards with x; fun_prop) (by norm_num [f₀]) (hdet hd₀)
      (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  obtain ⟨Ψ₁, K₁, -, hK₁, hfix₁, hΨ₁⟩ :=
    exists_diffeomorph_eventuallyEq_of_det_fderiv_pos (n := ⊤) (by simp)
      (g := f₁) (by filter_upwards with x; fun_prop) (by norm_num [f₁, f₀]) (hdet hd₁)
      (isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioo (3 / 4) (5 / 4)))
  exact ⟨Ψ₀, Ψ₁, hΨ₀, fun x hx ↦ hfix₀ (fun hxK ↦ hx (hK₀ hxK)),
    hΨ₁, fun x hx ↦ hfix₁ (fun hxK ↦ hx (hK₁ hxK))⟩

/-- A real diffeomorphism fixing `0` and `1` realizes both endpoint exponential germs. -/
theorem exists_diffeomorph_eventuallyEq_exp_at_zero_one {c : ℝ} (hc : c ≠ 0) :
    ∃ Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ,
      Ψ 0 = 0 ∧ Ψ 1 = 1 ∧
      (Ψ =ᶠ[𝓝 (0 : ℝ)] fun t ↦ (Real.exp (c * t) - 1) / c) ∧
      (Ψ =ᶠ[𝓝 (1 : ℝ)] fun t ↦ 1 - (Real.exp (c * (1 - t)) - 1) / c) := by
  obtain ⟨Ψ₀, Ψ₁, hΨ₀, hfix₀, hΨ₁, hfix₁⟩ := exists_diffeomorphs_eventuallyEq_exp_at_zero_one hc
  have h₀ : Ψ₀ 0 = 0 := by simpa  using hΨ₀.self_of_nhds
  have h₁ : Ψ₁ 1 = 1 := by simpa  using hΨ₁.self_of_nhds
  have hfix₀' : Ψ₀ =ᶠ[𝓝 (1 : ℝ)] id := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1)] with x hx
    exact hfix₀ (by rintro ⟨_, hx'⟩; exact lt_asymm hx hx')
  have hfix₁' : Ψ₁ =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 3 / 4)] with x hx
    exact hfix₁ (by rintro ⟨hx', _⟩; exact lt_asymm hx hx')
  let Ψ := Ψ₀.trans Ψ₁
  have hΨ0 : Ψ 0 = 0 := by
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    rw [h₀, hfix₁'.self_of_nhds]
    rfl
  have hΨ1 : Ψ 1 = 1 := by
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    rw [hfix₀'.self_of_nhds]
    exact h₁
  have ht : Tendsto Ψ₀ (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [h₀] using Ψ₀.continuous.tendsto (0 : ℝ)
  refine ⟨Ψ, hΨ0, hΨ1, ?_, ?_⟩
  · filter_upwards [hΨ₀, hfix₁'.comp_tendsto ht] with t ht ht'
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    exact ht'.trans ht
  · filter_upwards [hΨ₁, hfix₀'] with t ht ht'
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply]
    rw [ht']
    exact ht

/-- One real diffeomorphism simultaneously linearizes both logarithmic endpoint coordinates. -/
theorem exists_diffeomorph_log_collars (c : ℝ) :
    ∃ Ψ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ, ∃ η : ℝ,
      Ψ 0 = 0 ∧ Ψ 1 = 1 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∀ s : ℝ, 0 < s → s < η →
        Ψ (Real.log (1 + s) / c) = s / c ∧
        Ψ (1 - Real.log (1 + s) / c) = 1 - s / c := by
  by_cases hc : c = 0
  · subst c
    refine ⟨Diffeomorph.refl 𝓘(ℝ) ℝ ∞, 1 / 8, rfl, rfl, by norm_num, le_rfl, ?_⟩
    intro s _ _
    simp
  obtain ⟨Ψ, h0, h1, hlo, hup⟩ := exists_diffeomorph_eventuallyEq_exp_at_zero_one hc
  have hlog : Tendsto (fun s : ℝ ↦ Real.log (1 + s) / c) (𝓝 0) (𝓝 0) := by
    have hlin : ContinuousAt (fun s : ℝ ↦ 1 + s) 0 := continuousAt_const.add continuousAt_id
    have h : ContinuousAt (fun s : ℝ ↦ Real.log (1 + s) / c) 0 :=
      hlin.log (by norm_num) |>.div_const c
    simpa using h.tendsto
  have hlog' : Tendsto (fun s : ℝ ↦ 1 - Real.log (1 + s) / c) (𝓝 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hlog
  have hboth := (hlo.comp_tendsto hlog).and (hup.comp_tendsto hlog')
  obtain ⟨ε, hε, heq⟩ := Metric.eventually_nhds_iff.1 hboth
  refine ⟨Ψ, min ε (1 / 8), h0, h1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hsη
  have hsε : dist s 0 < ε := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
    exact hsη.trans_le (min_le_left _ _)
  obtain ⟨hlo', hup'⟩ := heq hsε
  simp only [Function.comp_apply] at hlo' hup'
  have hexp : Real.exp (c * (Real.log (1 + s) / c)) = 1 + s := by
    rw [mul_div_cancel₀ _ hc, Real.exp_log (by linarith)]
  constructor
  · rw [hlo', hexp]
    ring
  · rw [hup']
    have harg : c * (1 - (1 - Real.log (1 + s) / c)) =
        c * (Real.log (1 + s) / c) := by ring
    rw [harg, hexp]
    ring

end TauCeti
