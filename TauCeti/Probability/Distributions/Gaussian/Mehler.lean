/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.Distributions.Gaussian.Affine
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gaussian Mehler averaging

The one-dimensional Mehler averaging operator preserves standard Gaussian measure. It is
positive and preserves constants and uniform bounds. For bounded continuous functions it
converges pointwise to the function at time zero and to its Gaussian mean at large times.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace TauCeti.Probability

/-- Mehler averaging with the standard Gaussian law. The intended time domain is `t ≥ 0`. -/
def mehler (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
    ∂(gaussianReal 0 1)

/-- The defining Gaussian integral for Mehler averaging. -/
theorem mehler_def (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mehler t f x =
      ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
        ∂(gaussianReal 0 1) := (rfl)

/-- Mehler averaging leaves constants unchanged. -/
@[simp] theorem mehler_const (t c x : ℝ) : mehler t (fun _ ↦ c) x = c := by
  simp [mehler]

/-- Mehler averaging preserves nonnegativity. -/
theorem mehler_nonneg (t : ℝ) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ mehler t f x := integral_nonneg fun _y ↦ hf _

/-- Mehler averaging preserves a uniform bound. -/
theorem norm_mehler_le (t : ℝ) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ C) (x : ℝ) : ‖mehler t f x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const
    (μ := gaussianReal 0 1) (f := fun y ↦ f (Real.exp (-t) * x +
      Real.sqrt (1 - Real.exp (-2 * t)) * y)) (Filter.Eventually.of_forall fun y ↦ hf _)
  simpa [mehler] using h

/-- A bounded measurable function is integrable against every Mehler kernel. -/
theorem integrable_mehler_section (t x : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    Integrable (fun y ↦ f (Real.exp (-t) * x +
      Real.sqrt (1 - Real.exp (-2 * t)) * y)) (gaussianReal 0 1) := by
  apply (integrable_const C).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ hC _

/-- Mehler averaging is linear whenever the two kernel sections are integrable. -/
theorem mehler_add (t x : ℝ) {f g : ℝ → ℝ}
    (hf : Integrable (fun y ↦ f (Real.exp (-t) * x +
      Real.sqrt (1 - Real.exp (-2 * t)) * y)) (gaussianReal 0 1))
    (hg : Integrable (fun y ↦ g (Real.exp (-t) * x +
      Real.sqrt (1 - Real.exp (-2 * t)) * y)) (gaussianReal 0 1)) :
    mehler t (fun z ↦ f z + g z) x = mehler t f x + mehler t g x := by
  exact integral_add hf hg

/-- Mehler averaging commutes with scalar multiplication. -/
theorem mehler_const_mul (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mehler t (fun z ↦ c * f z) x = c * mehler t f x := by
  exact integral_const_mul _ _

/-- At time zero Mehler averaging is the identity. -/
@[simp] theorem mehler_zero (f : ℝ → ℝ) (x : ℝ) : mehler 0 f x = f x := by
  simp [mehler]

/-- The identity function is an eigenfunction of Mehler averaging. -/
theorem mehler_id (t x : ℝ) : mehler t id x = Real.exp (-t) * x := by
  have hi : Integrable (fun y : ℝ ↦ y) (gaussianReal 0 1) :=
    integrable_of_mem_interior_integrableExpSet (by simp)
  rw [mehler]
  simp only [id_eq]
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const,
    integral_const_mul, integral_id_gaussianReal]
  simp

/-- The Mehler kernel preserves standard Gaussian measure. -/
theorem gaussianReal_map_mehler (t : ℝ) (ht : 0 ≤ t) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ ↦ Real.exp (-t) * p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) * p.2) = gaussianReal 0 1 := by
  apply gaussianReal_map_linear_combination
  have hnonneg : 0 ≤ 1 - Real.exp (-2 * t) := by
    have ht' : -2 * t ≤ 0 := by linarith
    have h := Real.exp_le_one_iff.mpr ht'
    linarith
  rw [Real.sq_sqrt hnonneg, pow_two, ← Real.exp_add]
  have h : -t + -t = -2 * t := by ring
  rw [h]
  ring

/-- Mehler averaging preserves integrability under the standard Gaussian law. -/
theorem integrable_mehler (t : ℝ) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (mehler t f) (gaussianReal 0 1) := by
  let T : ℝ × ℝ → ℝ := fun p ↦ Real.exp (-t) * p.1 +
    Real.sqrt (1 - Real.exp (-2 * t)) * p.2
  have hT : Measurable T := by fun_prop
  have hmap : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map T = gaussianReal 0 1 :=
    gaussianReal_map_mehler t ht
  have hi : Integrable (f ∘ T) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have hf' : Integrable f (((gaussianReal 0 1).prod (gaussianReal 0 1)).map T) := by
      rwa [hmap]
    exact hf'.comp_measurable hT
  have heq : mehler t f = fun x ↦ ∫ y, f (T (x, y)) ∂(gaussianReal 0 1) := by
    funext x
    exact mehler_def t f x
  rw [heq]
  exact hi.integral_prod_left

/-- Integration against the standard Gaussian is unchanged by Mehler averaging. -/
theorem integral_mehler (t : ℝ) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    (∫ x, mehler t f x ∂(gaussianReal 0 1)) =
      ∫ x, f x ∂(gaussianReal 0 1) := by
  let T : ℝ × ℝ → ℝ := fun p ↦ Real.exp (-t) * p.1 +
    Real.sqrt (1 - Real.exp (-2 * t)) * p.2
  have hT : Measurable T := by fun_prop
  have hmap : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map T = gaussianReal 0 1 :=
    gaussianReal_map_mehler t ht
  have hi : Integrable (f ∘ T) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have hf' : Integrable f (((gaussianReal 0 1).prod (gaussianReal 0 1)).map T) := by
      rwa [hmap]
    exact hf'.comp_measurable hT
  calc
    _ = ∫ p, f (T p) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      exact (integral_prod (f ∘ T) hi).symm
    _ = ∫ x, f x ∂((gaussianReal 0 1).prod (gaussianReal 0 1)).map T :=
      (integral_map hT.aemeasurable (by rw [hmap]; exact hf.aestronglyMeasurable)).symm
    _ = _ := by rw [hmap]

private theorem tendsto_mehler_of_coefficients {ι : Type*} (l : Filter ι)
    [l.IsCountablyGenerated] (s : ι → ℝ) (a b : ℝ)
    (ha : Tendsto (fun i ↦ Real.exp (-s i)) l (𝓝 a))
    (hb : Tendsto (fun i ↦ Real.sqrt (1 - Real.exp (-2 * s i))) l (𝓝 b))
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    Tendsto (fun i ↦ mehler (s i) f x) l
      (𝓝 (∫ y, f (a * x + b * y) ∂(gaussianReal 0 1))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
  · filter_upwards with i
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with i
    filter_upwards with y
    exact hC _
  · exact integrable_const C
  · filter_upwards with y
    exact hf.continuousAt.tendsto.comp ((ha.mul_const x).add (hb.mul_const y))

/-- Mehler averaging tends pointwise to the identity as time tends to zero. -/
theorem tendsto_mehler_zero {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    Tendsto (fun t ↦ mehler t f x) (𝓝 0) (𝓝 (f x)) := by
  have ha : Tendsto (fun t : ℝ ↦ Real.exp (-t)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ ↦ Real.exp (-t)) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  have hb : Tendsto (fun t : ℝ ↦ Real.sqrt (1 - Real.exp (-2 * t))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ Real.sqrt (1 - Real.exp (-2 * t))) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  simpa using tendsto_mehler_of_coefficients (𝓝 0) id 1 0 ha hb hf hC x

/-- Mehler averaging converges pointwise to the Gaussian mean at large times. -/
theorem tendsto_mehler_atTop {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    Tendsto (fun t ↦ mehler t f x) atTop (𝓝 (∫ y, f y ∂(gaussianReal 0 1))) := by
  have ha : Tendsto (fun t : ℝ ↦ Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have he : Tendsto (fun t : ℝ ↦ Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have hb : Tendsto (fun t : ℝ ↦ Real.sqrt (1 - Real.exp (-2 * t))) atTop (𝓝 1) := by
    have hs : Tendsto (fun t : ℝ ↦ 1 - Real.exp (-2 * t)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub he
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa using tendsto_mehler_of_coefficients atTop id 0 1 ha hb hf hC x

end TauCeti.Probability
