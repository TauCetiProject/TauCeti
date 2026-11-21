/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Pi

/-!
# Basic properties of real Brownian motion

Complements Mathlib's `Mathlib.Probability.BrownianMotion.Basic` with basic unfiltered
properties and closure properties of standard real pre-Brownian and Brownian motions:

* any measure supporting a pre-Brownian motion assigns zero mass to every singleton
  (`MeasureTheory.NullSingletonClass`), since evaluation at time `1` has the nondegenerate
  Gaussian law `gaussianReal 0 1`;
* every even moment `(B s - B t) ^ (2 * m)` of a pre-Brownian increment equals
  `(2 * m - 1)‼ * dist s t ^ m`, regardless of the order of `s` and `t`;
* orthogonal linear combinations `t ↦ a * B₁ t + b * B₂ t` (`a ^ 2 + b ^ 2 = 1`) of two
  independent real pre-Brownian or Brownian motions are again pre-Brownian and Brownian.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.nullSingletonClass`: any measure supporting a pre-Brownian
  motion assigns zero mass to singletons.
* `ProbabilityTheory.IsPreBrownianReal.integral_pow_two_mul_sub`: even moments of pre-Brownian
  increments in either time order.
* `ProbabilityTheory.IsPreBrownianReal.const_mul_add_const_mul_of_indepFun`: orthogonal linear
  combinations of independent pre-Brownian motions are pre-Brownian.
* `ProbabilityTheory.IsBrownianReal.const_mul_add_const_mul_of_indepFun`: orthogonal linear
  combinations of independent Brownian motions are Brownian.
-/

public section

open MeasureTheory
open scoped Nat NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Any measure supporting a pre-Brownian motion assigns zero mass to every single sample point. -/
theorem IsPreBrownianReal.nullSingletonClass {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    NullSingletonClass P where
  measure_singleton ω := by
    have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
    exact (hB.hasLaw_eval 1).measure_singleton_eq_zero ω

/-- Every even moment `(B s - B t) ^ (2 m)` of a pre-Brownian increment equals
`(2 m - 1)‼ * dist s t ^ m`, regardless of the order of `s` and `t`. -/
theorem IsPreBrownianReal.integral_pow_two_mul_sub {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (m : ℕ) :
    ∫ ω, (B s ω - B t ω) ^ (2 * m) ∂P = (2 * m - 1 : ℕ)‼ * dist s t ^ m := by
  have h := (hB.hasLaw_sub s t).integral_comp (f := fun x : ℝ ↦ x ^ (2 * m)) (by fun_prop)
  have hm := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 (nndist s t) m
  simp only [sub_zero, coe_nndist] at hm
  simpa only [Function.comp_apply, Pi.sub_apply, mul_comm] using h.trans hm

/-- An orthogonal linear combination `t ↦ a * B₁ t + b * B₂ t` (`a ^ 2 + b ^ 2 = 1`) of two
independent real pre-Brownian motions is a real pre-Brownian motion. -/
theorem IsPreBrownianReal.const_mul_add_const_mul_of_indepFun {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsPreBrownianReal B₁ P) (hB₂ : IsPreBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    IsPreBrownianReal (fun t ω ↦ a * B₁ t ω + b * B₂ t ω) P := by
  have : IsProbabilityMeasure P := (hB₁.hasLaw_eval 0).isProbabilityMeasure
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ ?_) (fun n g hg ↦ ?_)
  · have h1 := gaussianReal_const_mul (hB₁.hasLaw_eval t) a
    have h2 := gaussianReal_const_mul (hB₂.hasLaw_eval t) b
    have hvar : NNReal.mk (a ^ 2) (sq_nonneg a) * t + NNReal.mk (b ^ 2) (sq_nonneg b) * t = t := by
      ext; push_cast; rw [← add_mul, hab, one_mul]
    refine ⟨h1.aemeasurable.add h2.aemeasurable, by
      simpa only [Pi.add_def, Pi.mul_apply, mul_zero, add_zero, Function.comp_def, hvar] using
        gaussianReal_add_gaussianReal_of_indepFun (hind.comp
          (measurable_const.mul (measurable_pi_apply t))
          (measurable_const.mul (measurable_pi_apply t))) h1 h2⟩
  · let Δ (c : Bool) (k : Fin n) (ω : Ω) : ℝ :=
      _root_.cond c (B₂ (g k.succ) ω - B₂ (g k.castSucc) ω) (B₁ (g k.succ) ω - B₁ (g k.castSucc) ω)
    have hm : Measurable (fun (f : ℝ≥0 → ℝ) (k : Fin n) ↦ f (g k.succ) - f (g k.castSucc)) :=
      measurable_pi_iff.2 fun _ ↦ (measurable_pi_apply _).sub (measurable_pi_apply _)
    have hbool : iIndepFun (fun c ω k ↦ Δ c k ω) P := (iIndepFun_iff _ _ _).2 fun s f hf ↦ by
      rcases (by decide : ∀ s : Finset Bool, (s = ∅ ∨ s = {false} ∨ s = {true}) ∨
          s = {false, true}) s with h | rfl
      · rcases h with rfl | rfl | rfl <;> simp
      · rw [Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_pair (by decide)]
        exact (Indep_iff ..).1 ((IndepFun_iff_Indep ..).1 (hind.comp hm hm)) _ _
          (hf false (by simp)) (hf true (by simp))
    convert (iIndepFun.swap (X := Δ) hbool
      (fun | false => hB₁.hasIndepIncrements n g hg | true => hB₂.hasIndepIncrements n g hg)
      (fun | false, _ => (hB₁.hasLaw_eval _).aemeasurable.sub (hB₁.hasLaw_eval _).aemeasurable
           | true, _ => (hB₂.hasLaw_eval _).aemeasurable.sub (hB₂.hasLaw_eval _).aemeasurable)
      ).comp (fun _ (f : Bool → ℝ) ↦ a * f false + b * f true) (fun _ ↦ by fun_prop) using 1
    ext _ _; simp only [Δ, Function.comp_apply, Bool.cond_false, Bool.cond_true]; ring

/-- An orthogonal linear combination `t ↦ a * B₁ t + b * B₂ t` (`a ^ 2 + b ^ 2 = 1`) of two
independent real Brownian motions is a real Brownian motion. -/
theorem IsBrownianReal.const_mul_add_const_mul_of_indepFun {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsBrownianReal B₁ P) (hB₂ : IsBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    IsBrownianReal (fun t ω ↦ a * B₁ t ω + b * B₂ t ω) P :=
  ⟨hB₁.toIsPreBrownianReal.const_mul_add_const_mul_of_indepFun hB₂.toIsPreBrownianReal hind hab,
    hB₁.cont.mp (hB₂.cont.mono fun _ h₂ h₁ ↦
      (continuous_const.mul h₁).add (continuous_const.mul h₂))⟩

end ProbabilityTheory
