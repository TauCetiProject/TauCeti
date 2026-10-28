/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
-- Proof-only: convexity of powers of a nonnegative convex function.
import Mathlib.Analysis.Convex.Mul

/-!
# Log-concave functions

A function `f : E → ℝ≥0∞` on a real vector space is *log-concave* if
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` whenever `0 ≤ a`, `0 ≤ b` and `a + b = 1`. For a
positive real-valued function this says exactly that its logarithm is concave
(`TauCeti.logConcave_ofReal_exp_iff`), while the value `0` allowed by `ℝ≥0∞` makes the indicator
of a convex set log-concave.

Taking values in `ℝ≥0∞` is what makes the notion stable under integration: the marginal
`x ↦ ∫⁻ y, f (x, y) ∂ν` of a log-concave function is log-concave whenever `ν` satisfies the
Prékopa–Leindler inequality, with no finiteness hypothesis on the integrals
(`TauCeti.LogConcave.lintegral_prod_right`, in
`TauCeti.MeasureTheory.Integral.PrekopaLeindler`). Marginals of this kind are the measures of
the slices of a convex body, and are the objects of Vaaler's cube-slicing theorem.

## Main definitions

* `TauCeti.LogConcave f`: the function `f : E → ℝ≥0∞` is log-concave.

## Main results

* `TauCeti.logConcave_ofReal_exp_iff`: `x ↦ exp (g x)` is log-concave if and only if `g` is
  concave.
* `TauCeti.logConcave_ofReal_exp_neg_mul_sq_norm`: the Gaussian `x ↦ exp (-c ‖x‖ ^ 2)` is
  log-concave.
* `TauCeti.logConcave_indicator_iff`: the indicator of a set at a nonzero value is log-concave if
  and only if the set is convex.
* `TauCeti.LogConcave.convex_support`, `TauCeti.LogConcave.convex_ge`,
  `TauCeti.LogConcave.convex_gt`: the support and the superlevel sets of a log-concave function
  are convex.
* `TauCeti.LogConcave.mul`, `TauCeti.LogConcave.comp_linearMap`: products and linear
  substitutions preserve log-concavity.
* `TauCeti.LogConcave.apply_le_apply_zero`: an even log-concave function is largest at the
  origin.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Definition C.3.1 and Remark C.3.2.

The definition and the convexity statements are adapted from the Apache-2.0 formalization of
Vaaler's theorem in `rwst/Subspace-Theorems` (file `ArithmeticHeights/LogConcave.lean`), by
Ralf Stephan.
-/

public section

open Set
open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- A function `f : E → ℝ≥0∞` on a real vector space is **log-concave** if
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` for all `x`, `y` and all weights `0 ≤ a`, `0 ≤ b` with
`a + b = 1`. For positive real-valued `f` this says that `Real.log ∘ f` is concave. -/
def LogConcave (f : E → ℝ≥0∞) : Prop :=
  ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f x ^ a * f y ^ b ≤ f (a • x + b • y)

theorem logConcave_def {f : E → ℝ≥0∞} :
    LogConcave f ↔ ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f x ^ a * f y ^ b ≤ f (a • x + b • y) :=
  Iff.rfl

namespace LogConcave

variable {f g : E → ℝ≥0∞}

/-- The defining inequality of a log-concave function. -/
theorem rpow_mul_rpow_le (hf : LogConcave f) {x y : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : f x ^ a * f y ^ b ≤ f (a • x + b • y) :=
  hf ha hb hab

/-- The minimum of two values of a log-concave function is at most its value at any convex
combination of the two points. -/
theorem ge_on_segment' (hf : LogConcave f) {x y : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) := by
  calc min (f x) (f y) = min (f x) (f y) ^ a * min (f x) (f y) ^ b := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]
    _ ≤ f x ^ a * f y ^ b := by gcongr <;> simp
    _ ≤ f (a • x + b • y) := hf ha hb hab

/-- **Every superlevel set of a log-concave function is convex.** -/
theorem convex_ge (hf : LogConcave f) (r : ℝ≥0∞) : Convex ℝ {x | r ≤ f x} :=
  fun _ hx _ hy _ _ ha hb hab ↦ (le_min hx hy).trans (hf.ge_on_segment' ha hb hab)

/-- **Every strict superlevel set of a log-concave function is convex.** -/
theorem convex_gt (hf : LogConcave f) (r : ℝ≥0∞) : Convex ℝ {x | r < f x} :=
  fun _ hx _ hy _ _ ha hb hab ↦ (lt_min hx hy).trans_le (hf.ge_on_segment' ha hb hab)

/-- **The support of a log-concave function is convex** (Bombieri–Gubler, Remark C.3.2). -/
theorem convex_support (hf : LogConcave f) : Convex ℝ (Function.support f) := by
  simpa only [Function.support, pos_iff_ne_zero] using hf.convex_gt 0

/-- A product of log-concave functions is log-concave. -/
protected theorem mul (hf : LogConcave f) (hg : LogConcave g) : LogConcave (f * g) := by
  intro x y a b ha hb hab
  simp only [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.mul_rpow_of_nonneg _ _ hb]
  calc f x ^ a * g x ^ a * (f y ^ b * g y ^ b) = f x ^ a * f y ^ b * (g x ^ a * g y ^ b) := by
        ring
    _ ≤ f (a • x + b • y) * g (a • x + b • y) := mul_le_mul' (hf ha hb hab) (hg ha hb hab)

/-- Composing a log-concave function with a linear map gives a log-concave function. -/
theorem comp_linearMap (hf : LogConcave f) (L : F →ₗ[ℝ] E) : LogConcave (f ∘ L) := by
  intro x y a b ha hb hab
  simpa only [Function.comp_apply, map_add, map_smul] using hf (x := L x) (y := L y) ha hb hab

/-- **An even log-concave function is largest at the origin.** Applied to the measures of the
parallel slices of a symmetric convex body, this says that the central slice is the largest. -/
theorem apply_le_apply_zero {G : Type*} [AddCommGroup G] [Module ℝ G] {f : G → ℝ≥0∞}
    (hf : LogConcave f) (hfe : f.Even) (x : G) : f x ≤ f 0 := by
  have h := hf.ge_on_segment' (x := x) (y := -x) (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [hfe x, min_self, show (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • -x = 0 by module] at h

end LogConcave

/-- A constant function is log-concave. -/
theorem logConcave_const (c : ℝ≥0∞) : LogConcave fun _ : E ↦ c := fun _ _ _ _ ha hb hab ↦ by
  rw [← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]

/-- The indicator of a convex set is log-concave, at any value. -/
theorem _root_.Convex.logConcave_indicator {s : Set E} (hs : Convex ℝ s) (c : ℝ≥0∞) :
    LogConcave (s.indicator fun _ ↦ c) := by
  intro x y a b ha hb hab
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem (hs hx hy ha hb hab),
        ← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]
    · rcases hb.eq_or_lt with rfl | hb
      · simp_all
      · simp [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
  · rcases ha.eq_or_lt with rfl | ha
    · simp_all
    · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

/-- The indicator of a set at a nonzero value is log-concave if and only if the set is convex. -/
theorem logConcave_indicator_iff {s : Set E} {c : ℝ≥0∞} (hc : c ≠ 0) :
    LogConcave (s.indicator fun _ ↦ c) ↔ Convex ℝ s :=
  ⟨fun h ↦ by simpa [Function.support_const hc] using h.convex_support,
    fun hs ↦ hs.logConcave_indicator c⟩

/-- A function `x ↦ exp (g x)` is log-concave if and only if `g` is concave. -/
theorem logConcave_ofReal_exp_iff {g : E → ℝ} :
    LogConcave (fun x ↦ ENNReal.ofReal (Real.exp (g x))) ↔ ConcaveOn ℝ univ g := by
  have key (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
      ENNReal.ofReal (Real.exp (g x)) ^ a * ENNReal.ofReal (Real.exp (g y)) ^ b =
        ENNReal.ofReal (Real.exp (a * g x + b * g y)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ha,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hb, ← Real.exp_mul, ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_comm (g x), mul_comm (g y)]
  refine ⟨fun h ↦ ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩,
    fun h x y a b ha hb hab ↦ ?_⟩
  · have := h (x := x) (y := y) ha hb hab
    rw [key x y ha hb, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp] at this
    simpa only [smul_eq_mul] using this
  · rw [key x y ha hb]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (h.2 trivial trivial ha hb hab))

/-- The Gaussian `x ↦ exp (-c ‖x‖ ^ 2)` on a real normed space is log-concave for `0 ≤ c`. -/
theorem logConcave_ofReal_exp_neg_mul_sq_norm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace ℝ G] {c : ℝ} (hc : 0 ≤ c) :
    LogConcave fun x : G ↦ ENNReal.ofReal (Real.exp (-c * ‖x‖ ^ 2)) := by
  refine logConcave_ofReal_exp_iff.2 ?_
  have h := ((convexOn_norm (convex_univ (𝕜 := ℝ) (E := G))).pow
    (fun x _ ↦ norm_nonneg x) 2).neg.smul hc
  convert h using 2 with x
  simp [neg_mul, smul_eq_mul]

end TauCeti
