/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Derivatives of functions of temperate growth

A smooth function whose iterated derivatives are all bounded has temperate growth. Typical examples
are smooth functions which outside a ball agree with a homogeneous function of degree at most `0`.
So does a smooth function satisfying symbol estimates
`‖D^k f(x)‖ ≤ C_k (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)` of some real order `m`, and the rescaled
Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r`.

The derivative `Df` of a function `f` of temperate growth has temperate growth, since the iterated
derivatives of `Df` are those of `f` shifted by one order. So does each directional derivative
`x ↦ Df(x) v`. These are the coefficients that appear when the Leibniz rule is applied to the
product of a Schwartz function or a tempered distribution with `f`.

## Main results

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: bounded derivatives give temperate
  growth.
* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow`: symbol estimates
  give temperate growth.
* `Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow`: the rescaled Bessel potential has
  temperate growth.
* `Function.HasTemperateGrowth.fderiv`: `Df` has temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: `x ↦ Df(x) v` has temperate growth.
-/

public section

open scoped ContDiff

namespace Function.HasTemperateGrowth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F}

/-- A smooth function all of whose iterated derivatives are bounded has temperate growth. -/
theorem of_norm_iteratedFDeriv_le (hf : ContDiff ℝ ∞ f)
    (hbd : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : f.HasTemperateGrowth :=
  ⟨hf, fun n ↦ ⟨0, (hbd n).imp fun C hC x ↦ by simpa using hC x⟩⟩

/-- **Symbol estimates give temperate growth.** A smooth function whose `k`-th derivative is
bounded by `C_k (1 + ‖x‖²) ^ ((m - k) / 2)` for every `k` has temperate growth. -/
theorem of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow {m : ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ k : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)) :
    f.HasTemperateGrowth := by
  refine ⟨hf, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbound k
  refine ⟨⌈m⌉₊, max C 0, fun x ↦ (hC x).trans ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hw : (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖) ^ ⌈m⌉₊ :=
    calc (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖ ^ 2) ^ ((⌈m⌉₊ : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by
            have := Nat.le_ceil m
            have : (0 : ℝ) ≤ k := k.cast_nonneg
            linarith)
      _ ≤ (1 + ‖x‖) ^ (⌈m⌉₊ : ℝ) :=
          TauCeti.one_add_norm_sq_rpow_half_le_one_add_norm_rpow x (Nat.cast_nonneg _)
      _ = (1 + ‖x‖) ^ ⌈m⌉₊ := Real.rpow_natCast _ _
  calc C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ max C 0 * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + ‖x‖) ^ ⌈m⌉₊ := mul_le_mul_of_nonneg_left hw (le_max_right _ _)

/-- The derivative of a function of temperate growth has temperate growth. -/
theorem fderiv (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right le_rfl, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x ↦ by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩

/-- A directional derivative `x ↦ Df(x) v` of a function of temperate growth has temperate
growth. -/
theorem fderiv_apply (hf : f.HasTemperateGrowth) (v : E) :
    (fun x ↦ _root_.fderiv ℝ f x v).HasTemperateGrowth :=
  (ContinuousLinearMap.apply ℝ F v).hasTemperateGrowth.comp hf.fderiv

end Function.HasTemperateGrowth

namespace Function

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The rescaled Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_one_add_norm_smul_sq_rpow (c r : ℝ) :
    (fun x : H ↦ (1 + ‖c • x‖ ^ 2) ^ r).HasTemperateGrowth :=
  (hasTemperateGrowth_one_add_norm_sq_rpow H r).comp (by fun_prop)

end Function
