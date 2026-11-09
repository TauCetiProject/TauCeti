/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# The modular `√(1 + f²) - 1` on real `L²`

The modular `√(1 + t²) - 1` is comparable to `t²` for small `t` and grows only linearly for large
`t`. This file shows that its integral is finite and continuous on real `L²` over an arbitrary
measure space.

## Main results

* `MeasureTheory.MemLp.integrable_sqrt_one_add_sq_sub_one`: the modular of a square-integrable
  function is integrable.
* `MeasureTheory.Lp.integrable_abs_mul_abs`: for `f` and `g` in real `L²`, `|f| |g|` is
  integrable.
* `MeasureTheory.Lp.abs_setIntegral_sqrt_one_add_sq_sub_le`: the modular is locally Lipschitz on
  `L²`, `|∫_t (√(1 + f²) - 1) - ∫_t (√(1 + g²) - 1)| ≤ ‖f - g‖ (‖f‖ + ‖g‖)`.
* `MeasureTheory.continuous_setIntegral_sqrt_one_add_sq_sub_one`: the modular
  `∫_t (√(1 + f²) - 1)` is continuous on `L²`.
-/

public section

noncomputable section

namespace MeasureTheory

open Filter

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- The modular `√(1 + f²) - 1` of a square-integrable function is integrable. -/
theorem MemLp.integrable_sqrt_one_add_sq_sub_one {f : α → ℝ} (hf : MemLp f 2 ν) :
    Integrable (fun x ↦ √(1 + f x ^ 2) - 1) ν := by
  have hf2 : Integrable (fun x ↦ f x ^ 2 / 2) ν :=
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf).div_const 2
  refine hf2.mono' ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact (hf.aestronglyMeasurable.aemeasurable.pow_const 2 |>.const_add 1
      |>.sqrt.sub_const 1).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (Real.one_le_sqrt_one_add_sq _))]
    exact Real.sqrt_one_add_sq_sub_one_le_sq_div_two _

/-- For `f` and `g` in real `L²`, the product `|f| |g|` is integrable. -/
theorem Lp.integrable_abs_mul_abs (f g : Lp ℝ 2 ν) : Integrable (fun x ↦ |f x| * |g x|) ν := by
  simpa only [Real.norm_eq_abs, Pi.mul_def] using
    (Lp.memLp f).norm.integrable_mul (Lp.memLp g).norm

/-- The modular is locally Lipschitz on `L²`:
`|∫_t (√(1 + f²) - 1) - ∫_t (√(1 + g²) - 1)| ≤ ‖f - g‖ (‖f‖ + ‖g‖)`. -/
theorem Lp.abs_setIntegral_sqrt_one_add_sq_sub_le (f g : Lp ℝ 2 ν) (t : Set α) :
    |∫ x in t, (√(1 + f x ^ 2) - 1) ∂ν - ∫ x in t, (√(1 + g x ^ 2) - 1) ∂ν| ≤
      ‖f - g‖ * (‖f‖ + ‖g‖) := by
  have hfi := (Lp.memLp f).integrable_sqrt_one_add_sq_sub_one
  have hgi := (Lp.memLp g).integrable_sqrt_one_add_sq_sub_one
  have hk : Integrable (fun x ↦ |(f - g) x| * |f x| + |(f - g) x| * |g x|) ν :=
    (Lp.integrable_abs_mul_abs (f - g) f).add (Lp.integrable_abs_mul_abs (f - g) g)
  rw [← integral_sub hfi.integrableOn hgi.integrableOn]
  calc |∫ x in t, ((√(1 + f x ^ 2) - 1) - (√(1 + g x ^ 2) - 1)) ∂ν|
      ≤ ∫ x in t, |(√(1 + f x ^ 2) - 1) - (√(1 + g x ^ 2) - 1)| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in t, (|(f - g) x| * |f x| + |(f - g) x| * |g x|) ∂ν := by
        refine setIntegral_mono_ae (hfi.sub hgi).abs.integrableOn hk.integrableOn ?_
        filter_upwards [Lp.coeFn_sub f g] with x hx
        have := Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le (f x) (g x)
        rw [hx, Pi.sub_apply]
        have h0 : 0 ≤ |f x - g x| * (|f x| + |g x|) := by positivity
        rw [sub_sub_sub_cancel_right]
        nlinarith
    _ ≤ ∫ x, (|(f - g) x| * |f x| + |(f - g) x| * |g x|) ∂ν :=
        setIntegral_le_integral hk (Eventually.of_forall fun x ↦ by positivity)
    _ ≤ ‖f - g‖ * ‖f‖ + ‖f - g‖ * ‖g‖ := by
        rw [integral_add (Lp.integrable_abs_mul_abs (f - g) f)
          (Lp.integrable_abs_mul_abs (f - g) g)]
        exact add_le_add (Lp.integral_abs_mul_abs_le_norm_mul_norm (f - g) f)
          (Lp.integral_abs_mul_abs_le_norm_mul_norm (f - g) g)
    _ = ‖f - g‖ * (‖f‖ + ‖g‖) := by ring

/-- The modular `∫_t (√(1 + f²) - 1)` is continuous on `L²`. -/
theorem continuous_setIntegral_sqrt_one_add_sq_sub_one (t : Set α) :
    Continuous fun f : Lp ℝ 2 ν ↦ ∫ x in t, (√(1 + f x ^ 2) - 1) ∂ν := by
  refine continuous_iff_continuousAt.2 fun f₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun f ↦ ?_) (?_ : Tendsto
    (fun f : Lp ℝ 2 ν ↦ ‖f - f₀‖ * (‖f‖ + ‖f₀‖)) (nhds f₀) (nhds 0))
  · rw [Real.dist_eq]
    exact Lp.abs_setIntegral_sqrt_one_add_sq_sub_le f f₀ t
  · have : Continuous fun f : Lp ℝ 2 ν ↦ ‖f - f₀‖ * (‖f‖ + ‖f₀‖) := by fun_prop
    simpa using this.tendsto f₀

end MeasureTheory
