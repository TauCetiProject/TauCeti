/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.SimpleFunc.Basic

/-!
# Fibre decompositions of simple functions in `Lᵖ`

A simple function `f` is the sum of its fibre pieces, the constants `c` restricted to the fibres
`f ⁻¹' {c}` (`MeasureTheory.SimpleFunc.eq_sum_restrict_const`). If each piece is represented by an
element `u c` of `Lᵖ`, then a combination `∑ c, a c • u c` with coefficients depending on the
value is the class of `x ↦ a (f x) • f x` (`MeasureTheory.Lp.coeFn_sum_smul_restrict_const`). This
is how an analytic family built from the fibres of a simple function, as in the complex
interpolation of the Lebesgue couple, is evaluated pointwise.

An element of `Lp.simpleFunc E p μ` with `0 < p < ∞` has fibres of finite measure, so it lies in
`L^q` for every exponent `q` (`MeasureTheory.Lp.simpleFunc.memLp_of_ne_zero_of_ne_top`).
-/

public section

open Filter
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- A combination of `Lᵖ` representatives `u c` of the fibre pieces of `f`, with coefficients
`a c` depending on the value, is the class of the weighted function `x ↦ a (f x) • f x`. -/
theorem coeFn_sum_smul_restrict_const (f : SimpleFunc α E) (a : E → 𝕜) (u : E → Lp E p μ)
    (hu : ∀ c, ⇑(u c) =ᵐ[μ] (SimpleFunc.const α c).restrict (f ⁻¹' {c})) :
    ⇑(∑ c ∈ f.range, a c • u c) =ᵐ[μ] fun x => a (f x) • f x := by
  have h : ∀ᵐ x ∂μ, ∀ c ∈ f.range,
      (a c • u c) x = a c • (SimpleFunc.const α c).restrict (f ⁻¹' {c}) x :=
    (eventually_all_finset f.range).2 fun c _ => by
      filter_upwards [coeFn_smul (a c) (u c), hu c] with x h₁ h₂
      rw [h₁, Pi.smul_apply, h₂]
  filter_upwards [coeFn_finsetSum f.range (fun c => a c • u c), h] with x hx hx'
  rw [hx, Finset.sum_apply, ← SimpleFunc.sum_smul_restrict_const_apply f a x]
  exact Finset.sum_congr rfl hx'

/-- A simple function of `Lᵖ` with `0 < p < ∞` has fibres of finite measure, so it lies in `L^q`
for every exponent `q`. -/
theorem simpleFunc.memLp_of_ne_zero_of_ne_top (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp.simpleFunc E p μ) (q : ℝ≥0∞) : MemLp (f : α → E) q μ :=
  (SimpleFunc.memLp_of_finite_measure_preimage q
    (SimpleFunc.measure_preimage_lt_top_of_memLp hp₀ hp _ (Lp.simpleFunc.memLp f))).ae_eq
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f)

end MeasureTheory.Lp
