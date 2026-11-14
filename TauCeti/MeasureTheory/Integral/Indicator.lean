/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals of expressions in an extension by zero

Let `h x v` be an expression in a point `x` and a value `v` which vanishes at `v = 0`. Then
`h x (1_s g x)`, where `1_s g` is the extension of `g` by zero from a measurable set `s`, is the
extension by zero of `h x (g x)`. So its integral over the whole space is the integral of
`h x (g x)` over `s`. This is how a quantity such as `∫ ‖1_Ω ∇u‖ ^ p` over the whole space, for the
extension by zero of a gradient on a domain `Ω`, becomes the integral `∫_Ω ‖∇u‖ ^ p`.

## Main statements

* `TauCeti.integral_comp_indicator`: `∫ h x (1_s g x) = ∫_s h x (g x)` for the Bochner integral.
* `TauCeti.lintegral_comp_indicator`: the same identity for the Lebesgue integral.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α} [Zero V] {s : Set α}

/-- The Bochner integral over the whole space of an expression `h x v`, vanishing at `v = 0`, in
the extension by zero of `g` from `s` is the integral of `h x (g x)` over `s`. -/
theorem integral_comp_indicator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hs : MeasurableSet s) (h : α → V → E) (h0 : ∀ x, h x 0 = 0) (g : α → V) :
    ∫ x, h x (s.indicator g x) ∂μ = ∫ x in s, h x (g x) ∂μ := by
  rw [← integral_indicator hs]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx, h0]

/-- The Lebesgue integral over the whole space of an expression `h x v`, vanishing at `v = 0`, in
the extension by zero of `g` from `s` is the integral of `h x (g x)` over `s`. -/
theorem lintegral_comp_indicator (hs : MeasurableSet s) (h : α → V → ℝ≥0∞)
    (h0 : ∀ x, h x 0 = 0) (g : α → V) :
    ∫⁻ x, h x (s.indicator g x) ∂μ = ∫⁻ x in s, h x (g x) ∂μ := by
  rw [← lintegral_indicator hs]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx, h0]

end TauCeti
