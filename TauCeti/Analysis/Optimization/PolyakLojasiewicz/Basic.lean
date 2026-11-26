/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.Convex.Strong

/-!
# The Polyak–Łojasiewicz condition

A Polyak–Łojasiewicz inequality bounds the objective gap by the squared norm of the
gradient. For positive modulus it makes stationarity equivalent to global optimality,
even without convexity. Strong convexity implies this inequality by the first-order
lower bound on the objective.

## References

* H. Karimi, J. Nutini and M. Schmidt, *Linear convergence of gradient and
  proximal-gradient methods under the Polyak–Łojasiewicz condition*, §2.3 and Appendix B.
-/

public section

open Set
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : ℝ} {f : E → ℝ}

namespace TauCeti

/-- A lower-bounded objective satisfies the **Polyak–Łojasiewicz condition** with modulus
`μ` if twice `μ` times the gap above its infimum is bounded by its squared gradient norm. -/
structure PolyakLojasiewicz (μ : ℝ) (f : E → ℝ) : Prop where
  /-- The objective has a real lower bound. -/
  bddBelow : BddBelow (range f)
  /-- The gradient controls the objective gap at every point. -/
  le (x : E) : 2 * μ * (f x - ⨅ y, f y) ≤ ‖∇ f x‖ ^ 2

/-- For a positive modulus one can test gradient domination against every comparison
point. The pairwise inequalities themselves supply a lower bound on the objective. -/
theorem polyakLojasiewicz_iff_forall_sub_le (hμ : 0 < μ) :
    PolyakLojasiewicz μ f ↔ ∀ x y, 2 * μ * (f x - f y) ≤ ‖∇ f x‖ ^ 2 := by
  have hpos : 0 < 2 * μ := by positivity
  constructor
  · intro h x y
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (ciInf_le h.bddBelow y) _) hpos.le).trans
      (h.le x)
  · intro h
    have lower (x y : E) : f x - ‖∇ f x‖ ^ 2 / (2 * μ) ≤ f y := by
      have := (le_div_iff₀' hpos).2 (h x y)
      linarith
    refine ⟨⟨_, forall_mem_range.mpr (lower 0)⟩, fun x ↦ ?_⟩
    have := le_ciInf (lower x)
    apply (le_div_iff₀' hpos).1
    linarith

/-- A positive Polyak–Łojasiewicz modulus makes vanishing of the gradient equivalent
to global minimality. -/
theorem PolyakLojasiewicz.gradient_eq_zero_iff_isMinOn (h : PolyakLojasiewicz μ f)
    (hμ : 0 < μ) {x : E} : ∇ f x = 0 ↔ IsMinOn f univ x := by
  constructor
  · intro hx
    refine isMinOn_univ_iff.mpr fun y ↦ ?_
    have hxy := (polyakLojasiewicz_iff_forall_sub_le hμ).mp h x y
    rw [hx, norm_zero, zero_pow two_ne_zero] at hxy
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hxy (by positivity))
  · intro hx
    exact gradient_eq_zero_iff.mpr (hx.isLocalMin Filter.univ_mem).fderiv_eq_zero

end TauCeti

/-- A differentiable strongly convex objective satisfies gradient domination with the
same positive modulus. -/
theorem StrongConvexOn.polyakLojasiewicz (hf : StrongConvexOn univ μ f) (hμ : 0 < μ)
    (hd : Differentiable ℝ f) : TauCeti.PolyakLojasiewicz μ f := by
  refine (TauCeti.polyakLojasiewicz_iff_forall_sub_le hμ).mpr fun x y ↦ ?_
  rw [TauCeti.norm_gradient_eq_norm_fderiv]
  exact hf.mul_sub_le_norm_sq_of_hasFDerivWithinAt hμ.le (mem_univ x) (mem_univ y)
    (hd x).hasFDerivAt.hasFDerivWithinAt
