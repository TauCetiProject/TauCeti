/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.RegularValue

/-!
# Gradients at regular points and regular values

At a regular point `x` of a function `f : M → ℝ`, the derivative of `f` along its Riemannian
gradient is `df_x(grad f x) = |grad f x|² > 0`
(`TauCeti.IsRegularPoint.mvfderiv_apply_mgradient_pos`): `f` strictly increases along its gradient
there. Every scalar value is regular for a function with unit Riemannian gradient
(`TauCeti.Manifold.isRegularValue_of_unit_mgradient`).
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

section Level

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)] {f : M → ℝ}

/-- A unit gradient makes every scalar value regular. -/
theorem isRegularValue_of_unit_mgradient
    (hunit : ∀ x, inner ℝ (mgradient I f x) (mgradient I f x) = 1) (c : ℝ) :
    IsRegularValue I 𝓘(ℝ) f c := by
  rw [isRegularValue_iff]
  intro x _
  rw [isRegularPoint_iff_mvfderiv_ne_zero]
  intro hz
  have h := mvfderiv_apply_mgradient (I := I) (f := f) (x := x)
  rw [hz, zero_apply, hunit] at h
  exact zero_ne_one h

/-- At a regular point `x` of `f`, the derivative of `f` along its gradient is positive:
`df_x(grad f x) = |grad f x|² > 0`. -/
theorem _root_.TauCeti.IsRegularPoint.mvfderiv_apply_mgradient_pos {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) : 0 < mvfderiv I f x (mgradient I f x) := by
  rw [mvfderiv_apply_mgradient, real_inner_self_pos, Ne, mgradient_eq_zero_iff]
  exact isRegularPoint_iff_mvfderiv_ne_zero.mp hx

end Level

end TauCeti.Manifold
