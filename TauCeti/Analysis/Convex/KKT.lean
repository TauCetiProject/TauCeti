/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sufficiency of the Karush–Kuhn–Tucker conditions

Let `E` and `F` be real Hilbert spaces, `f : E → ℝ` an objective, `g : ι → E → ℝ` finitely many
inequality constraints and `A x = b` a continuous linear equality constraint, with feasible set
`{x | (∀ i, g i x ≤ 0) ∧ A x = b}`. The *Karush–Kuhn–Tucker conditions* at a point `xs` are primal
feasibility (`xs` lies in the feasible set), multipliers `l i ≥ 0` and `y : F` with complementary
slackness `l i * g i xs = 0`, and subgradients `u ∈ ∂f(xs)`, `v i ∈ ∂gᵢ(xs)` (the subdifferential
`TauCeti.subdifferential` for the inner product pairing) such that
`u + ∑ i, l i • v i + Aᵀ y = 0`, where `Aᵀ` is the Hilbert adjoint.

The theorem assumes these conditions with primal feasibility weakened to the equality constraint
`A xs = b`, and concludes `IsMinOn f {x | (∀ i, g i x ≤ 0) ∧ A x = b} xs`, that is,
`f xs ≤ f x` for every feasible `x`. `IsMinOn` does not include membership of `xs` in the set:
without `g i xs ≤ 0` the point `xs` may be infeasible, and the conclusion is only this comparison
of objective values. When also `g i xs ≤ 0` for all `i`, so that all the KKT conditions hold,
`xs` is a minimizer of `f` on the feasible set. No constraint qualification and no convexity
hypothesis is needed: the subgradient inequalities themselves carry the argument, and
complementary slackness controls the terms with `l i ≠ 0`.

## Main statements

* `TauCeti.isMinOn_of_kkt` — **sufficiency of the Karush–Kuhn–Tucker conditions**: `f xs ≤ f x`
  for every feasible `x`.

## References

* J.-B. Hiriart-Urruty and C. Lemaréchal, *Convex Analysis and Minimization Algorithms I*,
  Grundlehren 305, Springer 1993, Chapter VII, Theorem 2.2.5, p. 310 (for convex data).

The argument follows `CKMA.HasConvexKKTMultipliers.isMinOn` in `CKMA/Analysis/Convex/Duality.lean`
of lean-CKMA (<https://github.com/bjbraams/lean-CKMA>), which is stated for the evaluation
pairing with values in `Fin m → ℝ`; here it is restated for the inner product pairing and the
Hilbert adjoint.
-/

public section

open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Sufficiency of the Karush–Kuhn–Tucker conditions.** Let `xs` satisfy the equality
constraint `A xs = b`, and let `l i ≥ 0` and `y` be multipliers with complementary slackness
`l i * g i xs = 0` and subgradients `u ∈ ∂f(xs)`, `v i ∈ ∂gᵢ(xs)` for the inner product pairing
with `u + ∑ i, l i • v i + Aᵀ y = 0`. Then `f xs ≤ f x` for every `x` in the feasible set
`{x | (∀ i, g i x ≤ 0) ∧ A x = b}`. The point `xs` itself need not satisfy `g i xs ≤ 0`; when it
does, all the KKT conditions hold and `xs` is a minimizer of `f` on the feasible set. No convexity
of `f` or `g i` and no constraint qualification is assumed. -/
theorem isMinOn_of_kkt {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ}
    (A : E →L[ℝ] F) (b : F) {xs : E} (hxs : A xs = b) (l : ι → ℝ) (y : F)
    (hl : ∀ i, 0 ≤ l i) (hcs : ∀ i, l i * g i xs = 0) (u : E)
    (hu : u ∈ subdifferential (innerₗ E) (fun x => (f x : EReal)) xs) (v : ι → E)
    (hv : ∀ i, v i ∈ subdifferential (innerₗ E) (fun x => (g i x : EReal)) xs)
    (hsum : u + ∑ i, l i • v i + ContinuousLinearMap.adjoint A y = 0) :
    IsMinOn f {x | (∀ i, g i x ≤ 0) ∧ A x = b} xs := by
  refine isMinOn_iff.2 fun x ⟨hgx, hAx⟩ => ?_
  have hfx := (mem_subdifferential_coe_iff _ f).1 hu x
  simp only [innerₗ_apply_apply] at hfx
  -- Each weighted constraint term `l i * ⟪x - xs, v i⟫` is at most `l i * g i x ≤ 0`.
  have hterm (i : ι) : l i * ⟪x - xs, v i⟫ ≤ 0 := by
    have hgi := (mem_subdifferential_coe_iff _ (g i)).1 (hv i) x
    simp only [innerₗ_apply_apply] at hgi
    nlinarith [mul_le_mul_of_nonneg_left hgi (hl i), mul_nonpos_of_nonneg_of_nonpos (hl i) (hgx i),
      hcs i]
  -- Pairing the stationarity condition with `x - xs`: the adjoint term vanishes on `ker A`.
  have hstat : ⟪x - xs, u⟫ + ∑ i, l i * ⟪x - xs, v i⟫ = 0 := by
    have h := congrArg (fun w => ⟪x - xs, w⟫) hsum
    simpa only [inner_add_right, inner_sum, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right, map_sub, hAx, hxs, sub_self, inner_zero_left,
      inner_zero_right, add_zero] using h
  have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hterm i
  linarith

end TauCeti
