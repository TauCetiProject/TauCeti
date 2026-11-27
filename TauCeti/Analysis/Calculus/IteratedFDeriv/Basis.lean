/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Iterated derivatives of a map and of its coordinates in a basis

Let `b` be a basis of a finite-dimensional normed space `G` over `𝕜 = ℝ` or `ℂ`, and `f : E → G` a
map on a real normed space that is `C^i` at a point `x`. Since `f = ∑ₗ (b.coord l ∘ f) • b l`, the
`i`-th derivative of `f` at `x` is bounded by those of its coordinates:
`‖D^i f(x)‖ ≤ ∑ₗ ‖b l‖ ‖D^i (b.coord l ∘ f)(x)‖` (`Module.Basis.norm_iteratedFDeriv_le_sum`).
The derivatives are taken over `ℝ`, so for a complex space `G` the coordinates are complex-valued
functions of a real variable, as for the frame coefficients of a section of a complex vector bundle
over a real manifold.
-/

public section

namespace Module.Basis

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]
  [FiniteDimensional 𝕜 G] {ι : Type*} [Fintype ι]

/-- The `i`-th derivative at `x` of a map into a finite-dimensional space that is `C^i` at `x` is
bounded by the `i`-th derivatives at `x` of its coordinates in a basis `b`, weighted by the norms
of the basis vectors. -/
theorem norm_iteratedFDeriv_le_sum (b : Basis ι 𝕜 G) {f : E → G} {i : ℕ} {x : E}
    (hf : ContDiffAt ℝ i f x) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ ∑ l, ‖b l‖ * ‖iteratedFDeriv ℝ i (fun y ↦ b.coord l (f y)) x‖ := by
  have hΛ (l : ι) : ContDiffAt ℝ i (fun y ↦ b.coord l (f y)) x :=
    ((LinearMap.toContinuousLinearMap (b.coord l)).restrictScalars ℝ).contDiff.contDiffAt.comp
      x hf
  have hf' : f = fun y ↦ ∑ l, (ContinuousLinearMap.id ℝ 𝕜).smulRight (b l) (b.coord l (f y)) :=
    funext fun y ↦ by simp [b.sum_repr (f y)]
  nth_rewrite 1 [hf']
  refine (TauCeti.norm_iteratedFDeriv_sum_comp_left_le (𝕜 := ℝ) Finset.univ
    (fun l ↦ (ContinuousLinearMap.id ℝ 𝕜).smulRight (b l)) fun l _ ↦ hΛ l).trans
    (Finset.sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z ↦ by simp [norm_smul, mul_comm]

end Module.Basis
