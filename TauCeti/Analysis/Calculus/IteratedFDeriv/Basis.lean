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
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Iterated derivatives of a map and of its coordinates in a basis

Let `b` be a basis of a finite-dimensional normed space `G` over `𝕜 = ℝ` or `ℂ`, and `f : E → G` a
`C^i` map on a real normed space. Since `f = ∑ₗ (b.coord l ∘ f) • b l`, the `i`-th derivative of
`f` is bounded by those of its coordinates: `‖D^i f(x)‖ ≤ ∑ₗ ‖b l‖ ‖D^i (b.coord l ∘ f)(x)‖`
(`Module.Basis.norm_iteratedFDeriv_le_sum`). The derivatives are taken over `ℝ`, so for a complex
space `G` the coordinates are complex-valued functions of a real variable, as for the frame
coefficients of a section of a complex vector bundle over a real manifold.
-/

public section

namespace Module.Basis

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]
  [FiniteDimensional 𝕜 G] {ι : Type*} [Fintype ι]

/-- The `i`-th derivative of a `C^i` map into a finite-dimensional space is bounded by the
`i`-th derivatives of its coordinates in a basis `b`, weighted by the norms of the basis vectors. -/
theorem norm_iteratedFDeriv_le_sum (b : Basis ι 𝕜 G) {f : E → G} {i : ℕ} (hf : ContDiff ℝ i f)
    (x : E) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ ∑ l, ‖b l‖ * ‖iteratedFDeriv ℝ i (fun y ↦ b.coord l (f y)) x‖ := by
  have hΛ (l : ι) : ContDiff ℝ i fun y ↦ b.coord l (f y) :=
    ((LinearMap.toContinuousLinearMap (b.coord l)).restrictScalars ℝ).contDiff.comp hf
  have hf' : f = fun y ↦ ∑ l, (ContinuousLinearMap.id ℝ 𝕜).smulRight (b l) (b.coord l (f y)) :=
    funext fun y ↦ by simp [b.sum_repr (f y)]
  nth_rewrite 1 [hf']
  rw [iteratedFDeriv_sum (f := fun l y ↦ (ContinuousLinearMap.id ℝ 𝕜).smulRight (b l)
    (b.coord l (f y))) fun l _ ↦ ((ContinuousLinearMap.id ℝ 𝕜).smulRight (b l)).contDiff.comp
      (hΛ l), Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
  refine (((ContinuousLinearMap.id ℝ 𝕜).smulRight (b l)).norm_iteratedFDeriv_comp_left
    (hΛ l).contDiffAt le_rfl).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z ↦ by simp [norm_smul, mul_comm]

end Module.Basis
