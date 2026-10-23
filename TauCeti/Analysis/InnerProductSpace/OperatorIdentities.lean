/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, qwen3.8-27b-dbirks-hyperqwen-huge
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

/-!
# Diagonal, polarization, and absorption identities for continuous linear operators

This module collects operator identities independent of projection-valued measures.

* `ContinuousLinearMap.inner_polarization` recovers `⟪ψ, T ξ⟫` from four diagonal values.
* `ContinuousLinearMap.eq_of_diagonal` uses complex polarization to identify operators from
  their diagonal inner products.
* `ContinuousLinearMap.norm_sub_sq_of_selfAdjoint_idempotent_absorption` computes the squared
  distance between `S x` and `T x` when `S` is a self-adjoint idempotent absorbed by `T`.

Use `eq_of_diagonal` to identify bounded complex-linear operators when
their diagonal inner products agree on every vector. Use
`norm_sub_sq_of_selfAdjoint_idempotent_absorption` to compare two operators
when the first is a self-adjoint projection absorbed by the second.
The latter identity applies over real or complex scalars and does not
require the second operator to be self-adjoint.
-/

public section

open scoped InnerProduct InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Complex polarization: equality of all diagonal inner products determines a continuous
linear operator. This specializes Mathlib's `ext_inner_map` to continuous linear maps. -/
theorem eq_of_diagonal (S T : H →L[ℂ] H)
    (h : ∀ x : H, ⟪x, S x⟫_ℂ = ⟪x, T x⟫_ℂ) : S = T := by
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun x => ?_)
  -- `ext_inner_map` compares linear maps; applying a continuous linear map is the same.
  change ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ
  rw [← inner_conj_symm (S x) x, ← inner_conj_symm (T x) x, h x]

/-- The complex polarization identity for the sesquilinear form of a bounded
operator, recovered from its diagonal quadratic form. -/
theorem inner_polarization (T : H →L[ℂ] H) (ψ ξ : H) :
    (1 / 4 : ℂ) *
        (⟪ξ + ψ, T (ξ + ψ)⟫_ℂ
          + Complex.I * ⟪ξ + Complex.I • ψ, T (ξ + Complex.I • ψ)⟫_ℂ
          - ⟪ξ - ψ, T (ξ - ψ)⟫_ℂ
          - Complex.I * ⟪ξ - Complex.I • ψ, T (ξ - Complex.I • ψ)⟫_ℂ)
      = ⟪ψ, T ξ⟫_ℂ := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Over either the real or complex scalars, if `S` is self-adjoint, idempotent,
and satisfies `S * T = S`, then the squared norm of `(S - T) x` is the difference
of the squared norms. The operator `T` need not be self-adjoint. -/
theorem norm_sub_sq_of_selfAdjoint_idempotent_absorption
    (S T : E →L[𝕜] E) (hS : IsSelfAdjoint S)
    (hSS : S * S = S) (hST : S * T = S) (x : E) :
    ‖S x - T x‖ ^ 2 = ‖T x‖ ^ 2 - ‖S x‖ ^ 2 := by
  have hcross : ⟪S x, T x⟫_𝕜 = ⟪S x, S x⟫_𝕜 := by
    calc
      ⟪S x, T x⟫_𝕜 = ⟪x, S (T x)⟫_𝕜 := hS.isSymmetric x (T x)
      _ = ⟪x, S x⟫_𝕜 := by rw [← mul_apply_eq_comp, hST]
      _ = ⟪x, S (S x)⟫_𝕜 := by rw [← mul_apply_eq_comp, hSS]
      _ = ⟪S x, S x⟫_𝕜 := (hS.isSymmetric x (S x)).symm
  rw [norm_sub_sq (𝕜 := 𝕜), hcross, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  ring

end RCLike

end ContinuousLinearMap
