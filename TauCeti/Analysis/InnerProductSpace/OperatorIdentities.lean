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
# Diagonal, polarization, and absorption identities for linear operators

This module collects operator identities independent of projection-valued measures.

* `LinearMap.inner_polarization` recovers `⟪ψ, T ξ⟫` from four diagonal values, and
  `LinearMap.norm_inner_le_add` bounds `‖⟪ψ, T ξ⟫‖` by a quarter of the sum of their norms.
* `LinearMap.norm_sub_sq_of_isSymmetric_idempotent_absorption` computes the squared
  distance between `S x` and `T x` when `S` is a symmetric idempotent absorbed by `T`.
* `ContinuousLinearMap.eq_of_diagonal` uses complex polarization to identify operators from
  their diagonal inner products.
* `ContinuousLinearMap.adjoint_ofReal_smul`: the adjoint commutes with real scalars.
* `ContinuousLinearMap.adjoint_apply_one`: the adjoint of an operator on the scalars takes the
  conjugate value at `1`.
* `ContinuousLinearMap.norm_apply_sq_of_adjoint_comp_eq_smul`: if `T† T = c` for a real scalar
  `c`, then `‖T x‖² = c ‖x‖²`.
* `ContinuousLinearMap.adjoint_smul_comp_smul`: multiplying `T` by a scalar `c` multiplies
  `T† T` by `‖c‖²`.
* `ContinuousLinearMap.adjoint_ofReal_smul_comp_ofReal_smul` and
  `ContinuousLinearMap.ofReal_smul_comp_adjoint_ofReal_smul`: if `T† T` (respectively `T T†`)
  is a real scalar `s`, then the same product for `c T` is `c² s`.

The first two identities and the polarization bound use only linearity, so they are stated
for linear maps on seminormed inner product spaces; apply them to a continuous linear map `T`
through its coercion `(T : E →ₗ[𝕜] E)`.

Use `eq_of_diagonal` to identify bounded complex-linear operators when
their diagonal inner products agree on every vector. Use
`norm_sub_sq_of_isSymmetric_idempotent_absorption` to compare two operators
when the first is an orthogonal projection absorbed by the second.
The latter identity applies over real or complex scalars, needs no completeness,
and does not require the second operator to be symmetric.
-/

public section

open scoped InnerProduct InnerProductSpace

namespace LinearMap

/-- The complex polarization identity for the sesquilinear form of a linear
operator, recovered from its diagonal quadratic form. This is the complex conjugate of
Mathlib's `inner_map_polarization'`, written with the operator on the right. -/
theorem inner_polarization {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ[ℂ] H) (ψ ξ : H) :
    (1 / 4 : ℂ) *
        (⟪ξ + ψ, T (ξ + ψ)⟫_ℂ
          + Complex.I * ⟪ξ + Complex.I • ψ, T (ξ + Complex.I • ψ)⟫_ℂ
          - ⟪ξ - ψ, T (ξ - ψ)⟫_ℂ
          - Complex.I * ⟪ξ - Complex.I • ψ, T (ξ - Complex.I • ψ)⟫_ℂ)
      = ⟪ψ, T ξ⟫_ℂ := by
  rw [← inner_conj_symm ψ, inner_map_polarization' T ξ ψ]
  simp only [map_div₀, map_sub, map_add, map_mul, inner_conj_symm, Complex.conj_I, map_ofNat]
  ring

/-- The polarization bound for the sesquilinear form of a linear operator: `‖⟪ψ, T ξ⟫‖` is at most
a quarter of the sum of the four diagonal values `‖⟪v, T v⟫‖` for `v = ξ + ψ`, `ξ - ψ`,
`ξ + i ψ` and `ξ - i ψ`. -/
theorem norm_inner_le_add {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ[ℂ] H) (ψ ξ : H) :
    ‖⟪ψ, T ξ⟫_ℂ‖ ≤ (‖⟪ξ + ψ, T (ξ + ψ)⟫_ℂ‖ + ‖⟪ξ - ψ, T (ξ - ψ)⟫_ℂ‖ +
      ‖⟪ξ + Complex.I • ψ, T (ξ + Complex.I • ψ)⟫_ℂ‖ +
      ‖⟪ξ - Complex.I • ψ, T (ξ - Complex.I • ψ)⟫_ℂ‖) / 4 := by
  rw [← T.inner_polarization ψ ξ, norm_mul, one_div, norm_inv, RCLike.norm_ofNat,
    inv_mul_eq_div]
  gcongr
  generalize ⟪ξ + ψ, T (ξ + ψ)⟫_ℂ = a, ⟪ξ - ψ, T (ξ - ψ)⟫_ℂ = b,
    ⟪ξ + Complex.I • ψ, T (ξ + Complex.I • ψ)⟫_ℂ = c,
    ⟪ξ - Complex.I • ψ, T (ξ - Complex.I • ψ)⟫_ℂ = d
  have h₁ := norm_sub_le (a + Complex.I * c - b) (Complex.I * d)
  have h₂ := norm_sub_le (a + Complex.I * c) b
  have h₃ := norm_add_le a (Complex.I * c)
  rw [norm_mul, Complex.norm_I, one_mul] at h₁ h₃
  linarith

/-- Over either the real or complex scalars, if `S` is symmetric, idempotent,
and satisfies `S * T = S`, then the squared norm of `(S - T) x` is the difference
of the squared norms. The operator `T` need not be symmetric. -/
theorem norm_sub_sq_of_isSymmetric_idempotent_absorption {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (S T : E →ₗ[𝕜] E) (hS : S.IsSymmetric) (hSS : S * S = S) (hST : S * T = S) (x : E) :
    ‖S x - T x‖ ^ 2 = ‖T x‖ ^ 2 - ‖S x‖ ^ 2 := by
  have hcross : ⟪S x, T x⟫_𝕜 = ⟪S x, S x⟫_𝕜 := by
    calc
      ⟪S x, T x⟫_𝕜 = ⟪x, S (T x)⟫_𝕜 := hS x (T x)
      _ = ⟪x, S x⟫_𝕜 := by rw [← mul_apply_eq_comp, hST]
      _ = ⟪x, S (S x)⟫_𝕜 := by rw [← mul_apply_eq_comp, hSS]
      _ = ⟪S x, S x⟫_𝕜 := (hS x (S x)).symm
  rw [norm_sub_sq (𝕜 := 𝕜), hcross, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  ring

end LinearMap

namespace ContinuousLinearMap

/-- Complex polarization: equality of all diagonal inner products determines a continuous
linear operator. This specializes Mathlib's `ext_inner_map` to continuous linear maps. -/
theorem eq_of_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S T : H →L[ℂ] H) (h : ∀ x : H, ⟪x, S x⟫_ℂ = ⟪x, T x⟫_ℂ) : S = T :=
  coe_injective <| (ext_inner_map _ _).mp fun x => by
    simpa only [coe_coe, inner_conj_symm] using congrArg (starRingEnd ℂ) (h x)

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- An operator on the scalars is multiplication by its value `T 1`, and its adjoint is
multiplication by the conjugate value: `T† 1 = conj (T 1)`. -/
theorem adjoint_apply_one (T : 𝕜 →L[𝕜] 𝕜) : T.adjoint 1 = starRingEnd 𝕜 (T 1) := by
  have h := T.adjoint_inner_left 1 1
  simp only [RCLike.inner_apply, map_one, mul_one, one_mul] at h
  rw [← h, starRingEnd_self_apply]

/-- The adjoint commutes with multiplication by a real scalar. -/
theorem adjoint_ofReal_smul (r : ℝ) (T : E →L[𝕜] F) :
    ((r : 𝕜) • T).adjoint = (r : 𝕜) • T.adjoint := by
  rw [map_smulₛₗ, RCLike.conj_ofReal]

/-- An operator `T` with `T† T = c` for a real scalar `c` multiplies norms squared by `c`. -/
theorem norm_apply_sq_of_adjoint_comp_eq_smul {T : E →L[𝕜] F} {c : ℝ}
    (hT : T.adjoint ∘L T = (c : 𝕜) • 1) (x : E) : ‖T x‖ ^ 2 = c * ‖x‖ ^ 2 := by
  rw [apply_norm_sq_eq_inner_adjoint_left, hT]
  simp [inner_smul_left, inner_self_eq_norm_sq_to_K]

/-- Multiplying an operator by a scalar `c` multiplies `T† T` by `‖c‖²`. -/
theorem adjoint_smul_comp_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).adjoint ∘L (c • T) = ((‖c‖ ^ 2 : ℝ) : 𝕜) • (T.adjoint ∘L T) := by
  rw [map_smulₛₗ, smul_comp, comp_smul, smul_smul, RCLike.conj_mul, RCLike.ofReal_pow]

/-- If `T† T = s` for a real scalar `s`, then `(c T)† (c T) = c² s` for real `c`. -/
theorem adjoint_ofReal_smul_comp_ofReal_smul {T : E →L[𝕜] F} {s : ℝ}
    (hT : T.adjoint ∘L T = (s : 𝕜) • 1) (c : ℝ) :
    ((c : 𝕜) • T).adjoint ∘L ((c : 𝕜) • T) = ((c ^ 2 * s : ℝ) : 𝕜) • 1 := by
  simp [adjoint_ofReal_smul, hT, smul_smul, sq, mul_assoc]

/-- If `T T† = s` for a real scalar `s`, then `(c T) (c T)† = c² s` for real `c`. -/
theorem ofReal_smul_comp_adjoint_ofReal_smul {T : E →L[𝕜] F} {s : ℝ}
    (hT : T ∘L T.adjoint = (s : 𝕜) • 1) (c : ℝ) :
    ((c : 𝕜) • T) ∘L ((c : 𝕜) • T).adjoint = ((c ^ 2 * s : ℝ) : 𝕜) • 1 := by
  simp [adjoint_ofReal_smul, hT, smul_smul, sq, mul_assoc]

end RCLike

end ContinuousLinearMap
