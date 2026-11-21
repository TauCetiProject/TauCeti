/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Algebra.Star.TensorProduct
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Star-algebra representations on Hilbert spaces

A star-algebra homomorphism from any complex star algebra to bounded operators
on a Hilbert space sends `f⋆ * f` to the operator `(π f)† (π f)`.
Consequently its diagonal matrix element is the squared norm of `π f ξ`.
This identity does not require a topology, commutativity, or a C⋆-norm on the domain.

A bounded linear map intertwines two joint representations of an algebraic tensor product
exactly when it intertwines both constituent actions. For an M–N Hilbert bimodule, take the
second algebra to be `Nᵐᵒᵖ`, so that the tensor `x ⊗ yᵒᵖ` acts by `ξ ↦ xξy`.
-/

public section

open scoped InnerProductSpace

namespace StarAlgHom

variable {A H : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The squared norm of a represented vector equals the real part of its
quadratic matrix coefficient, for a representation of any complex star algebra. -/
theorem norm_sq_apply_eq_re_inner_star_mul
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : A) :
    ‖π f ξ‖ ^ 2 = RCLike.re ⟪ξ, π (star f * f) ξ⟫_ℂ := by
  -- Express the squared norm as ⟪ξ, (π f)† (π f) ξ⟫, then transport
  -- the adjoint and product through the star homomorphism.
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
    ← map_star, ← map_mul]

end StarAlgHom

namespace ContinuousLinearMap

open scoped TensorProduct
open Algebra.TensorProduct

variable {𝕜 A B H K : Type*} [RCLike 𝕜]
  [Semiring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A]
  [Semiring B] [StarRing B] [Algebra 𝕜 B] [StarModule 𝕜 B]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- A bounded operator intertwines joint star representations if and only if it intertwines
both commuting constituent representations. -/
theorem comp_starLift_iff (T : H →L[𝕜] K)
    (π : A →⋆ₐ[𝕜] H →L[𝕜] H) (σ : B →⋆ₐ[𝕜] H →L[𝕜] H)
    (π' : A →⋆ₐ[𝕜] K →L[𝕜] K) (σ' : B →⋆ₐ[𝕜] K →L[𝕜] K)
    (h : ∀ a b, Commute (π a) (σ b)) (h' : ∀ a b, Commute (π' a) (σ' b)) :
    (∀ z, T.comp (starLift π σ h z) = (starLift π' σ' h' z).comp T) ↔
      (∀ a, T.comp (π a) = (π' a).comp T) ∧
      (∀ b, T.comp (σ b) = (σ' b).comp T) := by
  simpa only [← toAlgHom_starLift, StarAlgHom.coe_toAlgHom] using
    T.comp_lift_iff π.toAlgHom σ.toAlgHom π'.toAlgHom σ'.toAlgHom h h'

end ContinuousLinearMap
