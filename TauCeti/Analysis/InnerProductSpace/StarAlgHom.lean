/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Quadratic norm identity for star-algebra representations

A star-algebra homomorphism from any complex star algebra to bounded operators
on a Hilbert space sends `f⋆ * f` to the operator `(π f)† (π f)`.
Consequently its diagonal matrix element is the squared norm of `π f ξ`.
This identity does not require a topology, commutativity, or a C⋆-norm on the domain.
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
