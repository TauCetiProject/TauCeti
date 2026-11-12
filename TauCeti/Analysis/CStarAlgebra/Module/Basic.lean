/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs

/-!
# Separation by C⋆-module inner products

The coefficient-valued inner product separates vectors in either variable. These
extensionality principles allow identities of module operators to be checked by
pairing against arbitrary vectors, without a scalar-valued Riesz theorem.
-/

public section

namespace CStarModule

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
  [CStarModule A E]

/-- Vectors are determined by their inner products against all vectors in the first slot. -/
theorem ext_inner_left {x y : E} (h : ∀ z, inner A z x = inner A z y) : x = y := by
  apply sub_eq_zero.mp
  apply (inner_self (A := A)).mp
  simp [inner_sub_right, h]

/-- Vectors are determined by their inner products against all vectors in the second slot. -/
theorem ext_inner_right {x y : E} (h : ∀ z, inner A x z = inner A y z) : x = y := by
  apply ext_inner_left (A := A)
  intro z
  simpa using congrArg star (h z)

end CStarModule
