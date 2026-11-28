/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Derivatives of paths of idempotents

Differentiating a path of idempotents gives `P' P + P P' = P'`. In particular its
compression `P P' P` vanishes. These identities describe tangent vectors to the space of
projections and give the correction term in parallel transport of their ranges.
-/

public section

open scoped Topology

namespace HasDerivAt

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [NormedRing B] [NormedAlgebra 𝕜 B]
  {P : 𝕜 → B} {D : B} {t : 𝕜}

/-- The derivative of a path of idempotents is the sum of its two products with the
idempotent. Idempotence is required only in a neighborhood of the differentiation point. -/
theorem mul_add_mul_eq_of_isIdempotentElem (hP : HasDerivAt P D t)
    (h : ∀ᶠ s in 𝓝 t, IsIdempotentElem (P s)) : D * P t + P t * D = D := by
  exact ((hP.mul hP).congr_of_eventuallyEq (h.mono fun _ hs ↦ hs.eq.symm)).unique hP

/-- The derivative of a path of idempotents has zero compression to the range of the
idempotent. -/
theorem mul_mul_eq_zero_of_isIdempotentElem (hP : HasDerivAt P D t)
    (h : ∀ᶠ s in 𝓝 t, IsIdempotentElem (P s)) : P t * D * P t = 0 := by
  have hd := congrArg (fun a ↦ P t * a) (hP.mul_add_mul_eq_of_isIdempotentElem h)
  rw [mul_add, ← mul_assoc (P t) (P t), h.self_of_nhds.eq] at hd
  simpa only [mul_assoc] using add_eq_right.mp hd

end HasDerivAt
