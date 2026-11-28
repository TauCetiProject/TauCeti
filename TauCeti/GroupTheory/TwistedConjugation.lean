/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Basic

/-!
# Twisted conjugation by a group element

For an endomorphism `σ` of a group the right-action convention for twisted conjugation is
`b ↦ g⁻¹ * b * σ g`. Multiplying the conjugator on the right composes two such operations.
-/

public section

namespace MonoidHom

variable {G : Type*} [Group G]

/-- The `σ`-twisted conjugate of `b` by `g`, in the right-action convention. -/
def twistedConj (σ : G →* G) (g b : G) : G :=
  g⁻¹ * b * σ g

/-- Twisted conjugation multiplies by `g⁻¹` on the left and by `σ g` on the right. -/
theorem twistedConj_def (σ : G →* G) (g b : G) :
    σ.twistedConj g b = g⁻¹ * b * σ g := (rfl)

/-- The identity element fixes every element under twisted conjugation. -/
@[simp]
theorem twistedConj_one (σ : G →* G) (b : G) : σ.twistedConj 1 b = b := by
  simp [twistedConj]

/-- Twisted conjugation by `g * i` is twisted conjugation by `g` followed by that by `i`. -/
theorem twistedConj_mul (σ : G →* G) (g i b : G) :
    σ.twistedConj (g * i) b = σ.twistedConj i (σ.twistedConj g b) := by
  simp [twistedConj, mul_assoc]

end MonoidHom
