/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.GroupTheory.TwistedConjugation

/-!
# Twisted relative position

If an endomorphism `σ` of `G` preserves a subgroup `I`, the relative position of the left cosets
`gI` and `bσ(g)I` defines a map from `G ⧸ I` to the double-coset space of `I`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The `σ`-twisted relative position of `gI` is its relative position with `bσ(g)I`, given by
the double coset of `g⁻¹ * b * σ g`. The condition `I.map σ ≤ I` makes it independent of the
representative. -/
def twistedRelativePosition (I : Subgroup G) (σ : G →* G) (hσ : I.map σ ≤ I) (b : G) :
    G ⧸ I → DoubleCoset.Quotient (I : Set G) (I : Set G) :=
  Quotient.map' (fun g ↦ σ.twistedConj g b) fun x y hxy ↦ by
    have hi : x⁻¹ * y ∈ I := QuotientGroup.leftRel_apply.mp hxy
    refine DoubleCoset.rel_iff.mpr ⟨(x⁻¹ * y)⁻¹, I.inv_mem hi, σ (x⁻¹ * y),
      hσ (Subgroup.mem_map_of_mem σ hi), ?_⟩
    calc
      σ.twistedConj y b = σ.twistedConj (x * (x⁻¹ * y)) b := by rw [mul_inv_cancel_left]
      _ = (x⁻¹ * y)⁻¹ * σ.twistedConj x b * σ (x⁻¹ * y) := by
        rw [σ.twistedConj_mul, MonoidHom.twistedConj_def σ (x⁻¹ * y)]

/-- The twisted relative position on the coset represented by `g`. -/
@[simp]
theorem twistedRelativePosition_mk (I : Subgroup G) (σ : G →* G) (hσ : I.map σ ≤ I)
    (b g : G) :
    I.twistedRelativePosition σ hσ b (g : G ⧸ I) = DoubleCoset.mk I I (σ.twistedConj g b) :=
  (rfl)

end Subgroup
