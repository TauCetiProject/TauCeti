/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Evaluation lemmas for orbit-stabilizer decompositions

Mathlib's `MulAction.selfEquivSigmaOrbits'`, `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'`,
and `MulAction.selfEquivSigmaOrbitsQuotientStabilizer` decompose a `G`-set `X` into a disjoint
union of orbits and coset spaces `G ⧸ stabilizer G (φ ω)`. This file records the evaluation of
their inverse equivalences on points and cosets.

## Main results

* `MulAction.selfEquivSigmaOrbits'_symm_apply` (and `AddAction.selfEquivSigmaOrbits'_symm_apply`):
  the inverse of `selfEquivSigmaOrbits'` sends `⟨ω, x⟩` to `(x : X)`.
* `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'_symm_mk` (and
  `AddAction.selfEquivSigmaOrbitsQuotientStabilizer'_symm_mk`): the inverse of
  `selfEquivSigmaOrbitsQuotientStabilizer'` sends `⟨ω, QuotientGroup.mk g⟩` to `g • φ ω`.
* `MulAction.selfEquivSigmaOrbitsQuotientStabilizer_symm_mk` (and
  `AddAction.selfEquivSigmaOrbitsQuotientStabilizer_symm_mk`): the inverse of
  `selfEquivSigmaOrbitsQuotientStabilizer` sends `⟨ω, QuotientGroup.mk g⟩` to `g • ω.out`.
-/

public section

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The inverse of `MulAction.selfEquivSigmaOrbits'` sends `⟨ω, x⟩` to `(x : X)`. -/
@[to_additive (attr := simp)
  /-- The inverse of `AddAction.selfEquivSigmaOrbits'` sends `⟨ω, x⟩` to `(x : X)`. -/]
theorem selfEquivSigmaOrbits'_symm_apply (ω : orbitRel.Quotient G X) (x : ω.orbit) :
    (selfEquivSigmaOrbits' G X).symm ⟨ω, x⟩ = (x : X) := by
  simp [selfEquivSigmaOrbits', Equiv.sigmaCongrRight_symm]

/-- The inverse of `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'` sends
`⟨ω, QuotientGroup.mk g⟩` to `g • φ ω`. -/
@[to_additive (attr := simp)
  /-- The inverse of `AddAction.selfEquivSigmaOrbitsQuotientStabilizer'` sends
  `⟨ω, QuotientAddGroup.mk g⟩` to `g +ᵥ φ ω`. -/]
theorem selfEquivSigmaOrbitsQuotientStabilizer'_symm_mk
    {φ : orbitRel.Quotient G X → X} (hφ : Function.LeftInverse Quotient.mk'' φ)
    (ω : orbitRel.Quotient G X) (g : G) :
    (selfEquivSigmaOrbitsQuotientStabilizer' G X hφ).symm ⟨ω, QuotientGroup.mk g⟩ = g • φ ω := by
  simp [selfEquivSigmaOrbitsQuotientStabilizer', Equiv.sigmaCongrRight_symm]

/-- The inverse of `MulAction.selfEquivSigmaOrbitsQuotientStabilizer` sends
`⟨ω, QuotientGroup.mk g⟩` to `g • ω.out`. -/
@[to_additive (attr := simp)
  /-- The inverse of `AddAction.selfEquivSigmaOrbitsQuotientStabilizer` sends
  `⟨ω, QuotientAddGroup.mk g⟩` to `g +ᵥ ω.out`. -/]
theorem selfEquivSigmaOrbitsQuotientStabilizer_symm_mk
    (ω : orbitRel.Quotient G X) (g : G) :
    (selfEquivSigmaOrbitsQuotientStabilizer G X).symm ⟨ω, QuotientGroup.mk g⟩ = g • ω.out :=
  selfEquivSigmaOrbitsQuotientStabilizer'_symm_mk Quotient.out_eq' ω g

end MulAction
