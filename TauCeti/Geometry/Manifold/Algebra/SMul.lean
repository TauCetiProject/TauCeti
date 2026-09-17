/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Diffeomorphisms from pointwise-smooth group actions

This file packages the action of an element of a group with a `ContMDiffConstSMul` instance as a
self-diffeomorphism. Unlike `Diffeomorph.smul`, this construction does not require a manifold
structure on the acting group or joint smoothness of the action.

## Main declaration

* `Diffeomorph.constSmul`: the diffeomorphism given by a fixed element of a pointwise-smooth
  group action.
-/

public section

open scoped ContDiff Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [Group G] [MulAction G M] {n : ℕ∞ω} [ContMDiffConstSMul I n G M] (g : G)

variable (I n) in
/-- The diffeomorphism given by a fixed element of a pointwise `Cⁿ` group action. Its inverse is
scalar multiplication by the inverse group element. -/
@[expose, to_additive
/-- The diffeomorphism given by a fixed element of a pointwise `Cⁿ` additive group action. Its
inverse is addition by the negated group element. -/]
def constSmul : M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := contMDiff_const_smul g
  contMDiff_invFun := contMDiff_const_smul g⁻¹

/-- Evaluating the diffeomorphism associated to a fixed group element agrees with its action. -/
@[to_additive (attr := simp)
  /-- Evaluating the diffeomorphism associated to a fixed additive-group element agrees with its
  action. -/]
lemma constSmul_apply (x : M) : constSmul I n g x = g • x := rfl

/-- The inverse of the diffeomorphism associated to a fixed group element acts by its inverse. -/
@[to_additive (attr := simp)
  /-- The inverse of the diffeomorphism associated to a fixed additive-group element acts by its
  negation. -/]
lemma constSmul_symm_apply (x : M) : (constSmul I n g).symm x = g⁻¹ • x := rfl

/-- Taking the inverse of a fixed-action diffeomorphism inverts the acting group element. -/
@[to_additive
  /-- Taking the inverse of a fixed-action diffeomorphism negates the acting additive-group
  element. -/]
lemma constSmul_symm :
    (constSmul I n g : M ≃ₘ^n⟮I, I⟯ M).symm = constSmul I n g⁻¹ :=
  Diffeomorph.ext fun _ ↦ rfl

end Diffeomorph
