/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# Tangent vectors and the antipode

A counit-valued derivation `d` of a commutative Hopf algebra is a tangent vector at the identity
of the corresponding affine group. Inversion on the group is represented by the antipode `S`, and
its differential at the identity is negation: `d ∘ S = -d`.

Consequently a tangent vector that annihilates a set of coordinate functions also annihilates
their antipodes. This is what lets the Lie algebra of a closed subgroup be computed from an
antipode-stable generating set of its ideal, such as the matrix coefficients and their antipodes
cutting out the stabilizer of a subspace of a representation.

## Main declaration

* `Derivation.apply_antipode`: a counit-valued derivation negates under the antipode.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open TauCeti WithConv

namespace Derivation

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B]
  [Algebra R B]

/-- A tangent vector at the identity negates under the antipode: the differential of inversion
at the identity is `-1`. -/
@[simp]
theorem apply_antipode (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    d (HopfAlgebra.antipode R a) = -d a := by
  have h := congrArg (fun ψ : tangentKer R A B ↦ TrivSqZeroExt.snd (ψ.val.ofConv a))
    (map_inv (derivationMulEquivTangentKer R A B) (.ofAdd d))
  rw [← ofAdd_neg, derivationMulEquivTangentKer_apply_snd, toAdd_ofAdd, Subgroup.coe_inv,
    convInv_def, ofConv_toConv, AlgHom.antipodeComp_apply,
    derivationMulEquivTangentKer_apply_snd, toAdd_ofAdd] at h
  rw [← h, neg_apply]

end Derivation
