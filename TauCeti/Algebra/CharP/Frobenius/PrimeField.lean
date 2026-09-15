/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Iterated Frobenius over the prime field

Every element of the prime field `ZMod p` satisfies `a ^ p = a`, so for an algebra `A` over
`ZMod p` of exponential characteristic `p` the iterated Frobenius `x ↦ x ^ p ^ n` fixes the image
of `ZMod p` and is therefore a homomorphism of `ZMod p`-algebras, not merely of rings. This is
what lets the Frobenius act on a construction over the prime field that is functorial in
`ZMod p`-algebras rather than in rings.

## Main declarations

* `TauCeti.iterateFrobeniusAlgHom`: the `p ^ n`-power Frobenius of a `ZMod p`-algebra, as an
  algebra endomorphism.
-/

public section

namespace TauCeti

variable (p n : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Algebra (ZMod p) A] [ExpChar A p]

/-- **The `p ^ n`-power Frobenius of an algebra over the prime field, as an algebra
endomorphism.** -/
noncomputable def iterateFrobeniusAlgHom : A →ₐ[ZMod p] A where
  toRingHom := iterateFrobenius A p n
  commutes' r := by
    -- Expose the underlying ring homomorphism hidden by the algebra-morphism bundling.
    change iterateFrobenius A p n (algebraMap (ZMod p) A r) = algebraMap (ZMod p) A r
    rw [← (algebraMap (ZMod p) A).map_iterateFrobenius p r n, iterateFrobenius_def,
      ZMod.pow_card_pow]

/-- The algebra endomorphism of the Frobenius is the iterated Frobenius ring homomorphism. -/
@[simp]
theorem coe_iterateFrobeniusAlgHom :
    (iterateFrobeniusAlgHom p n A : A →+* A) = iterateFrobenius A p n := by
  rw [iterateFrobeniusAlgHom]
  rfl

/-- The algebra endomorphism of the Frobenius raises an element to its `p ^ n`-th power. -/
@[simp]
theorem iterateFrobeniusAlgHom_apply (a : A) : iterateFrobeniusAlgHom p n A a = a ^ p ^ n := by
  -- Expose the underlying ring homomorphism hidden by the algebra-morphism bundling.
  change (iterateFrobeniusAlgHom p n A : A →+* A) a = a ^ p ^ n
  rw [coe_iterateFrobeniusAlgHom, iterateFrobenius_def]

end TauCeti
