/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# Representations by Lie algebra morphisms

A representation `Ad` of a monoid `K` on a Lie algebra `L` acts by Lie algebra morphisms when
`Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆` for all `k`, `x` and `y`. Each `Ad k` is then a Lie algebra
morphism (`Representation.toLieHom`), and these morphisms compose as the monoid does. This is how
a group acting on a Lie algebra by automorphisms, as `K` acts on `𝔤` in a pair `(𝔤, K)`, enters
the functoriality of Lie algebra cochains.
-/

public section

namespace Representation

variable {R K L : Type*} [CommRing R] [Monoid K] [LieRing L] [LieAlgebra R L]
  (Ad : Representation R K L) (hAd : ∀ k x y, Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆)

/-- The action of `k` in a representation by Lie algebra morphisms, as a Lie algebra morphism. -/
def toLieHom (k : K) : L →ₗ⁅R⁆ L :=
  { Ad k with map_lie' := hAd k _ _ }

@[simp]
theorem toLieHom_apply (k : K) (x : L) : Ad.toLieHom hAd k x = Ad k x :=
  (rfl)

/-- The identity of `K` acts by the identity Lie algebra morphism. -/
@[simp]
theorem toLieHom_one : Ad.toLieHom hAd 1 = LieHom.id :=
  LieHom.ext fun x ↦ by simp

/-- The Lie algebra morphisms of a representation compose as the monoid does. -/
theorem toLieHom_mul (k k' : K) :
    Ad.toLieHom hAd (k * k') = (Ad.toLieHom hAd k).comp (Ad.toLieHom hAd k') :=
  LieHom.ext fun x ↦ by simp

end Representation
