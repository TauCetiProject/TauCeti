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

A representation `Ad` of a monoid `K` on a Lie algebra `L` acts by Lie algebra morphisms
(`Representation.IsLieAction Ad`) when `Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆` for all `k`, `x` and
`y`. Each `Ad k` is then a Lie algebra morphism (`Representation.toLieHom`), and these morphisms
compose as the monoid does. This is how a group acting on a Lie algebra by automorphisms, as `K`
acts on `𝔤` in a pair `(𝔤, K)`, enters the functoriality of Lie algebra cochains.

## Main definitions

* `Representation.IsLieAction Ad`: `K` acts on `L` by Lie algebra morphisms. By
  `Representation.IsLieAction.of_lieEquiv`, this holds when every `Ad k` underlies a Lie algebra
  automorphism.
* `Representation.toLieHom`: the action of `k` in a representation by Lie algebra morphisms, as a
  Lie algebra morphism.
-/

public section

namespace Representation

variable {R K L : Type*} [CommRing R] [Monoid K] [LieRing L] [LieAlgebra R L]

/-- A representation `Ad` of a monoid `K` on a Lie algebra `L` **acts by Lie algebra morphisms**
when every `Ad k` preserves the Lie bracket. -/
class IsLieAction (Ad : Representation R K L) : Prop where
  /-- Every `Ad k` preserves the Lie bracket. -/
  map_lie (k : K) (x y : L) : Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆

/-- A representation whose operators are the linear maps underlying Lie algebra morphisms `φ k`
acts by Lie algebra morphisms. -/
theorem IsLieAction.of_lieHom {Ad : Representation R K L} (φ : K → L →ₗ⁅R⁆ L)
    (h : ∀ k x, φ k x = Ad k x) : IsLieAction Ad where
  map_lie k x y := by simp only [← h, LieHom.map_lie]

/-- A representation whose operators are the linear maps underlying Lie algebra automorphisms
`φ k` acts by Lie algebra morphisms. -/
theorem IsLieAction.of_lieEquiv {Ad : Representation R K L} (φ : K → L ≃ₗ⁅R⁆ L)
    (h : ∀ k x, φ k x = Ad k x) : IsLieAction Ad :=
  .of_lieHom (fun k ↦ (φ k : L →ₗ⁅R⁆ L)) h

/-- The trivial representation acts by Lie algebra morphisms. -/
instance IsLieAction.instTrivial : IsLieAction (Representation.trivial R K L) :=
  .of_lieHom (fun _ ↦ 1) fun _ _ ↦ rfl

/-- Restricting a representation by Lie algebra morphisms along a monoid morphism `f` gives a
representation by Lie algebra morphisms. -/
instance IsLieAction.comp {K' : Type*} [Monoid K'] (Ad : Representation R K L) [IsLieAction Ad]
    (f : K' →* K) : IsLieAction (Ad.comp f) where
  map_lie k := IsLieAction.map_lie (Ad := Ad) (f k)

variable (Ad : Representation R K L) [IsLieAction Ad]

/-- The action of `k` in a representation by Lie algebra morphisms, as a Lie algebra morphism. -/
def toLieHom (k : K) : L →ₗ⁅R⁆ L :=
  { Ad k with map_lie' := IsLieAction.map_lie k _ _ }

@[simp]
theorem toLieHom_apply (k : K) (x : L) : Ad.toLieHom k x = Ad k x :=
  (rfl)

/-- The identity of `K` acts by the identity Lie algebra morphism. -/
@[simp]
theorem toLieHom_one : Ad.toLieHom 1 = LieHom.id :=
  LieHom.ext fun x ↦ by simp

/-- The Lie algebra morphisms of a representation compose as the monoid does. -/
theorem toLieHom_mul (k k' : K) :
    Ad.toLieHom (k * k') = (Ad.toLieHom k).comp (Ad.toLieHom k') :=
  LieHom.ext fun x ↦ by simp

end Representation
