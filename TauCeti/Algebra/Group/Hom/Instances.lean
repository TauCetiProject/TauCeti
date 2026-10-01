/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Precomposition with a bijective homomorphism

For a homomorphism `f : M →* N` and a commutative monoid `P`, Mathlib's `MonoidHom.compHom' f` is
precomposition with `f`, as a homomorphism `(N →* P) →* M →* P`. This file records that it is
bijective as soon as `f` is: `Hom(-, P)` takes isomorphisms to isomorphisms. The bundled form of
this fact is Mathlib's `MulEquiv.monoidHomCongrLeft`; the statement here is the one to use when
the isomorphism is given as a homomorphism known to be bijective, and the precomposition map is
the unbundled `compHom'`.

## Main results

* `MonoidHom.compHom'_bijective`, `AddMonoidHom.compHom'_bijective`: precomposition with a bijective
  homomorphism is bijective on homomorphisms into a commutative monoid.
-/

public section

namespace TauCeti

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [CommMonoid P]

/-- Precomposition with a bijective homomorphism is bijective on homomorphisms into a commutative
monoid: `Hom(-, P)` takes isomorphisms to isomorphisms. The inverse is precomposition with the
inverse bijection. -/
@[to_additive /-- Precomposition with a bijective homomorphism is bijective on homomorphisms into
a commutative additive monoid: `Hom(-, P)` takes isomorphisms to isomorphisms. The inverse is
precomposition with the inverse bijection. -/]
theorem _root_.MonoidHom.compHom'_bijective {f : M →* N} (hf : Function.Bijective f) :
    Function.Bijective (MonoidHom.compHom' f : (N →* P) →* M →* P) :=
  ⟨fun φ ψ h => MonoidHom.ext fun n => by
      obtain ⟨m, rfl⟩ := hf.2 n
      exact DFunLike.congr_fun h m,
    fun χ => ⟨χ.comp (MulEquiv.ofBijective f hf).symm.toMonoidHom, MonoidHom.ext fun m =>
      congrArg χ ((MulEquiv.ofBijective f hf).symm_apply_apply m)⟩⟩

end TauCeti
