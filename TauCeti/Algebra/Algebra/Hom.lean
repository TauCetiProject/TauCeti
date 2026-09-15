/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `AlgHom`, `RingHom.toAlgebra` and `algebraMap` all occur in the statement below.
public import Mathlib.Algebra.Algebra.Hom

/-!
# Bridging lemmas between `AlgHom` and `RingHom`

Two small families of identities relating the bundled homomorphism types, each of which several
files would otherwise restate inline.

## The structure map of the algebra induced by an algebra homomorphism

An algebra homomorphism `f : A →ₐ[R] B` induces an `A`-algebra structure on `B`, namely
`f.toRingHom.toAlgebra`. Mathlib's `RingHom.algebraMap_toAlgebra` identifies the structure map of
that algebra with the homomorphism it was built from, but states it as an equality of *bundled ring
homomorphisms*. Every consumer that has to feed a hypothesis of the form `∀ z, algebraMap A B z =
f z` therefore applies it pointwise by hand, through `congrArg DFunLike.coe` and `congrFun`.

This file states the pointwise form once, for an `AlgHom`, which is the shape those consumers want:
the right-hand side is `f z` rather than `f.toRingHom z`.

## Functoriality of `RingHom.toIntAlgHom`

Every ring is a `ℤ`-algebra, so a ring homomorphism is a `ℤ`-algebra homomorphism; Mathlib bundles
that as `RingHom.toIntAlgHom` but carries no *named* identity, composition or round-trip lemma for
it; the round-trips are reachable only through `RingHom.equivIntAlgHom`, which is not the shape
`rw` wants. Any file transporting an equality of ring homomorphisms into `AlgHom` needs these, and
several do.

## Main results

* `AlgHom.algebraMap_toAlgebra_apply`: `algebraMap A B z = f z` for the algebra structure
  `f.toRingHom.toAlgebra` induced by `f : A →ₐ[R] B`.
* `RingHom.toIntAlgHom_id`, `RingHom.toIntAlgHom_comp`: `RingHom.toIntAlgHom` is functorial.
* `RingHom.toIntAlgHom_toRingHom`, `AlgHom.toRingHom_toIntAlgHom`: it is inverse to
  `AlgHom.toRingHom` in both directions.

## Implementation notes

### The structure map

The codomain is a `CommSemiring`, not a `Semiring`. That is forced rather than chosen:
`RingHom.toAlgebra` is itself stated for `[CommSemiring R] [CommSemiring S]`
(`Mathlib/Algebra/Algebra/Defs.lean`), so the algebra instance this lemma is about does not exist
over a bare semiring codomain. The `Semiring` version of the construction is `RingHom.toAlgebra'`,
which takes a commutation hypothesis `∀ c x, i c * x = x * i c` and is a different instance; a
lemma about it would not apply to any of the call sites here, all of which build their algebra with
the unprimed `toAlgebra`.

This is original work, not ported: Mathlib carries the un-applied `RingHom.algebraMap_toAlgebra`
but no pointwise `AlgHom` form, though it does carry the analogous `_apply` lemmas for the other
`AlgHom` coercions (`AlgHom.toLinearMap_apply`, `AlgHom.toLieHom_apply`).

### Functoriality of `RingHom.toIntAlgHom`

The two round-trip lemmas are stated through the coercion rather than `.toRingHom`, because
Mathlib's `AlgHom.toRingHom_eq_coe` is a `simp` lemma making the coercion the simp-normal form:
a `.toRingHom` left-hand side is rewritten before the lemma can fire, so the `simp` attribute
would be dead.
-/

public section

/-- **The structure map of `f.toRingHom.toAlgebra` is `f`**, pointwise. Mathlib's
`RingHom.algebraMap_toAlgebra` is the same fact as an equality of bundled ring homomorphisms; this
is the applied form, stated for an `AlgHom` so that the right-hand side is `f z`.

Consumers wanting a hypothesis `∀ z, algebraMap A B z = f z` can pass this lemma directly, since
`z` is explicit. -/
-- Proved from `RingHom.algebraMap_toAlgebra` and `AlgHom.coe_toRingHom` rather than by `rfl`:
-- both sides are definitionally equal, but `rfl` closes the goal only by reducing through
-- `toRingHom`, `toAlgebra`, `algebraMap` and two coercions -- exactly the fragile defeq this
-- lemma exists to spare its call sites.
theorem AlgHom.algebraMap_toAlgebra_apply {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (z : A) :
    @algebraMap A B _ _ f.toRingHom.toAlgebra z = f z := by
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-! ### Functoriality of `RingHom.toIntAlgHom` -/

section ToIntAlgHom

variable {R : Type*} {S : Type*} {T : Type*} [Ring R] [Ring S] [Ring T]

/-- `RingHom.toIntAlgHom` sends the identity ring homomorphism to the identity `ℤ`-algebra
homomorphism. -/
@[simp]
theorem RingHom.toIntAlgHom_id : (RingHom.id R).toIntAlgHom = AlgHom.id ℤ R :=
  AlgHom.ext fun _ ↦ rfl

/-- `RingHom.toIntAlgHom` preserves composition. -/
@[simp]
theorem RingHom.toIntAlgHom_comp (f : S →+* T) (g : R →+* S) :
    (f.comp g).toIntAlgHom = f.toIntAlgHom.comp g.toIntAlgHom :=
  AlgHom.ext fun _ ↦ rfl

/-- Reading a ring homomorphism as a `ℤ`-algebra homomorphism and back recovers it: composing
`AlgHom.toRingHom` after `RingHom.toIntAlgHom` is the identity, so `RingHom.toIntAlgHom` is a
right inverse of `AlgHom.toRingHom`.

Stated through the coercion rather than `.toRingHom`, because Mathlib's `AlgHom.toRingHom_eq_coe`
is a `simp` lemma making the coercion the simp-normal form; a `.toRingHom` left-hand side would
be rewritten before this could fire. -/
@[simp]
theorem RingHom.toIntAlgHom_toRingHom (f : R →+* S) : (f.toIntAlgHom : R →+* S) = f :=
  RingHom.ext fun _ ↦ rfl

/-- Reading a `ℤ`-algebra homomorphism as a ring homomorphism and back recovers it: composing
`RingHom.toIntAlgHom` after `AlgHom.toRingHom` is the identity, so `RingHom.toIntAlgHom` is a
left inverse of `AlgHom.toRingHom`.

Stated through the coercion, for the reason given above. -/
@[simp]
theorem AlgHom.toRingHom_toIntAlgHom (φ : R →ₐ[ℤ] S) : ((φ : R →+* S)).toIntAlgHom = φ :=
  AlgHom.ext fun _ ↦ rfl

end ToIntAlgHom
