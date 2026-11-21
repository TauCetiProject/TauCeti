/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Subalgebras of Artinian algebras are Artinian rings

If an `R`-algebra `A` is Artinian as an `R`-module, then every subalgebra `S` of `A` is an
Artinian ring: each ideal of `S` is an `R`-submodule of `A`, so a descending chain of ideals
stabilises. In particular, every subalgebra of a module-finite algebra over an Artinian
commutative ring is Artinian, as is, for instance, the centre of the monoid algebra `K[G]` of a
finite monoid `G` over an Artinian commutative ring `K`.

The Artinian centre supplies the structure theory used to split the centre of a finite group
algebra into its residue fields.
-/

public section

/-- A subalgebra of an algebra that is Artinian as a module over the base ring is an Artinian
ring. -/
instance Subalgebra.isArtinianRing {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [IsArtinian R A] (S : Subalgebra R A) : IsArtinianRing S :=
  isArtinian_of_tower R (isArtinian_submodule' S.toSubmodule)
