/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finiteness properties of the centre of a finite monoid algebra

For a finite monoid `G`, the centre of `K[G]` is finite when `K` is a finite commutative
semiring, and Artinian when `K` is an Artinian commutative ring. Neither assertion requires
inverses in `G` or a class-sum basis for the centre.

The Artinian instance supplies the structure theory used to split the centre of a finite group
algebra into its residue fields.
-/

public section

namespace TauCeti

/-- The centre of a finite monoid algebra over a finite commutative semiring is finite. -/
instance instFiniteCenterMonoidAlgebra (K G : Type*) [CommSemiring K] [Finite K] [Monoid G]
    [Finite G] : Finite (Subalgebra.center K (MonoidAlgebra K G)) := by
  have : Finite (MonoidAlgebra K G) := Module.finite_of_finite K
  infer_instance

/-- The centre of a finite monoid algebra over an Artinian commutative ring is Artinian. -/
instance instIsArtinianRingCenterMonoidAlgebra (K G : Type*) [CommRing K] [IsArtinianRing K]
    [Monoid G] [Finite G] : IsArtinianRing (Subalgebra.center K (MonoidAlgebra K G)) := by
  have : IsArtinian K (MonoidAlgebra K G) :=
    isArtinian_of_linearEquiv (MonoidAlgebra.coeffLinearEquiv K).symm
  exact isArtinian_of_tower K
    (isArtinian_submodule' (Subalgebra.center K (MonoidAlgebra K G)).toSubmodule)

end TauCeti
