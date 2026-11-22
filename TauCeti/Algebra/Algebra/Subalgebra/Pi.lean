/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Units in subalgebras of integral and finite products

Let `O` be a commutative ring, `B : ι → Type*` a family of commutative `O`-algebras such that
`∏ i, B i` is integral over `O`, and `A : Subalgebra O (∀ i, B i)` an `O`-subalgebra. Since
`O → ∏ i, B i` is integral, the inclusion `A ↪ ∏ i, B i` is also integral and injective, hence a
local homomorphism (`RingHom.IsIntegral.isLocalHom`). Therefore an element `y ∈ A` is a unit in `A`
(and not merely in the ambient product) if and only if every coordinate `y i` is a unit in `B i`.

In particular, when `ι` is finite and each `B i` is a finite `O`-module, the product `∀ i, B i` is
finite and hence integral over `O`, yielding the finite-product criterion `Subalgebra.isUnit_iff`
and the homogeneous finite-product criterion `Subalgebra.isUnit_iff_isUnit_prod`.

## Main results

* `Subalgebra.isUnit_iff_of_isIntegral`: an element of a subalgebra of an integral product algebra
  `∀ i, B i` is a unit if and only if all of its coordinates are units.
* `Subalgebra.isUnit_iff`: an element of a subalgebra of a finite product `∀ i, B i` of finite
  `O`-algebras is a unit if and only if all of its coordinates are units.
* `Subalgebra.isUnit_iff_isUnit_prod`: product criterion for units in a subalgebra of `ι → B` for
  a finite `O`-algebra `B` (in particular `ι → O`).
-/

public section

namespace Subalgebra

variable {O ι : Type*} [CommRing O]

/-- **Units in a subalgebra of an integral product algebra**: if `∀ i, B i` is integral over `O`
and `A : Subalgebra O (∀ i, B i)`, an element `y ∈ A` is a unit in `A` if and only if every
coordinate `y i` is a unit in `B i`. -/
theorem isUnit_iff_of_isIntegral {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra O (B i)]
    [Algebra.IsIntegral O (∀ i, B i)] {A : Subalgebra O (∀ i, B i)} {y : A} :
    IsUnit y ↔ ∀ i : ι, IsUnit ((y : ∀ i, B i) i) := by
  have hint : (A.val : A →+* ∀ i, B i).IsIntegral :=
    RingHom.IsIntegral.tower_top (algebraMap O A) (A.val : A →+* ∀ i, B i) <| by
      simpa [A.val.comp_algebraMap] using
        (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral O (∀ i, B i)))
  have : IsLocalHom (A.val : A →+* ∀ i, B i) := hint.isLocalHom Subtype.val_injective
  exact (isUnit_map_iff (A.val : A →+* ∀ i, B i) y).symm.trans Pi.isUnit_iff

/-- **Units in a subalgebra of a finite product**: for a finite index type `ι`, finite
`O`-algebras `B i`, and a subalgebra `A : Subalgebra O (∀ i, B i)`, an element `y ∈ A` is a unit in
`A` if and only if every coordinate `y i` is a unit in `B i`. -/
theorem isUnit_iff [Finite ι] {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra O (B i)]
    [∀ i, Module.Finite O (B i)] {A : Subalgebra O (∀ i, B i)} {y : A} :
    IsUnit y ↔ ∀ i : ι, IsUnit ((y : ∀ i, B i) i) := by
  have : Algebra.IsIntegral O (∀ i, B i) := Algebra.IsIntegral.of_finite O (∀ i, B i)
  exact isUnit_iff_of_isIntegral

/-- **Product criterion for units in a subalgebra of a finite product**: for a finite index type
`ι`, a finite `O`-algebra `B`, and `A : Subalgebra O (ι → B)`, `y ∈ A` is a unit in `A` if and only
if the product `∏ i, y i` is a unit in `B`. -/
theorem isUnit_iff_isUnit_prod [Fintype ι] {B : Type*} [CommRing B] [Algebra O B]
    [Module.Finite O B] {A : Subalgebra O (ι → B)} {y : A} :
    IsUnit y ↔ IsUnit (∏ i : ι, (y : ι → B) i) := by
  rw [isUnit_iff, IsUnit.prod_univ_iff]

end Subalgebra
