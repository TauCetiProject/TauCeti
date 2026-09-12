/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Iterated Frobenius on units

Let `A` be a commutative semiring of exponential characteristic `p`. The `p ^ n`-power Frobenius
`iterateFrobenius A p n` is a ring homomorphism, so it acts on the units of `A` through
`Units.map`, and that action is the `p ^ n`-th power map. This file records that, pointwise and
coordinatewise along a family, because the coordinatewise form is what a split torus of a
Chevalley carrier meets when its Frobenius is computed on weight-torus points.

Nothing here is about the fixed locus of the Frobenius; for the subring and subfield it fixes, see
`TauCeti.Algebra.CharP.Frobenius.Fixed`.

## Main results

* `TauCeti.map_iterateFrobenius_unit_eq_pow`: `Units.map (iterateFrobenius A p n) u = u ^ p ^ n`.
* `TauCeti.map_iterateFrobenius_units_eq_pow`: the same coordinatewise along a family of units.
-/

public section

namespace TauCeti

variable (A : Type*) [CommSemiring A] (p n : ℕ) [ExpChar A p]

/-- The `p ^ n`-power Frobenius acts on a unit as the `p ^ n`-th power map. -/
@[simp]
theorem map_iterateFrobenius_unit_eq_pow (u : Aˣ) :
    Units.map (iterateFrobenius A p n : A →* A) u = u ^ p ^ n :=
  Units.ext (by
    rw [Units.coe_map, MonoidHom.coe_coe, iterateFrobenius_def, Units.val_pow_eq_pow_val])

/-- Applying the `p ^ n`-power Frobenius to each coordinate of a family of units raises the family
to its `p ^ n`-th power. This is the coordinatewise form of
`TauCeti.map_iterateFrobenius_unit_eq_pow`, which is the shape a torus calculation meets it in. -/
theorem map_iterateFrobenius_units_eq_pow {ι : Type*} (s : ι → Aˣ) :
    (fun i => Units.map (iterateFrobenius A p n : A →* A) (s i)) = s ^ p ^ n :=
  funext fun i => (map_iterateFrobenius_unit_eq_pow A p n (s i)).trans (Pi.pow_apply s _ i).symm

end TauCeti
