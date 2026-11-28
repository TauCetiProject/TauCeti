/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Divisible.Rat
public import TauCeti.GroupTheory.Divisible.Units
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed

/-!
# Units of absolutely integrally closed rings

Every unit of an absolutely integrally closed ring `D` has an `n`-th root for every `n ≠ 0`, and
that root is again a unit, so the unit group `Dˣ` is `ℕ`-rootable. Hence every unit `x` of `D` is
`r (ofAdd 1)` for a homomorphism `r : Multiplicative ℚ →* Dˣ`: a compatible system of roots of
`x`. More precisely, `TauCeti.factorialRootsEquiv` identifies such homomorphisms with the
compatible systems of factorial roots `y (n + 1) ^ (n + 1) = y n` in `Dˣ`, and every unit starts
one.

## Main results

* `TauCeti.IsAbsolutelyIntegrallyClosed.unitsRootableByNat`: the unit group of an absolutely
  integrally closed ring is `ℕ`-rootable. Like `TauCeti.IsAlgClosed.unitsRootableByNat` it is
  built with `TauCeti.unitsRootableByNatOfExistsPow`, so for an algebraically closed field the two
  instances agree definitionally.
* `Units.exists_monoidHom_rat_apply_ofAdd_one`: every unit `x` of an absolutely integrally closed
  ring is `r (ofAdd 1)` for a homomorphism `r : Multiplicative ℚ →* Dˣ`.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `Lib/PadicComparison/ToricTower`, declarations
  `New.Variety.compatibleRoots` and `New.Variety.compatibleRootsAt`, and file
  `Lib/PadicComparison/Descent/TestCategory`, declaration `New.Variety.exists_compatible_roots`.
-/

public section

open Multiplicative

variable {D : Type*} [CommRing D] [TauCeti.IsAbsolutelyIntegrallyClosed D]

namespace TauCeti.IsAbsolutelyIntegrallyClosed

/-- The unit group of an absolutely integrally closed ring is `ℕ`-rootable: an `n`-th root of a
unit, which exists in the ring, is a unit. -/
noncomputable instance unitsRootableByNat : RootableBy Dˣ ℕ :=
  unitsRootableByNatOfExistsPow fun _ hn x ↦ exists_pow_nat_eq (x : D) (Nat.pos_of_ne_zero hn)

end TauCeti.IsAbsolutelyIntegrallyClosed

/-- Every unit `x` of an absolutely integrally closed ring `D` is `r (ofAdd 1)` for a homomorphism
`r : Multiplicative ℚ →* Dˣ`, that is, from `(ℚ, +)` to the unit group. -/
theorem Units.exists_monoidHom_rat_apply_ofAdd_one (x : Dˣ) :
    ∃ r : Multiplicative ℚ →* Dˣ, r (ofAdd 1) = x :=
  TauCeti.exists_monoidHom_rat_apply_ofAdd_one x
