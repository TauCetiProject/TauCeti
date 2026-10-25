/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# The order-twelve Burnside test

The alternating group on four letters has order twelve. Its solvability follows here through
Burnside's `pᵃqᵇ` theorem with `p = 2`, `a = 2`, `q = 3`, `b = 1`, rather than through a
pre-existing solvability instance.

-/

public section

namespace TauCeti

/-- The alternating group `A₄`, of order `2² · 3`, is solvable. -/
example :
    Group.IsSolvable (alternatingGroup (Fin 4)) := by
  apply isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 2) (b := 1) (by decide) (by decide)
  exact alternatingGroup.card_of_card_eq_four
    (α := Fin 4) (by simp only [Nat.card_eq_fintype_card, Fintype.card_fin])

end TauCeti
