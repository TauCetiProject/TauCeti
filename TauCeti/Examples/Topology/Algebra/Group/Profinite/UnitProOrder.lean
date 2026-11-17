/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder

/-!
# Examples of invertible pro-order

The `p`-adic integers have pro-order invertible in `A` exactly when `p` is a unit of `A`, so
they have it over `ℚ` but not over `ℤ`. The discrete cyclic group `ℤ/p` fails the condition over
`𝔽_p`, and the trivial group satisfies it over every coefficient ring.
-/

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

example (A : Type*) [CommSemiring A] :
    HasUnitProOrder A (Multiplicative ℤ_[p]) ↔ IsUnit (p : A) :=
  (isProP_multiplicative_padicInt p).hasUnitProOrder_iff A

example : HasUnitProOrder ℚ (Multiplicative ℤ_[p]) :=
  (isProP_multiplicative_padicInt p).hasUnitProOrder
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero).isUnit

example : ¬ HasUnitProOrder ℤ (Multiplicative ℤ_[p]) := by
  rw [(isProP_multiplicative_padicInt p).hasUnitProOrder_iff ℤ, Int.isUnit_iff]
  have := (Fact.out : p.Prime).two_le
  omega

example : ¬ HasUnitProOrder (ZMod p) (Multiplicative (ZMod p)) := by
  rw [hasUnitProOrder_iff_isUnit_card, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card, ZMod.natCast_self]
  exact not_isUnit_zero

example (A : Type*) [CommSemiring A] : HasUnitProOrder A Unit :=
  hasUnitProOrder_of_subsingleton A

end TauCeti
