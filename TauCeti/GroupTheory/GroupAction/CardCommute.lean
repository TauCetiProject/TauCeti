/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.GroupTheory.GroupAction.CardCommute

/-!
# The class formula with orbit-wise stabilizer orders

Complements to `Mathlib.GroupTheory.GroupAction.CardCommute`. Mathlib's class formula
`MulAction.card_eq_sum_card_group_div_card_stabilizer` expresses the size of a finite `G`-set as a
sum over the orbits of `|G| / |G_x|`, with the stabilizer taken at a chosen representative `x` and
the division in `ℕ`. Since `|G_x|` divides `|G|`, the formula holds equally in any division
semiring of characteristic zero, and there the stabilizer order is best read as the function
`TauCeti.cardStabilizerOnOrbit` on the orbit space. This is the form in which weighted orbit counts,
such as the pole-orbit equation for finite rotation groups, are manipulated.

## Main results

* `TauCeti.card_eq_finsum_card_group_div_cardStabilizerOnOrbit`: the class formula
  `|X| = Σ_ω |G| / |G_ω|` in a division semiring of characteristic zero.
-/

public section

open MulAction

namespace TauCeti

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The class formula**, in a division semiring `𝕜` of characteristic zero: a finite `G`-set
`α`, for a finite group `G`, has `Σ_ω |G| / |G_ω|` points, the sum running over the orbits `ω` and
`|G_ω|` being the order of the stabilizer of any point of `ω`. -/
theorem card_eq_finsum_card_group_div_cardStabilizerOnOrbit (𝕜 : Type*) [DivisionSemiring 𝕜]
    [CharZero 𝕜] [Finite G] [Finite α] :
    (Nat.card α : 𝕜) =
      ∑ᶠ ω : orbitRel.Quotient G α, (Nat.card G : 𝕜) / cardStabilizerOnOrbit ω := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite α
  have := Fintype.ofFinite (orbitRel.Quotient G α)
  rw [finsum_eq_sum_of_fintype, ← Fintype.card_eq_nat_card,
    card_eq_sum_card_group_div_card_stabilizer G α, Nat.cast_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.cast_div (Subgroup.card_subgroup_dvd_card _) (Nat.cast_ne_zero.mpr Nat.card_pos.ne'),
    ← cardStabilizerOnOrbit_mk, Quotient.out_eq']

end TauCeti
