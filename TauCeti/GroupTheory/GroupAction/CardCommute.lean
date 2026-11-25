/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Field.Defs
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.GroupTheory.GroupAction.CardCommute
import TauCeti.SetTheory.Cardinal.Finite

/-!
# The class formula with orbit-wise stabilizer orders

Complements to `Mathlib.GroupTheory.GroupAction.CardCommute`. Mathlib's class formula
`MulAction.card_eq_sum_card_group_div_card_stabilizer` expresses the size of a finite `G`-set as a
sum over the orbits of `|G| / |G_x|`, with the stabilizer taken at a chosen representative `x` and
the division in `ℕ`. Since `|G_x|` divides `|G|`, the formula holds equally in any division
semiring in which `|G|` is nonzero, and there the stabilizer order is best read as the function
`TauCeti.cardStabilizerOnOrbit` on the orbit space. This is the form in which weighted orbit counts,
such as the pole-orbit equation for finite rotation groups, are manipulated.

## Main results

* `TauCeti.card_eq_finsum_card_group_div_cardStabilizerOnOrbit`: the class formula
  `|X| = Σ_ω |G| / |G_ω|` in a division semiring in which `|G|` is nonzero.
-/

public section

open MulAction

namespace TauCeti

variable (G α : Type*) [Group G] [MulAction G α]

/-- **The class formula**, in a division semiring `𝕜` in which the order of `G` is nonzero: a
`G`-set `α` has `Σ_ω |G| / |G_ω|` points, the sum running over the orbits `ω` and `|G_ω|` being
the order of the stabilizer of any point of `ω`. The hypothesis forces `G` to be finite; if `α` is
infinite, then so is the set of orbits, and both sides are `0`. -/
theorem card_eq_finsum_card_group_div_cardStabilizerOnOrbit (𝕜 : Type*) [DivisionSemiring 𝕜]
    [NeZero (Nat.card G : 𝕜)] :
    (Nat.card α : 𝕜) =
      ∑ᶠ ω : orbitRel.Quotient G α, (Nat.card G : 𝕜) / cardStabilizerOnOrbit ω := by
  classical
  have hG : (Nat.card G : 𝕜) ≠ 0 := NeZero.ne _
  have := finite_of_natCast_card_ne_zero hG
  -- The order of a stabilizer divides `|G|`, so it is nonzero in `𝕜` as well.
  have hstab (ω : orbitRel.Quotient G α) : (cardStabilizerOnOrbit ω : 𝕜) ≠ 0 := fun h ↦ by
    obtain ⟨k, hk⟩ := cardStabilizerOnOrbit_dvd_card ω
    exact hG (by rw [hk, Nat.cast_mul, h, zero_mul])
  cases finite_or_infinite α with
  | inr hα =>
    -- A finite group has finite orbits, so there are infinitely many orbits.
    have : Infinite (orbitRel.Quotient G α) :=
      ⟨fun _ ↦ hα.not_finite (Finite.of_finite_mulAction_orbitRel_quotient G α)⟩
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, finsum_of_infinite_support]
    rw [Function.support_eq_univ fun ω ↦ div_ne_zero hG (hstab ω)]
    exact Set.infinite_univ
  | inl hα =>
    have := Fintype.ofFinite G
    have := Fintype.ofFinite α
    have := Fintype.ofFinite (orbitRel.Quotient G α)
    rw [finsum_eq_sum_of_fintype, ← Fintype.card_eq_nat_card,
      card_eq_sum_card_group_div_card_stabilizer G α, Nat.cast_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, ← cardStabilizerOnOrbit_mk,
      Quotient.out_eq', Nat.cast_div (cardStabilizerOnOrbit_dvd_card ω) (hstab ω)]

end TauCeti
