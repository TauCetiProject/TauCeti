/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import TauCeti.NumberTheory.NumberField.Units.SUnit.Integer

/-!
# Tests of the unit groups of rings of `S`-integers

The criterion `r₁ + r₂ + |S| ≥ 2` for a unit of infinite order, on its boundary cases.

* Over `ℚ` with `S = ∅`, the count is `1`: every unit of `ℤ` has finite order, and the torsion
  `{±1}` has order `2`.
* Over `ℚ` with one prime `p` in `S`, the count is `2`: `ℤ[1/p]` has a unit of infinite order.
* Over `ℚ(i)` with `S = ∅`, the count is again `1`, since `ℚ(i)` has one complex and no real place:
  every unit of `ℤ[i]` has finite order, and the torsion `{±1, ±i}` has order `4`. Inverting
  primes does not change the torsion.
-/

open IsDedekindDomain NumberField TauCeti.NumberField.SUnit

/-- Over `ℚ` the torsion of the units of every ring of `S`-integers is `{±1}`, of order `2`. -/
example (S : Set (HeightOneSpectrum (RingOfIntegers ℚ))) :
    Nat.card (CommGroup.torsion (S.integer ℚ)ˣ) = 2 := by
  rw [natCard_torsion_units_integer,
    Units.torsionOrder_eq_two_of_odd_finrank (by rw [Module.finrank_self]; decide)]

/-- Every unit of the `∅`-integers of `ℚ` has finite order: `ℚ` has a single infinite place. -/
example : ∀ u : ((∅ : Set (HeightOneSpectrum (RingOfIntegers ℚ))).integer ℚ)ˣ,
    IsOfFinOrder u := by
  by_contra! h
  have := (exists_not_isOfFinOrder_units_integer_iff _).1 h
  simp at this

/-- Inverting one prime of `ℚ` produces a unit of infinite order. -/
example (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    ∃ u : (({v} : Set (HeightOneSpectrum (RingOfIntegers ℚ))).integer ℚ)ˣ, ¬ IsOfFinOrder u :=
  (exists_not_isOfFinOrder_units_integer_iff _).2 (by simp)

section Gaussian

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- Over `ℚ(i)` the torsion of the units of every ring of `S`-integers has order `4`. -/
example (S : Set (HeightOneSpectrum (RingOfIntegers K))) :
    Nat.card (CommGroup.torsion (S.integer K)ˣ) = 4 := by
  rw [natCard_torsion_units_integer, IsCyclotomicExtension.Rat.torsionOrder_eq (n := 4)]
  decide

/-- Every unit of the `∅`-integers of `ℚ(i)` has finite order: `ℚ(i)` has a single infinite
place, which is complex. -/
example : ∀ u : ((∅ : Set (HeightOneSpectrum (RingOfIntegers K))).integer K)ˣ,
    IsOfFinOrder u := by
  by_contra! h
  have := (exists_not_isOfFinOrder_units_integer_iff _).1 h
  rw [Nat.card_eq_fintype_card (α := InfinitePlace K),
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := 4) (by decide),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two K (n := 4)] at this
  simp only [Nat.card_of_isEmpty, zero_add, add_zero] at this
  exact absurd this (by decide)

end Gaussian
