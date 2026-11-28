/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace.Basic
import TauCeti.Data.ZMod.ReductionFiber

/-!
# Counting cyclotomic infinite places by their labels

For a cyclotomic extension of order `m`, a base with a unique infinite place, an
unramified reference place, and irreducibility of the cyclotomic polynomial give
`InfinitePlace.equivUnitsZMod`. There are then `φ(m)` places. If `q ∣ m` and reduction to
`q` loses no prime factors, each reduced class, including `1`, contains `m / q` places.

These generalize the formulas `New.Parameters.numInfPlaces_E` and
`New.Parameters.card_placeClass_eq_one_eq_towerDeg` in lsernau/grh-lean,
`grh/src/New/Reduction/Data/FieldsAndPlaces.lean` at revision `72fead1`.
-/

public section

namespace NumberField.InfinitePlace

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Subsingleton (InfinitePlace K)]
  {m : ℕ} [IsCyclotomicExtension {m} K L]

/-- Over a base with a unique infinite place, an unramified reference place and irreducibility
of the cyclotomic polynomial give exactly `φ(m)` infinite places at cyclotomic order `m`. -/
theorem natCard_eq_totient_of_isCyclotomicExtension (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic m K)) : Nat.card (InfinitePlace L) = m.totient := by
  let : NeZero m := ⟨by rintro rfl; simp at h⟩
  rw [Nat.card_congr (w.equivUnitsZMod hw h), Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Given the cyclotomic labels relative to `w`, each reduced label modulo `q ∣ m`
occurs at exactly `m / q` infinite places when `m` and `q` have the same prime factors. -/
theorem natCard_unitsMap_equivUnitsZMod_fiber (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic m K)) {q : ℕ} (hd : q ∣ m)
    (hs : m.primeFactors ⊆ q.primeFactors) (a : (ZMod q)ˣ) :
    Nat.card {v : InfinitePlace L // ZMod.unitsMap hd (w.equivUnitsZMod hw h v) = a} = m / q := by
  let : NeZero m := ⟨by rintro rfl; simp at h⟩
  let e := (w.equivUnitsZMod hw h).subtypeEquiv (q := fun u ↦ ZMod.unitsMap hd u = a)
    fun _ ↦ Iff.rfl
  exact (Nat.card_congr e).trans (ZMod.card_unitsMap_fiber_of_primeFactors_subset hd hs a)

end NumberField.InfinitePlace
