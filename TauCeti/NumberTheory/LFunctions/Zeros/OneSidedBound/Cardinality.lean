/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace.Basic
import TauCeti.Data.Nat.Totient.PrimeSupport
import TauCeti.Data.ZMod.ReductionFiber

/-!
# Cardinalities of cyclotomic place classes

In the tower `q₁ = q₀ * T`, all primes dividing `T` divide `q₀`. Thus the unit labels, and hence
the infinite places over the imaginary quadratic base, have `T` members in each reduced class
modulo `q₀`. In particular the class of `1` used in place-averaged prime sums has size `T`, and
the total number of places is `φ(q₀) * T`.

The place counts follow the statements `New.Parameters.numInfPlaces_E` and
`New.Parameters.card_placeClass_eq_one_eq_towerDeg` in
[`New/Reduction/Data/FieldsAndPlaces.lean`][fields] of lsernau/grh-lean.

[fields]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/FieldsAndPlaces.lean
-/

public section

open NumberField Polynomial

namespace TauCeti.OneSidedBound.Parameters

/-- There are `T` cyclotomic labels of any fixed reduced class modulo `q₀`. The class of one
is the index set of the short-cutoff place average. -/
@[simp]
theorem card_place_class_eq_towerDeg (P : Parameters) (s : ℕ) (a : (ZMod P.q₀)ˣ) :
    (Finset.univ.filter fun u ↦ ZMod.unitsMap (P.q₀_dvd_q₁ s) u = a).card = towerDeg s := by
  have hs : (P.q₁ s).primeFactors ⊆ P.q₀.primeFactors := by
    rw [P.q₁_def, Nat.primeFactors_mul P.q₀_ne_zero (towerDeg_pos s).ne',
      Finset.union_eq_left.mpr (P.primeFactors_towerDeg_subset s)]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ZMod.natCard_unitsMap_fiber_eq_of_primeFactors_subset (P.q₀_dvd_q₁ s) hs,
    P.q₁_def, Nat.mul_div_cancel_left _ P.q₀_pos]

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Subsingleton (InfinitePlace K)]

/-- A cyclotomic extension of order `q₁` with the full cyclotomic place labeling has
`φ(q₀) * T` infinite places. -/
theorem natCard_infinitePlace (P : Parameters) (s : ℕ) [IsCyclotomicExtension {P.q₁ s} K L]
    (w : InfinitePlace L) (hw : w.IsUnramified K) (h : Irreducible (cyclotomic (P.q₁ s) K)) :
    Nat.card (InfinitePlace L) = P.q₀.totient * towerDeg s := by
  rw [Nat.card_congr (w.equivUnitsZMod hw h), Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, P.q₁_def]
  exact Nat.totient_mul_of_primeFactors_subset (P.primeFactors_towerDeg_subset s)

/-- A reduced class modulo `q₀` labels exactly `T` infinite places of the extension of order
`q₁`. The label is relative to the reference place `w`. -/
theorem natCard_infinitePlace_class_eq_towerDeg (P : Parameters) (s : ℕ)
    [IsCyclotomicExtension {P.q₁ s} K L] (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic (P.q₁ s) K)) (a : (ZMod P.q₀)ˣ) :
    Nat.card {v // ZMod.unitsMap (P.q₀_dvd_q₁ s) (w.equivUnitsZMod hw h v) = a} = towerDeg s := by
  let e := (w.equivUnitsZMod hw h).subtypeEquiv
    (q := fun u ↦ ZMod.unitsMap (P.q₀_dvd_q₁ s) u = a) fun _ ↦ Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    P.card_place_class_eq_towerDeg s a]

end TauCeti.OneSidedBound.Parameters
