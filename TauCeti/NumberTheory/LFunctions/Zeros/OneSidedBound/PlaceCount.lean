/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace.Basic
import Mathlib.GroupTheory.Coset.Basic
import TauCeti.Data.Nat.Totient.PrimeFactors
import TauCeti.Data.ZMod.PrincipalUnits

/-!
# Counts of cyclotomic place classes

At level `q₁(s) = q₀ T(s)`, each unit class modulo `q₀` is the reduction of exactly `T(s)`
unit labels. When the infinite places of the cyclotomic extension are labeled by these units,
this counts the places in each class, in particular the classes `1` and `-1` used for the two
cutoffs of the signed prime sum.

The count is that of `New.Parameters.numInfPlaces_E` and
`New.Parameters.card_placeClass_eq_one_eq_towerDeg` in `New/Reduction/Data/FieldsAndPlaces.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

namespace TauCeti.OneSidedBound.Parameters

open NumberField Polynomial

/-- The cyclotomic label set has size `T(s) φ(q₀)`: passing to `q₁(s)` adds no new prime factors. -/
theorem totient_q₁ (P : Parameters) (s : ℕ) : (P.q₁ s).totient = towerDeg s * P.q₀.totient := by
  rw [P.q₁_def]
  apply Nat.totient_mul_eq_mul_totient_of_primeFactors_subset
  intro p hp
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have h₁ : p ∣ P.q₁ s := P.q₁_def s ▸ hpd.mul_left P.q₀
  exact Nat.mem_primeFactors.mpr ⟨hp, P.dvd_q₀_of_dvd_q₁ hp h₁, P.q₀_ne_zero⟩

/-- Each unit class modulo `q₀` has exactly `T(s)` lifts to a unit class modulo `q₁(s)`. -/
theorem natCard_fiber_unitsMap_q₁ (P : Parameters) (s : ℕ) (a : (ZMod P.q₀)ˣ) :
    Nat.card {u : (ZMod (P.q₁ s))ˣ // ZMod.unitsMap (P.q₀_dvd_q₁ s) u = a} = towerDeg s := by
  let h := P.q₀_dvd_q₁ s
  calc
    _ = Nat.card (ZMod.unitsMap h).ker :=
      Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective (ZMod.unitsMap_surjective h) a)
    _ = towerDeg s := Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr P.q₀_pos) <|
      (ZMod.card_ker_unitsMap_mul_totient h).trans (P.totient_q₁ s)

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Subsingleton (InfinitePlace K)]

/-- The cyclotomic extension over a base with one infinite place has `T(s) φ(q₀)` infinite places
if the cyclotomic polynomial remains irreducible and a basepoint is unramified. -/
theorem natCard_infinitePlace (P : Parameters) {s : ℕ} [IsCyclotomicExtension {P.q₁ s} K E]
    (w : InfinitePlace E) (hw : w.IsUnramified K) (hirr : Irreducible (cyclotomic (P.q₁ s) K)) :
    Nat.card (InfinitePlace E) = towerDeg s * P.q₀.totient := by
  calc
    _ = Nat.card (ZMod (P.q₁ s))ˣ := Nat.card_congr (w.equivUnitsZMod hw hirr)
    _ = _ := by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, P.totient_q₁ s]

/-- Every class modulo `q₀` contains exactly `T(s)` infinite places, using cyclotomic labels
relative to an unramified basepoint. -/
theorem natCard_infinitePlace_class (P : Parameters) {s : ℕ} [IsCyclotomicExtension {P.q₁ s} K E]
    (w : InfinitePlace E) (hw : w.IsUnramified K) (hirr : Irreducible (cyclotomic (P.q₁ s) K))
    (a : (ZMod P.q₀)ˣ) :
    Nat.card {v : InfinitePlace E //
      ZMod.unitsMap (P.q₀_dvd_q₁ s) (w.equivUnitsZMod hw hirr v) = a} = towerDeg s := by
  rw [← P.natCard_fiber_unitsMap_q₁ s a]
  exact Nat.card_congr ((w.equivUnitsZMod hw hirr).subtypeEquiv fun _ ↦ Iff.rfl)

end TauCeti.OneSidedBound.Parameters
