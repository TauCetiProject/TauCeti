/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.Data.Nat.Totient
import TauCeti.Data.ZMod.ReductionFiber

/-!
# Cardinalities of cyclotomic place labels

There are `towerDeg s * φ(q₀)` unit labels at level `q₁ s`, and exactly `towerDeg s`
of them over each unit class modulo `q₀`. In particular the identity class, used to
index the averaging set for the one-sided prime sum, occupies a fraction `1/φ(q₀)`
of all labels.

## References

* `New.Parameters.numInfPlaces_E` and `New.Parameters.card_placeClass_eq_one_eq_towerDeg`,
  `grh/src/New/Reduction/Data/FieldsAndPlaces.lean` of https://github.com/lsernau/grh-lean
  at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- The cyclotomic tower introduces no new prime factors of the level. -/
@[simp] theorem primeFactors_q₁ (P : Parameters) (s : ℕ) :
    (P.q₁ s).primeFactors = P.q₀.primeFactors := by
  refine Finset.Subset.antisymm (fun p hp ↦ ?_) (Nat.primeFactors_mono (P.q₀_dvd_q₁ s)
    (P.q₁_pos s).ne')
  obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp, P.dvd_q₀_of_dvd_q₁ hp hdvd, P.q₀_ne_zero⟩

/-- The total number of unit labels at level `q₁ s` is `towerDeg s` times the number at `q₀`. -/
theorem totient_q₁ (P : Parameters) (s : ℕ) :
    (P.q₁ s).totient = towerDeg s * P.q₀.totient := by
  have hdvd : towerDeg s ∣ P.q₁ s := (P.q₁_def s).symm ▸ dvd_mul_left _ _
  have hs : (towerDeg s).primeFactors ⊆ P.q₀.primeFactors :=
    P.primeFactors_q₁ s ▸ Nat.primeFactors_mono hdvd (P.q₁_pos s).ne'
  exact (P.q₁_def s).symm ▸ Nat.totient_mul_of_primeFactors_subset hs

/-- Every unit class modulo `q₀` labels exactly `towerDeg s` units at level `q₁ s`. -/
theorem card_unitsMap_q₁_fiber (P : Parameters) (s : ℕ) (u : (ZMod P.q₀)ˣ) :
    Nat.card {v : (ZMod (P.q₁ s))ˣ // ZMod.unitsMap (P.q₀_dvd_q₁ s) v = u} = towerDeg s := by
  calc
    _ = P.q₁ s / P.q₀ := ZMod.card_unitsMap_fiber_of_primeFactors_subset (P.q₀_dvd_q₁ s)
      (P.primeFactors_q₁ s).le u
    _ = towerDeg s := by rw [P.q₁_def, Nat.mul_div_cancel_left _ P.q₀_pos]

end TauCeti.OneSidedBound.Parameters
