/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.Data.Nat.Totient.Multiplication
import TauCeti.Data.ZMod.PrincipalUnits

/-!
# Cardinalities of the cyclotomic place labels

The tower adds no new prime divisors to the base modulus. The total number of place labels
therefore grows by the tower degree, and that degree is also the number of labels of base
class `1`. These are the counts in `New.Data.card_aPlaces` and `New.Data.f_eq_card_aPlaces_mul`
in `New/Reduction/PrimeSums.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
at `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- The totient of the tower modulus is the base totient times the tower degree. -/
theorem totient_q₁ (P : Parameters) (s : ℕ) :
    (P.q₁ s).totient = P.q₀.totient * towerDeg s := by
  rw [q₁_def, Nat.totient_mul_of_primeFactors_subset (P.primeFactors_towerDeg_subset s)]

/-- Exactly `towerDeg s` cyclotomic place labels have base class `1`. -/
theorem card_filter_unitsMap_eq_one (P : Parameters) (s : ℕ) :
    (Finset.univ.filter fun τ ↦ ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1).card = towerDeg s := by
  let π := ZMod.unitsMap (P.q₀_dvd_q₁ s)
  have hker : Nat.card π.ker = (Finset.univ.filter fun τ ↦ π τ = 1).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype _ (fun u ↦ by simp [MonoidHom.mem_ker])
  have h := ZMod.card_ker_unitsMap_mul_totient (P.q₀_dvd_q₁ s)
  rw [hker, P.totient_q₁, Nat.mul_comm P.q₀.totient] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr P.q₀_pos) h

end TauCeti.OneSidedBound.Parameters
