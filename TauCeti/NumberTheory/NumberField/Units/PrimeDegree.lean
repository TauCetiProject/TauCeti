/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Units of a number field of prime degree

In a number field of prime degree, a non-torsion unit lies in no proper subfield, since a unit
with rational value is torsion, and therefore generates `K` over `ℚ`. This is what lets a
statement about integral primitive elements of `K` apply to every non-torsion unit when the
degree is prime.

## Main results

* `TauCeti.NumberField.Units.adjoin_eq_top_of_finrank_prime`: in prime degree, a non-torsion
  unit generates `K` over `ℚ`.
* `TauCeti.NumberField.Units.finrank_prime_of_rank_eq_one_of_isReal`: a number field of unit rank
  one with a real place has prime degree.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped IntermediateField
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Prime degree makes a competing unit a generator.** In a number field of prime degree, a
non-torsion unit generates `K` over `ℚ`. -/
theorem adjoin_eq_top_of_finrank_prime (hp : Nat.Prime (Module.finrank ℚ K)) {v : (𝓞 K)ˣ}
    (hv : v ∉ torsion K) : Algebra.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤ := by
  -- A field of prime degree has no proper subfield, and a non-torsion unit is not rational.
  have h : IntermediateField.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤ :=
    ((IntermediateField.isSimpleOrder_of_finrank_prime ℚ K hp).eq_bot_or_eq_top _).resolve_left
      fun h => hv (mem_torsion_of_mem_bot (h ▸ IntermediateField.mem_adjoin_simple_self ℚ _))
  exact (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic fun x _ =>
    IsAlgebraic.of_finite ℚ x).mp h

/-- A number field of unit rank one with a real infinite place has prime degree: it has two
infinite places, one of them real, so its degree is `2` or `3`. -/
theorem finrank_prime_of_rank_eq_one_of_isReal (hr : rank K = 1) {w : InfinitePlace K}
    (hw : w.IsReal) : Nat.Prime (Module.finrank ℚ K) := by
  have hcard := card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hdeg := card_add_two_mul_card_eq_rank (K := K)
  have hpos : 0 < nrRealPlaces K := Nat.pos_of_ne_zero fun h0 ↦
    (not_isReal_iff_isComplex.2 ((nrRealPlaces_eq_zero_iff.1 h0).isComplex w)) hw
  have hpl : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos_iff.2 ⟨w⟩
  have hr' : Fintype.card (InfinitePlace K) = 2 := by unfold rank at hr; omega
  rw [← hdeg]
  rcases Nat.lt_or_ge (nrComplexPlaces K) 1 with h0 | h1
  · have hc : nrComplexPlaces K = 0 := by omega
    have hrl : nrRealPlaces K = 2 := by omega
    rw [hc, hrl]
    exact Nat.prime_two
  · have hc : nrComplexPlaces K = 1 := by omega
    have hrl : nrRealPlaces K = 1 := by omega
    rw [hc, hrl]
    exact Nat.prime_three

end TauCeti.NumberField.Units
