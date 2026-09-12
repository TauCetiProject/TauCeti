/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.Coupling
import TauCeti.Data.ENNReal.Weights
import TauCeti.MeasureTheory.Measure.FiniteMeasure

/-!
# The shift coupling of two weightings of a finite carrier

Two probability measures on a finite carrier that differ by a transfer of weight onto one
designated atom `k₀` -- so that `ν'` is dominated by `ν` everywhere else -- admit a coupling that
moves as little mass as possible: it keeps the matched mass `min (ν {k}) (ν' {k})` at `(k, k)` and
puts the excess `ν {k} - ν' {k}` at `(k, k₀)`.  The mass it places off the diagonal is then exactly
the transferred weight, which is what a cost estimate against the diagonal consumes.

Mathlib has no maximal-coupling construction, and the general one is not needed here: dominance away
from a single atom already pins down where the unmatched mass has to go.

## Main definitions

* `TauCeti.MeasureTheory.shiftCoupling` -- the coupling described above.

## Main results

* `TauCeti.MeasureTheory.shiftCoupling_apply` -- its value on an arbitrary set;
* `TauCeti.MeasureTheory.shiftCoupling_compl_diagonal_le_sum_tsub` -- it puts at most the
  transferred mass off the diagonal;
* `TauCeti.MeasureTheory.isCoupling_shiftCoupling` -- it is a coupling of `ν` and `ν'`.

## References

* `TauCeti/Data/ENNReal/Weights.lean` -- the arithmetic of the two weightings the marginals are
  computed from.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

variable (ν ν' : Measure κ) (k₀ : κ)

/-- The coupling of two weight vectors on a finite carrier that keeps as much mass as possible on
the diagonal and transfers the excess of every other atom to the designated atom `k₀`.

It couples `ν` and `ν'` exactly when `ν'` is dominated by `ν` away from `k₀`
(`isCoupling_shiftCoupling`), and the mass it puts off the diagonal is then the total transferred
weight (`shiftCoupling_compl_diagonal_le_sum_tsub`). -/
def shiftCoupling : Measure (κ × κ) :=
  ∑ k, min (ν {k}) (ν' {k}) • Measure.dirac (k, k) +
    ∑ k, (ν {k} - ν' {k}) • Measure.dirac (k, k₀)

/-- The value of the shift coupling on an arbitrary set: the definition's body is not exposed, so
this is the lemma downstream modules compute with. -/
theorem shiftCoupling_apply (S : Set (κ × κ)) :
    shiftCoupling ν ν' k₀ S =
      ∑ k, min (ν {k}) (ν' {k}) * S.indicator 1 (k, k) +
        ∑ k, (ν {k} - ν' {k}) * S.indicator 1 (k, k₀) := by
  simp only [shiftCoupling, Measure.coe_add, Pi.add_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.of_discrete]

/-- **The shift coupling puts at most the transferred mass off the diagonal.**  The matched mass
sits on the diagonal by construction, and the excess of an atom `k` leaves the diagonal only when
`k ≠ k₀`. -/
theorem shiftCoupling_compl_diagonal_le_sum_tsub :
    shiftCoupling ν ν' k₀ (Set.diagonal κ)ᶜ ≤ ∑ k, (ν {k} - ν' {k}) := by
  rw [shiftCoupling_apply]
  have h1 : ∑ k, min (ν {k}) (ν' {k}) * ((Set.diagonal κ)ᶜ).indicator 1 (k, k) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [Set.indicator_of_notMem (by simp [Set.mem_diagonal_iff]), mul_zero]
  rw [h1, zero_add]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : ((k, k₀) : κ × κ) ∈ ((Set.diagonal κ)ᶜ : Set (κ × κ))
  · rw [Set.indicator_of_mem hk, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hk, mul_zero]
    simp

variable {ν ν' k₀}

/-- **The shift coupling is a coupling.**  Its first marginal is `ν` because the matched mass and
the excess add up at every atom, and its second marginal is `ν'` because the designated atom `k₀`
absorbs exactly the total excess. -/
theorem isCoupling_shiftCoupling [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hdom : ∀ k, k ≠ k₀ → ν' {k} ≤ ν {k}) : IsCoupling ν ν' (shiftCoupling ν ν' k₀) := by
  have hfg : ∑ k, ν {k} = ∑ k, ν' {k} := ν.sum_singleton_eq_one.trans ν'.sum_singleton_eq_one.symm
  have hne : ∑ k, ν {k} ≠ ⊤ := by rw [ν.sum_singleton_eq_one]; exact ENNReal.one_ne_top
  have hdom' : ∀ k ∈ Finset.univ, k ≠ k₀ → ν' {k} ≤ ν {k} := fun k _ hk => hdom k hk
  have hk₀ := le_of_sum_eq_of_forall_ne_le (Finset.mem_univ k₀) hfg hne hdom'
  refine isCoupling_iff.2 ⟨?_, ?_⟩
  · refine Measure.ext_of_singleton fun i => ?_
    rw [Measure.fst_apply (MeasurableSet.singleton i), shiftCoupling_apply]
    have h1 : ∑ k, min (ν {k}) (ν' {k}) * (Prod.fst ⁻¹' ({i} : Set κ)).indicator 1 (k, k)
        = min (ν {i}) (ν' {i}) := by
      refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_).trans ?_
      · intro k _ hk
        rw [Set.indicator_of_notMem (by simpa using hk), mul_zero]
      · rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
    have h2 : ∑ k, (ν {k} - ν' {k}) * (Prod.fst ⁻¹' ({i} : Set κ)).indicator 1 (k, k₀)
        = ν {i} - ν' {i} := by
      refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_).trans ?_
      · intro k _ hk
        rw [Set.indicator_of_notMem (by simpa using hk), mul_zero]
      · rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
    rw [h1, h2]
    exact (add_comm _ _).trans tsub_add_min
  · refine Measure.ext_of_singleton fun i => ?_
    rw [Measure.snd_apply (MeasurableSet.singleton i), shiftCoupling_apply]
    have h1 : ∑ k, min (ν {k}) (ν' {k}) * (Prod.snd ⁻¹' ({i} : Set κ)).indicator 1 (k, k)
        = min (ν {i}) (ν' {i}) := by
      refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_).trans ?_
      · intro k _ hk
        rw [Set.indicator_of_notMem (by simpa using hk), mul_zero]
      · rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
    rcases eq_or_ne k₀ i with rfl | hne
    · have h2 : ∑ k, (ν {k} - ν' {k}) * (Prod.snd ⁻¹' ({k₀} : Set κ)).indicator 1 (k, k₀)
          = ∑ k, (ν {k} - ν' {k}) :=
        Finset.sum_congr rfl fun k _ => by
          rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
      rw [h1, h2, min_eq_left hk₀]
      exact add_sum_tsub_eq_of_forall_ne_le (Finset.mem_univ k₀) hfg hne hdom'
    · have h2 : ∑ k, (ν {k} - ν' {k}) * (Prod.snd ⁻¹' ({i} : Set κ)).indicator 1 (k, k₀)
          = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [Set.indicator_of_notMem (by simpa using hne), mul_zero]
      rw [h1, h2, add_zero]
      exact min_eq_right (hdom i fun e => hne e.symm)

end MeasureTheory

end TauCeti
