/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius
import TauCeti.FieldTheory.IsAlgClosed.Frobenius
import TauCeti.RingTheory.LaurentSeries.DifferenceEquation.Basic

/-!
# Difference equations for coefficient Frobenius on Laurent series

Dividing the multipliers by their common power of `X` reduces solvability to a residue
polynomial. Over an algebraically closed field `k`, this makes every nonzero scalar
twisted polynomial in positive coefficient Frobenius surjective on `k((X))`.

## References

* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004),
  Proposition 3.17, for the use of reduction to a polynomial over the residue field.
-/

public section

open scoped PowerSeries LaurentSeries
open Finset Function HahnSeries

namespace TauCeti.LaurentSeries

variable {p : ℕ} {k : Type*} [Field k] [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- A nonzero scalar twisted polynomial in positive coefficient Frobenius is surjective on
Laurent series over an algebraically closed field. Each index in `s` denotes an iterate
of the same coefficient automorphism. -/
theorem surjective_sum_mul_coefficientFrobenius {f : ℕ} (hf : 0 < f) {s : Finset ℕ}
    (a : ℕ → k⸨X⸩) (ha : ∃ i ∈ s, a i ≠ 0) :
    Surjective (fun x : k⸨X⸩ => ∑ i ∈ s, a i * (coefficientFrobenius p f)^[i] x) := by
  classical
  obtain ⟨j, hj, hmin⟩ := (s.filter fun i => a i ≠ 0).exists_min_image
    (fun i => (a i).order) (by
      obtain ⟨i, hi, hi₀⟩ := ha
      exact ⟨i, mem_filter.mpr ⟨hi, hi₀⟩⟩)
  simp_rw [coefficientFrobenius_iterate, coe_coefficientFrobenius]
  apply surjective_sum_mul_mapRingHom_of_surjective_coeff s a _ (a j).order
  · intro i hi
    rcases eq_or_ne (a i) 0 with hz | hn
    · simp [hz]
    · rw [← order_eq_orderTop_of_ne_zero hn, WithTop.coe_le_coe]
      exact hmin i (mem_filter.mpr ⟨hi, hn⟩)
  · obtain ⟨hjs, hj₀⟩ := mem_filter.mp hj
    exact surjective_sum_mul_iterateFrobenius s _ hf ⟨j, hjs, coeff_order_eq_zero.not.mpr hj₀⟩

end TauCeti.LaurentSeries
