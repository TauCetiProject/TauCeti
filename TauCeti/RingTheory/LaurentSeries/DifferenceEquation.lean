/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius

import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear
import TauCeti.FieldTheory.IsAlgClosed.Frobenius
import TauCeti.RingTheory.PowerSeries.Basic

/-!
# Difference equations for coefficient maps on Laurent series

Dividing the multipliers of a finite sum of coefficient maps by a common power of `X`
reduces solvability to a power-series equation. Over an algebraically closed residue field
`k`, this makes every nonzero scalar twisted polynomial in positive coefficient Frobenius
surjective on `k((X))`.

On a finite-dimensional vector space over `k((X))` with semilinear endomorphism `Φ`
for this Frobenius, a dependence among iterates and a telescoping sum give surjectivity
of `Φ - 1`. Applied to the space of linear maps into the kernel of an isocrystal
epimorphism, this lets one correct a linear section to a Frobenius-equivariant section.

## References

* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004),
  Proposition 3.17, for the use of reduction to a polynomial over the residue field.
-/

public section

open scoped PowerSeries LaurentSeries
open Finset Function HahnSeries

namespace TauCeti.LaurentSeries

/-- A finite sum of coefficient maps with Laurent-series multipliers acts surjectively if
the multipliers have a common lower exponent `m` and their coefficients there give a
surjective equation on the coefficient ring. -/
theorem surjective_sum_mul_mapRingHom_of_surjective_coeff {R ι : Type*} [Ring R]
    (s : Finset ι) (a : ι → R⸨X⸩) (τ : ι → R →+* R) (m : ℤ)
    (hm : ∀ i ∈ s, (m : WithTop ℤ) ≤ (a i).orderTop)
    (hlead : Surjective (fun x => ∑ i ∈ s, (a i).coeff m * τ i x)) :
    Surjective (fun x : R⸨X⸩ => ∑ i ∈ s, a i * mapRingHom (τ i) x) := by
  let A (i : ι) := PowerSeries.mk fun n => (a i).coeff (n + m)
  have hA (i : ι) (hi : i ∈ s) :
      (A i : R⸨X⸩) = single (-m) 1 * a i := by
    ext j
    rw [PowerSeries.coeff_coe, coeff_single_mul, one_mul, sub_neg_eq_add]
    split_ifs with hj
    · exact (le_orderTop_iff_forall.mp (hm i hi) _ (WithTop.coe_lt_coe.mpr (by omega))).symm
    · simp [A, abs_of_nonneg (le_of_not_gt hj)]
  have hconst (i : ι) : PowerSeries.constantCoeff (A i) = (a i).coeff m := by
    simp [A, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  intro b
  obtain ⟨x, hx⟩ := TauCeti.surjective_sum_mul_map_of_surjective_constantCoeff s A τ
    (by simpa only [hconst] using hlead) b.powerSeriesPart
  let d := b.order - m
  refine ⟨single d 1 * (x : R⸨X⸩), ?_⟩
  have hshift : (single b.order 1 : R⸨X⸩) * single (-m) 1 = single d 1 := by
    rw [single_mul_single, one_mul, ← sub_eq_add_neg]
  have hcomm (i : ι) : Commute (a i) (single d 1) := by
    ext j
    simp only [coeff_mul_single, coeff_single_mul, one_mul, mul_one]
  calc
    _ = single b.order 1 * (b.powerSeriesPart : R⸨X⸩) := by
      rw [← hx, map_sum, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      simp only [map_mul, mapRingHom_single, map_one, hA i hi]
      rw [mapRingHom_apply, map_ofPowerSeries]
      rw [← mul_assoc, (hcomm i).eq, ← hshift]
      simp only [mul_assoc]
    _ = b := b.single_order_mul_powerSeriesPart

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
  simp_rw [coefficientFrobenius_iterate, coefficientFrobenius_apply]
  apply surjective_sum_mul_mapRingHom_of_surjective_coeff s a _ (a j).order
  · intro i hi
    rcases eq_or_ne (a i) 0 with hz | hn
    · simp [hz]
    · rw [← order_eq_orderTop_of_ne_zero hn, WithTop.coe_le_coe]
      exact hmin i (mem_filter.mpr ⟨hi, hn⟩)
  · obtain ⟨hjs, hj₀⟩ := mem_filter.mp hj
    exact surjective_sum_mul_iterateFrobenius s _ hf ⟨j, hjs, coeff_order_eq_zero.not.mpr hj₀⟩

end TauCeti.LaurentSeries

namespace TauCeti.LaurentSeries

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
  {f : ℕ} {V : Type*} [AddCommGroup V] [Module k⸨X⸩ V]

local notation "σ" => coefficientFrobenius (k := k) p f

/-- On a finite-dimensional Laurent-series vector space over an algebraically closed field,
the difference `Φ - 1` for positive coefficient Frobenius is surjective. -/
theorem surjective_sub_id_of_coefficientFrobenius_semilinear [Module.Finite k⸨X⸩ V] (hf : 0 < f)
    (Φ : V →ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] V) : Surjective (fun x => Φ x - x) := by
  apply Φ.surjective_sub_id_of_surjective_sum_mul_iterate σ
  exact fun _ a ha => surjective_sum_mul_coefficientFrobenius hf a ha

end TauCeti.LaurentSeries
