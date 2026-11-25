/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius

import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear
import TauCeti.RingTheory.PowerSeries.CoefficientFrobenius

/-!
# Difference equations for coefficient Frobenius on Laurent series

If the residue field `k` is algebraically closed, every nonzero scalar twisted polynomial
in positive coefficient Frobenius is surjective on `k((X))`. Normalizing the operator
coefficients by a common power of `X` reduces the problem to a power-series equation.

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

open _root_.LaurentSeries (coeff_coe_powerSeries ofPowerSeries_powerSeriesPart)

variable {p : ℕ} {k : Type*} [Field k] [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- A nonzero scalar twisted polynomial in positive coefficient Frobenius is surjective on
Laurent series over an algebraically closed field. Each index in `s` denotes an iterate
of the same coefficient automorphism. -/
theorem surjective_sum_mul_coefficientFrobenius {f : ℕ} (hf : 0 < f) {s : Finset ℕ}
    (a : ℕ → k⸨X⸩) (ha : ∃ i ∈ s, a i ≠ 0) :
    Surjective (fun x : k⸨X⸩ => ∑ i ∈ s, a i * coefficientFrobenius p (f * i) x) := by
  classical
  intro b
  obtain ⟨j, hj, hmin⟩ := (s.filter fun i => a i ≠ 0).exists_min_image
    (fun i => (a i).order) (by
      obtain ⟨i, hi, hi₀⟩ := ha
      exact ⟨i, mem_filter.mpr ⟨hi, hi₀⟩⟩)
  let m := (a j).order
  -- Dividing all operator coefficients by the same monomial gives a nonzero reduction.
  let aSeries (i : ℕ) := PowerSeries.X ^ ((a i).order - m).toNat * (a i).powerSeriesPart
  have haSeries_coe (i : ℕ) (hi : i ∈ s) :
      (aSeries i : k⸨X⸩) = single (-m) 1 * a i := by
    rcases eq_or_ne (a i) 0 with hzero | hne
    · simp [aSeries, hzero]
    have hle := hmin i (mem_filter.mpr ⟨hi, hne⟩)
    have hadd : (((a i).order - m).toNat : ℤ) + -(a i).order = -m := by omega
    simp only [aSeries, PowerSeries.coe_mul, ofPowerSeries_X_pow, ofPowerSeries_powerSeriesPart]
    rw [← mul_assoc, single_mul_single, one_mul, hadd]
  have hj' := mem_filter.mp hj
  have hAj : PowerSeries.constantCoeff (aSeries j) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← coeff_coe_powerSeries, haSeries_coe _ hj'.1]
    simpa [coeff_single_mul, m] using (coeff_order_eq_zero.not.mpr hj'.2)
  obtain ⟨x, hx⟩ := TauCeti.PowerSeries.exists_sum_mul_map_iterateFrobenius_eq (p := p) s aSeries hf
    ⟨j, hj'.1, hAj⟩ b.powerSeriesPart
  refine ⟨single (b.order - m) 1 * (x : k⸨X⸩), ?_⟩
  apply mul_left_cancel₀ (a := (single (-b.order) 1 : k⸨X⸩)) (by simp)
  rw [← ofPowerSeries_powerSeriesPart b, ← hx, map_sum]
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hshift : (single (-b.order) 1 : k⸨X⸩) * single (b.order - m) 1 =
      single (-m) 1 := by
    have hadd : -b.order + (b.order - m) = -m := by omega
    rw [single_mul_single, one_mul, hadd]
  simp only [map_mul, coefficientFrobenius_single, one_pow, coefficientFrobenius_coe,
    haSeries_coe i hi]
  rw [← hshift]
  ac_rfl

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
  intro s a ha
  simpa only [coefficientFrobenius_iterate] using surjective_sum_mul_coefficientFrobenius hf a ha

end TauCeti.LaurentSeries
