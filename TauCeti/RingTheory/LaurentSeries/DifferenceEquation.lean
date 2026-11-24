/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius

import TauCeti.Algebra.Module.LinearMap.Iterate
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
  classical
  intro v
  -- The first `finrank + 1` iterates of the target vector satisfy a nonzero relation.
  let n := Module.finrank k⸨X⸩ V
  let u (i : Fin (n + 1)) := Φ^[n - i.val] v
  have hu : ¬ LinearIndependent k⸨X⸩ u := by
    intro h
    simpa [n] using h.fintype_card_le_finrank
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hu
  -- Untwist each relation coefficient by the corresponding Frobenius power.
  let c (i : Fin (n + 1)) := (σ).symm^[n - i.val] (a i)
  have hinverse : LeftInverse σ (σ).symm := (σ).apply_symm_apply
  have hinv (i : Fin (n + 1)) : σ^[n - i.val] (c i) = a i := hinverse.iterate _ _
  let d (i : ℕ) := if hi : i < n + 1 then c ⟨i, hi⟩ else 0
  have hd : ∃ i ∈ range (n + 1), d i ≠ 0 := by
    refine ⟨i₀, mem_range.mpr i₀.isLt, ?_⟩
    simp only [d, i₀.isLt, dite_true, Fin.eta]
    intro hi
    apply hi₀
    rw [← hinv i₀, hi]
    exact iterate_fixed (map_zero σ) _
  obtain ⟨z, hz⟩ := surjective_sum_mul_coefficientFrobenius (p := p) hf d hd (-1)
  let w (i : Fin (n + 1)) := (c i * σ^[i.val] z) • v
  have hsum : ∑ i, w i = -v := by
    have hz' : (∑ i : Fin (n + 1), c i * σ^[i.val] z) = -1 := by
      rw [sum_fin_eq_sum_range]
      refine (sum_congr rfl fun i hi => ?_).trans hz
      have hil : i < n + 1 := mem_range.mp hi
      simp only [d, dite_eq_left hil, coefficientFrobenius_iterate]
    simp only [w, ← sum_smul, hz', neg_one_smul]
  have hiter (i : Fin (n + 1)) :
      Φ^[n - i.val] (w i) = σ^[n] z • (a i • u i) := by
    rw [iterate_map_smulₛₗ Φ, RingEquiv.coe_toRingHom, iterate_map_mul, hinv, ← iterate_add_apply,
      Nat.sub_add_cancel (by omega : i.val ≤ n), smul_smul, mul_comm]
  -- The iterated terms sum to zero, and their starting terms sum to `-v`.
  refine ⟨∑ i : Fin (n + 1), ∑ j ∈ range (n - i.val), Φ^[j] (w i), ?_⟩
  dsimp only
  rw [map_sum, ← sum_sub_distrib]
  have htel (n : ℕ) (x : V) :
      Φ (∑ j ∈ range n, Φ^[j] x) - ∑ j ∈ range n, Φ^[j] x = Φ^[n] x - x := by
    simp only [map_sum, ← sum_sub_distrib, ← iterate_succ_apply']
    exact sum_range_sub (fun j => Φ^[j] x) n
  simp_rw [htel, hiter]
  rw [sum_sub_distrib, ← smul_sum, ha, smul_zero, hsum, zero_sub, neg_neg]

end TauCeti.LaurentSeries
