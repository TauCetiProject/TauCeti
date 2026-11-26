/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.Algebra.MvPolynomial.Funext

/-!
# Evaluating polynomial combinations over valuation rings

If integral polynomials are linearly independent after reduction, a linear combination over the
fraction field has an integral evaluation point where its value has the size of a largest scalar
coefficient. The point can also be chosen where an auxiliary polynomial of nonzero reduction
has unit value. This allows a determinant factor to be included without losing the bound.

The selection statement is motivated by `New.exists_norm_le_norm_sum_mul_eval` in
`grh/src/New/Derivatives/Divisibility/Count.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open IsLocalRing

namespace MvPolynomial

/-- Over a local ring with infinite residue field, a multivariate polynomial takes a unit value
if and only if its reduction is nonzero. -/
theorem exists_isUnit_eval_iff {R σ : Type*} [CommRing R] [IsLocalRing R]
    [Infinite (ResidueField R)] (p : MvPolynomial σ R) :
    (∃ x, IsUnit (eval x p)) ↔ map (residue R) p ≠ 0 := by
  simp only [← residue_ne_zero_iff_isUnit, map_eval]
  refine ⟨fun ⟨x, hx⟩ h ↦ hx (by simp [h]), fun h ↦ ?_⟩
  obtain ⟨y, hy⟩ := exists_eval_ne_zero h
  obtain ⟨x, rfl⟩ := residue_surjective.comp_left y
  exact ⟨x, hy⟩

end MvPolynomial

namespace Valuation

open MvPolynomial

/-- Suppose the reductions of a finite family of integral polynomials are linearly independent
and the residue field is infinite. A linear combination with field coefficients admits an
integral evaluation point where its value under the multiplicative valuation is the maximum of the
scalar coefficient values. For an empty family that maximum is `0`. The same point can be chosen
where `g` takes a unit value, provided `g` has nonzero reduction. -/
theorem exists_eval_sum_valuation_eq_sup {K Γ σ ι : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Fintype ι] (v : Valuation K Γ)
    [Infinite (ResidueField v.valuationSubring)]
    (P : ι → MvPolynomial σ v.valuationSubring)
    (hP : LinearIndependent (ResidueField v.valuationSubring)
      (fun i ↦ MvPolynomial.map (residue v.valuationSubring) (P i)))
    (g : MvPolynomial σ v.valuationSubring)
    (hg : MvPolynomial.map (residue v.valuationSubring) g ≠ 0)
    (c : ι → K) :
    ∃ x : σ → v.valuationSubring, IsUnit (eval x g) ∧
      v (∑ j, c j * (eval x (P j) : K)) = Finset.univ.sup (fun i ↦ v (c i)) := by
  classical
  by_cases hc : ∀ i, c i = 0
  · obtain ⟨x, hx⟩ := (exists_isUnit_eval_iff g).2 hg
    refine ⟨x, hx, ?_⟩
    simp only [hc, zero_mul, Finset.sum_const_zero, map_zero]
    exact le_antisymm zero_le (Finset.sup_le fun _ _ ↦ le_rfl)
  push Not at hc
  obtain ⟨j, hj⟩ := hc
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k ↦ v (c k)) ⟨j, Finset.mem_univ j⟩
  have hmax (k : ι) : v (c k) ≤ v (c i) := hi k (Finset.mem_univ k)
  have hci : v (c i) ≠ 0 := ((pos_iff_ne_zero.mpr ((map_ne_zero v).2 hj)).trans_le (hmax j)).ne'
  have hi₀ : c i ≠ 0 := fun h ↦ hci (by simp [h])
  -- Divide by a largest coefficient before reducing; its own normalized coefficient is one.
  let a (k : ι) : v.valuationSubring := ⟨c k / c i, (v.mem_valuationSubring_iff _).2 (by
    rw [map_div₀, div_le_one₀ (pos_of_ne_zero hci)]
    exact hmax k)⟩
  have ha : a i = 1 := Subtype.ext (div_self hi₀)
  let Q := ∑ k, a k • P k
  have hQ : MvPolynomial.map (residue v.valuationSubring) Q ≠ 0 := by
    intro h
    have hsum : ∑ k, residue v.valuationSubring (a k) •
        MvPolynomial.map (residue v.valuationSubring) (P k) = 0 := by
      simpa [Q, smul_eq_C_mul] using h
    simpa [ha] using (linearIndependent_iff'.mp hP _ _ hsum i (Finset.mem_univ i))
  obtain ⟨x, hx⟩ := (exists_isUnit_eval_iff (Q * g)).2 (by simpa using mul_ne_zero hQ hg)
  rw [map_mul, (Commute.all _ _).isUnit_mul_iff] at hx
  have heval : (∑ k, c k * (eval x (P k) : K)) = c i * (eval x Q : K) := by
    have he (k : ι) : eval x (a k • P k) = a k * eval x (P k) := by simp [smul_eq_C_mul]
    simp only [Q, map_sum, he]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    -- The underlying field element of `a k` is the normalized coefficient.
    have hcoe : (a k : K) = c k / c i := rfl
    rw [hcoe, ← mul_assoc, mul_comm (c i), div_mul_cancel₀ _ hi₀]
  have hval : v (eval x Q : K) = 1 :=
    (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.mp hx.1
  refine ⟨x, hx.2, ?_⟩
  rw [heval, map_mul, hval, mul_one]
  exact le_antisymm (Finset.le_sup (f := fun k ↦ v (c k)) (Finset.mem_univ i))
    (Finset.sup_le fun k _ ↦ hmax k)

end Valuation
