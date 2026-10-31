/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Uniqueness of polynomial right components

Two monic right components of the same positive degree, normalized to vanish at zero,
are equal whenever their composites with nonconstant outer polynomials agree.
Consequently arbitrary right components of the same positive degree differ by an affine
change of variable. This is the polynomial rigidity used to recover parameters from
composites, even when postcomposition introduces additional critical points.

The argument compares the degree of the difference of two composites with the same outer
polynomial. Its leading contribution comes from the leading monomial of the outer polynomial;
characteristic zero prevents cancellation in the geometric sum of mixed powers.

## Main results

* `Polynomial.eq_of_comp_eq_comp_of_monic`: uniqueness of normalized right components,
  over a characteristic-zero integral domain.
* `Polynomial.eq_C_mul_add_C_of_comp_eq_comp`: the explicit affine relation between
  arbitrary equal-degree right components over a characteristic-zero field.

## References

E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
d'Enfants*, Lemma 4.50.
-/

public section

namespace Polynomial

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- The geometric sum of mixed powers of two monic polynomials of equal degree has the
expected degree in characteristic zero. -/
theorem natDegree_geom_sum₂ {p q : R[X]} (hp : p.Monic) (hq : q.Monic)
    (hdeg : p.natDegree = q.natDegree) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ range n, p ^ i * q ^ (n - 1 - i)).natDegree = (n - 1) * p.natDegree := by
  have hd (i : ℕ) (hi : i ∈ range n) :
      (p ^ i * q ^ (n - 1 - i)).natDegree = (n - 1) * p.natDegree := by
    rw [natDegree_mul (hp.pow i).ne_zero (hq.pow _).ne_zero, natDegree_pow,
      natDegree_pow, ← hdeg, ← add_mul]
    congr 1
    have := mem_range.mp hi
    omega
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (hd i hi).le
  · have hc : (∑ i ∈ range n, p ^ i * q ^ (n - 1 - i)).coeff
        ((n - 1) * p.natDegree) = (n : R) := by
      rw [finsetSum_coeff]
      trans ∑ i ∈ range n, (1 : R)
      · apply sum_congr rfl
        intro i hi
        rw [← hd i hi]
        exact ((hp.pow i).mul (hq.pow _)).coeff_natDegree
      · simp
    rw [hc]
    exact_mod_cast hn.ne'

/-- A nonconstant difference of equal-degree monic polynomials remains visible in the
highest terms of a difference of powers. -/
theorem natDegree_pow_sub_pow_of_monic {p q : R[X]} (hp : p.Monic) (hq : q.Monic)
    (hdeg : p.natDegree = q.natDegree) (hdiff : 0 < (p - q).natDegree)
    {n : ℕ} (hn : 0 < n) :
    (p ^ n - q ^ n).natDegree = (n - 1) * p.natDegree + (p - q).natDegree := by
  have hs := natDegree_geom_sum₂ hp hq hdeg hn
  obtain rfl | hn' := eq_or_lt_of_le (Nat.succ_le_of_lt hn)
  · simp
  have hpos : 0 < p.natDegree := by
    have := natDegree_sub_le p q
    rw [← hdeg, max_self] at this
    omega
  have hne := ne_zero_of_natDegree_gt (hs ▸ Nat.mul_pos (by omega) hpos)
  rw [← geom_sum₂_mul p q n, natDegree_mul hne (ne_zero_of_natDegree_gt hdiff), hs]

/-- For monic equal-degree inputs with nonconstant difference, the degree of the difference
of composites is controlled by the leading term of the outer polynomial. -/
theorem natDegree_comp_sub_comp_of_monic {f p q : R[X]} (hf : 0 < f.natDegree)
    (hp : p.Monic) (hq : q.Monic) (hdeg : p.natDegree = q.natDegree)
    (hdiff : 0 < (p - q).natDegree) :
    (f.comp p - f.comp q).natDegree =
      (f.natDegree - 1) * p.natDegree + (p - q).natDegree := by
  have hmain := natDegree_pow_sub_pow_of_monic hp hq hdeg hdiff hf
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hf)
  have hlow : (f.eraseLead.comp p - f.eraseLead.comp q).natDegree ≤
      (f.natDegree - 1) * p.natDegree := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_comp_le.trans (Nat.mul_le_mul_right _ f.eraseLead_natDegree_le)
    · rw [hdeg]
      exact natDegree_comp_le.trans (Nat.mul_le_mul_right _ f.eraseLead_natDegree_le)
  have hexp : f.comp p - f.comp q =
      C f.leadingCoeff * (p ^ f.natDegree - q ^ f.natDegree) +
        (f.eraseLead.comp p - f.eraseLead.comp q) := by
    conv_lhs => rw [← f.eraseLead_add_C_mul_X_pow]
    simp only [add_comp, mul_comp, C_comp, pow_comp, X_comp]
    ring
  rw [hexp, natDegree_add_eq_left_of_natDegree_lt, natDegree_C_mul hlc, hmain]
  rw [natDegree_C_mul hlc, hmain]
  omega

/-- Monic right components of equal positive degree and equal constant coefficient are
uniquely determined by a common composite with nonconstant outer polynomials. Only one
outer polynomial needs to be assumed nonconstant. -/
theorem eq_of_comp_eq_comp_of_monic {f g p q : R[X]} (hf : 0 < f.natDegree)
    (hp : p.Monic) (hq : q.Monic) (hdeg : p.natDegree = q.natDegree)
    (hpdeg : 0 < p.natDegree) (hzero : p.coeff 0 = q.coeff 0)
    (heq : f.comp p = g.comp q) : p = q := by
  have hqdeg : q.natDegree ≠ 0 := by omega
  have hfg : f.natDegree = g.natDegree := by
    have h := congrArg natDegree heq
    rw [natDegree_comp, natDegree_comp, ← hdeg] at h
    exact Nat.eq_of_mul_eq_mul_right hpdeg h
  have hlc : f.leadingCoeff = g.leadingCoeff := by
    have h := congrArg leadingCoeff heq
    simpa [leadingCoeff_comp hpdeg.ne', leadingCoeff_comp hqdeg,
      hp.leadingCoeff, hq.leadingCoeff] using h
  have hbound : (g - f).natDegree ≤ f.natDegree - 1 := by
    apply natDegree_le_pred
    · exact (natDegree_sub_le g f).trans (by rw [hfg, max_self])
    · rw [coeff_sub, coeff_natDegree, hfg, coeff_natDegree, hlc, sub_self]
  by_contra hpq
  have hdiff : 0 < (p - q).natDegree := by
    by_contra! h
    have hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
    have hcoeff : (p - q).coeff 0 = 0 := by simp [hzero]
    rw [hcoeff, C_0] at hc
    exact hpq (sub_eq_zero.mp hc)
  have h := natDegree_comp_sub_comp_of_monic hf hp hq hdeg hdiff
  have hexp : f.comp p - f.comp q = (g - f).comp q := by
    rw [sub_comp, heq]
  rw [hexp] at h
  have hle := (natDegree_comp_le (p := g - f) (q := q)).trans
    (Nat.mul_le_mul_right q.natDegree hbound)
  rw [← hdeg, h] at hle
  omega

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- Equal-degree nonconstant right components of a common polynomial composite differ by
an affine transformation. The nonzero slope is the ratio of their leading coefficients. -/
theorem eq_C_mul_add_C_of_comp_eq_comp {f g p q : K[X]}
    (hf : 0 < f.natDegree) (hp : 0 < p.natDegree)
    (hdeg : p.natDegree = q.natDegree) (heq : f.comp p = g.comp q) :
    q = C (q.leadingCoeff / p.leadingCoeff) * p +
      C (q.coeff 0 - q.leadingCoeff / p.leadingCoeff * p.coeff 0) := by
  let N (r : K[X]) := C r.leadingCoeff⁻¹ * (r - C (r.coeff 0))
  let A (r : K[X]) := C r.leadingCoeff * X + C (r.coeff 0)
  have hlc (r : K[X]) (hr : 0 < r.natDegree) : r.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hr)
  have hN (r : K[X]) (hr : 0 < r.natDegree) :
      (N r).Monic ∧ (N r).natDegree = r.natDegree ∧ (N r).coeff 0 = 0 := by
    have hlead : (r - C (r.coeff 0)).leadingCoeff = r.leadingCoeff :=
      leadingCoeff_sub_of_degree_lt (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hr))
    refine ⟨monic_C_mul_of_mul_leadingCoeff_eq_one ?_, ?_, ?_⟩
    · rw [hlead, inv_mul_cancel₀ (hlc r hr)]
    · simp only [N, natDegree_C_mul (inv_ne_zero (hlc r hr)), natDegree_sub_C]
    · simp [N]
  have hA (r : K[X]) (hr : 0 < r.natDegree) : (A r).comp (N r) = r := by
    simp only [A, N, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hlc r hr), C_1, one_mul]
    exact sub_add_cancel _ _
  have hq : 0 < q.natDegree := by omega
  have hnorm : N p = N q := by
    apply eq_of_comp_eq_comp_of_monic (f := f.comp (A p)) (g := g.comp (A q))
    · simpa [natDegree_comp, A, natDegree_C_mul (hlc p hp)] using hf
    · exact (hN p hp).1
    · exact (hN q hq).1
    · rw [(hN p hp).2.1, (hN q hq).2.1, hdeg]
    · rwa [(hN p hp).2.1]
    · rw [(hN p hp).2.2, (hN q hq).2.2]
    · simpa only [comp_assoc, hA p hp, hA q hq] using heq
  calc
    q = (A q).comp (N p) := by rw [hnorm, hA q hq]
    _ = _ := by
      simp only [A, N, div_eq_mul_inv, add_comp, mul_comp, C_comp, X_comp, map_sub, map_mul]
      ring

end Field

end Polynomial
