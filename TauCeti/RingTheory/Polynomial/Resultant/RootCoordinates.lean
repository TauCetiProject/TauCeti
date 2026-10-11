/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.Normalization
import TauCeti.RingTheory.Polynomial.RootEnumeration
public import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Discriminants under changes of root coordinate

Translation of the root coordinate preserves the discriminant. Reversal also preserves it
when the constant coefficient is nonzero, so that reversal preserves degree. These identities
allow reciprocal coordinates centered at a nonroot: the new leading coefficient is the value
of the original polynomial at that center. In a polynomial family this is useful even when
the original leading coefficient vanishes upon specialization. Reversal is taken at the
formal degree before specialization; it must not be recomputed at a smaller fiber degree.

Combined with integral normalization, reversal at a nonroot `a` turns any polynomial into a monic
polynomial over the same ring whose discriminant is that of the original polynomial times a power
of its value at `a`.

The identities include repeated roots and constant polynomials. No separability or
characteristic-zero hypothesis is needed.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), Sections 2–3 (delineability).
* S. Lang, *Algebra*, third edition, Chapter IV, §8 (discriminants and root products).
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/- The passage from split fields to arbitrary rings uses Mathlib's
`Polynomial.induction_of_Splits_of_injective_of_surjective`. Translation uses
`Polynomial.resultant_taylor` and `Polynomial.resultant_deriv`; the reversal root calculations
use `Polynomial.discr_prod_X_sub_C` and `TauCeti.discr_C_mul`. -/

private theorem discr_comp_X_add_C_of_field {K : Type*} [Field K] (f : K[X])
    (a : K) : (f.comp (X + C a)).discr = f.discr := by
  by_cases hn : f.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hn]
    simp
  have hpos : 0 < f.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hn)
  have hder : (taylor a f).derivative = taylor a f.derivative := by
    simp [taylor_apply, derivative_comp]
  -- The derivative can have degree less than `n - 1` in positive characteristic.
  -- Extend the resultant's degree bound before applying `resultant_deriv`.
  have hres :
      resultant (taylor a f) (taylor a f.derivative) f.natDegree (f.natDegree - 1) =
        resultant f f.derivative f.natDegree (f.natDegree - 1) := by
    calc
      _ = f.leadingCoeff ^ (f.natDegree - 1 - f.derivative.natDegree) *
          resultant (taylor a f) (taylor a f.derivative) := by
        conv_lhs => rw [← Nat.add_sub_of_le (natDegree_derivative_le f)]
        rw [resultant_add_right_deg _ _ _ _ _ (by simp), coeff_taylor_natDegree]
        simp only [natDegree_taylor]
      _ = f.leadingCoeff ^ (f.natDegree - 1 - f.derivative.natDegree) *
          resultant f f.derivative := by rw [resultant_taylor]
      _ = _ := by
        conv_rhs => rw [← Nat.add_sub_of_le (natDegree_derivative_le f)]
        rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  rw [← hder, ← natDegree_taylor f a,
    resultant_deriv (by simpa only [degree_taylor] using hpos), natDegree_taylor,
    leadingCoeff_taylor, resultant_deriv hpos] at hres
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    intro hz
    simp [hz] at hn)
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (by simp)) hlc) hres

/-- Translating the root coordinate preserves the discriminant over any commutative ring. -/
@[simp]
theorem discr_comp_X_add_C (f : R[X]) (a : R) :
    (f.comp (X + C a)).discr = f.discr := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits K f _ => exact discr_comp_X_add_C_of_field f a
  | injective R S φ hφ f ih =>
    apply hφ
    rw [← discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ _),
      ← discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ _), map_comp]
    simpa only [Polynomial.map_add, map_X, map_C] using ih (φ a)
  | surjective R S φ hφ f ih =>
    obtain ⟨g, hg, hdeg⟩ := exists_degree_eq_of_mem_lifts (map_surjective φ hφ f)
    obtain ⟨a, rfl⟩ := hφ a
    have hnat : g.natDegree = f.natDegree := natDegree_eq_of_degree_eq hdeg
    have hmap : (g.map φ).natDegree = g.natDegree := by rw [hg, hnat]
    have hmapshift : ((g.comp (X + C a)).map φ).natDegree =
        (g.comp (X + C a)).natDegree := by
      rw [map_comp, Polynomial.map_add, map_X, map_C, hg,
        ← taylor_apply, ← taylor_apply, natDegree_taylor, natDegree_taylor, hnat]
    have h := congrArg φ (ih g a)
    rw [← discr_map_of_natDegree_eq φ hmapshift, ← discr_map_of_natDegree_eq φ hmap,
      map_comp, Polynomial.map_add, map_X, map_C, hg] at h
    exact h

private theorem discr_reverse_of_splits {K : Type*} [Field K] {f : K[X]}
    (hf : f.Splits) (h0 : f.coeff 0 ≠ 0) : f.reverse.discr = f.discr := by
  classical
  have hf0 : f ≠ 0 := fun h ↦ h0 (by simp [h])
  obtain ⟨r, hr⟩ := (exists_isRootEnumeration_iff_splits
    (R := K) (f := f) (L := K) (ι := Fin f.natDegree) (by simp)).2 (by simpa using hf)
  have hroots : f.roots = univ.val.map r := by simpa [isRootEnumeration_iff] using hr
  have hfac : f = C f.leadingCoeff * ∏ i, (X - C (r i)) := by
    conv_lhs => rw [hf.eq_prod_roots, hroots, Multiset.map_map,
      ← prod_eq_multiset_prod]
    rfl
  have hr0 (i : Fin f.natDegree) : r i ≠ 0 := by
    intro hi
    have hz : f.eval 0 = 0 := by
      conv_lhs => rw [hfac]
      simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [prod_eq_zero (mem_univ i) (by simp [hi]), mul_zero]
    exact h0 (by simpa only [coeff_zero_eq_eval_zero] using hz)
  -- Reverse each linear factor and extract its nonzero scalar.
  have h1 : (1 : K[X]).reverse = 1 := by
    simpa only [C_1] using reverse_C (1 : K)
  have hrev (s : Finset (Fin f.natDegree)) :
      (∏ i ∈ s, (X - C (r i))).reverse = ∏ i ∈ s, (1 - C (r i) * X) := by
    induction s using Finset.induction with
    | empty => simpa only [prod_empty] using h1
    | @insert i s hi ih =>
      rw [prod_insert hi, prod_insert hi, reverse_mul_of_domain, ih]
      congr 1
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C]
      have hX : (X : K[X]).reverse = 1 := by
        simpa only [one_mul, h1] using reverse_mul_X (1 : K[X])
      simp only [hX, natDegree_X, pow_one, C_neg]
      ring
  have hlin (i : Fin f.natDegree) :
      1 - C (r i) * X = C (-r i) * (X - C (r i)⁻¹) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ (hr0 i)]
    simp [C_neg]
    ring
  have hrevfac : f.reverse =
      C (f.leadingCoeff * ∏ i, -r i) * ∏ i, (X - C (r i)⁻¹) := by
    conv_lhs => rw [hfac, reverse_mul_of_domain, reverse_C, hrev]
    simp only [hlin, prod_mul_distrib, ← map_prod]
    rw [← mul_assoc, ← C_mul]
  -- Each root occurs in exactly `n - 1` unordered pairs. Squaring removes
  -- the signs introduced by reciprocal differences and reversed leading coefficients.
  have hpair : ∏ i, ∏ j ∈ Ioi i, r i * r j =
      (∏ i, r i) ^ (f.natDegree - 1) := by
    rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun _ j ↦ r j)]
    simp [Finset.card_compl, ← prod_pow]
  have hexp : 2 * f.natDegree - 2 = 2 * (f.natDegree - 1) := by omega
  have hden : ∏ i, ∏ j ∈ Ioi i, (r i * r j) ^ 2 =
      (∏ i, r i) ^ (2 * f.natDegree - 2) := by
    simp only [prod_pow, hpair, ← pow_mul, hexp]
    rw [Nat.mul_comm (f.natDegree - 1)]
  have hdiff (i j : Fin f.natDegree) :
      ((r i)⁻¹ - (r j)⁻¹) ^ 2 = (r i - r j) ^ 2 / (r i * r j) ^ 2 := by
    field_simp [hr0 i, hr0 j]
    ring
  have hsign : (∏ i, -r i) ^ (2 * f.natDegree - 2) =
      (∏ i, r i) ^ (2 * f.natDegree - 2) := by
    rw [prod_neg, card_univ, Fintype.card_fin, hexp, mul_pow, pow_mul]
    simp [← pow_mul, mul_comm f.natDegree 2]
  have hlc := leadingCoeff_ne_zero.2 hf0
  have hp : (∏ i, r i) ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hr0 i
  rw [hrevfac, TauCeti.discr_C_mul _ (mul_ne_zero hlc (prod_ne_zero_iff.2
    fun i _ ↦ neg_ne_zero.2 (hr0 i))), discr_prod_X_sub_C]
  conv_rhs => rw [hfac, TauCeti.discr_C_mul _ hlc, discr_prod_X_sub_C]
  simp only [natDegree_finsetProd_X_sub_C_eq_card, card_univ, Fintype.card_fin,
    hdiff, prod_div_distrib, hden]
  rw [mul_pow, hsign]
  field_simp [hp]

/-- Reversal preserves the discriminant when the constant coefficient is nonzero.
The condition ensures that reversal preserves the degree; without it the statement can fail. -/
@[simp]
theorem discr_reverse (f : R[X]) (h0 : f.coeff 0 ≠ 0) : f.reverse.discr = f.discr := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits K f hf => exact discr_reverse_of_splits hf h0
  | injective R S φ hφ f ih =>
    apply hφ
    have hmap : (f.map φ).reverse = f.reverse.map φ := by
      rw [reverse, reverse, natDegree_map_eq_of_injective hφ, reflect_map]
    have h0' : (f.map φ).coeff 0 ≠ 0 := by
      rw [coeff_map]
      exact (map_eq_zero_iff φ hφ).not.2 h0
    rw [← discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ _),
      ← discr_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ _), ← hmap]
    exact ih h0'
  | surjective R S φ hφ f ih =>
    obtain ⟨g, hg, hdeg⟩ := exists_degree_eq_of_mem_lifts (map_surjective φ hφ f)
    have hnat : g.natDegree = f.natDegree := natDegree_eq_of_degree_eq hdeg
    have h0g : g.coeff 0 ≠ 0 := by
      intro hz
      apply h0
      rw [← hg, coeff_map, hz, map_zero]
    have hrevdeg (p : R[X]) (hp : p.coeff 0 ≠ 0) : p.reverse.natDegree = p.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (.inr hp), Nat.sub_zero]
    have hrevdeg' : f.reverse.natDegree = f.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (.inr h0), Nat.sub_zero]
    have hmaprev : f.reverse = g.reverse.map φ := by
      rw [reverse, reverse, ← hnat, ← hg, reflect_map]
    have hmap : (g.map φ).natDegree = g.natDegree := by rw [hg, hnat]
    have hmaprevdeg : (g.reverse.map φ).natDegree = g.reverse.natDegree := by
      rw [← hmaprev, hrevdeg', hrevdeg g h0g, hnat]
    have h := congrArg φ (ih g h0g)
    rw [← discr_map_of_natDegree_eq φ hmaprevdeg, ← discr_map_of_natDegree_eq φ hmap,
      hg, ← hmaprev] at h
    exact h

/-- Specializing a reversal taken at the formal degree preserves the formal discriminant
whenever the specialized constant coefficient is nonzero. The original polynomial may
drop degree under `φ`; the reversed polynomial retains its degree. -/
@[simp]
theorem discr_map_reverse {S : Type*} [CommRing S] (f : R[X]) (φ : R →+* S)
    (h0 : φ (f.coeff 0) ≠ 0) : (f.reverse.map φ).discr = φ f.discr := by
  have h0f : f.coeff 0 ≠ 0 := fun h ↦ h0 (h ▸ map_zero φ)
  have hdeg : f.reverse.natDegree = f.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (.inr h0f), Nat.sub_zero]
  have hmapdeg : (f.reverse.map φ).natDegree = f.reverse.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero natDegree_map_le
    rw [coeff_map, hdeg, coeff_reverse, revAt_le le_rfl, Nat.sub_self]
    exact h0
  rw [discr_map_of_natDegree_eq φ hmapdeg, discr_reverse f h0f]

/-- Translating the root coordinate to a nonroot `a` and reversing at the formal degree keeps
the degree. -/
theorem natDegree_reverse_comp_X_add_C (f : R[X]) {a : R} (h : f.eval a ≠ 0) :
    (f.comp (X + C a)).reverse.natDegree = f.natDegree := by
  rw [← taylor_apply, reverse_natDegree, natTrailingDegree_eq_zero.2 (.inr (by
    rwa [taylor_coeff_zero])), Nat.sub_zero, natDegree_taylor]

/-- Translating the root coordinate to a nonroot `a` and reversing at the formal degree gives
leading coefficient `f.eval a`. -/
theorem leadingCoeff_reverse_comp_X_add_C (f : R[X]) {a : R} (h : f.eval a ≠ 0) :
    (f.comp (X + C a)).reverse.leadingCoeff = f.eval a := by
  rw [← taylor_apply, reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (.inr (by
    rwa [taylor_coeff_zero])), taylor_coeff_zero]

/-- Normalized reciprocal coordinates centered at a nonroot `a` multiply the discriminant of a
degree `n` polynomial by the `(n - 1) * (n - 2)` power of `f.eval a`. In a polynomial family,
`f.eval a` can remain nonzero under a specialization that kills the leading coefficient of `f`;
when that specialization lands in a field, such as `ℝ`, the factor becomes a unit, so this monic
polynomial over the same ring carries the discriminant of `f` up to a unit factor there. -/
theorem discr_integralNormalization_reverse_comp_X_add_C (f : R[X]) {a : R}
    (h : f.eval a ≠ 0) :
    (f.comp (X + C a)).reverse.integralNormalization.discr =
      f.eval a ^ ((f.natDegree - 1) * (f.natDegree - 2)) * f.discr := by
  rw [TauCeti.discr_integralNormalization, leadingCoeff_reverse_comp_X_add_C f h,
    natDegree_reverse_comp_X_add_C f h,
    discr_reverse _ (by rwa [← taylor_apply, taylor_coeff_zero]), discr_comp_X_add_C]

end Polynomial
