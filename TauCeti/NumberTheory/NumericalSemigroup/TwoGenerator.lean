/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumericalSemigroup.Symmetric
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

/-!
# Numerical semigroups with two generators

For coprime natural numbers `a` and `b`, the submonoid `⟨a, b⟩ = AddSubmonoid.closure {a, b}` of
`ℕ` is a numerical semigroup. Its Apéry set with respect to `a` is `{0, b, 2 b, …, (a - 1) b}`,
and Selmer's formulas then give Sylvester's formulas for its invariants:

* the Frobenius number is `F = a b - a - b`;
* the conductor and twice the genus both equal `(a - 1) (b - 1)`.

In particular `⟨a, b⟩` is symmetric: equality `2 g = F + 1` characterises symmetric numerical
semigroups. All statements hold for every coprime pair, including the degenerate pairs where `a`
or `b` is `0` or `1` and `⟨a, b⟩ = ℕ`, whose Frobenius number is `-1`. For `1 < a` and `1 < b`
the Frobenius number agrees with Mathlib's `frobeniusNumber_pair`.

## Main results

* `AddSubmonoid.aperySet_closure_pair`: `Ap(⟨a, b⟩, a) = {j b | j < a}`.
* `AddSubmonoid.numericalFrobenius_closure_pair`: `F(⟨a, b⟩) = a b - a - b`.
* `AddSubmonoid.numericalConductor_closure_pair`: `C(⟨a, b⟩) = (a - 1) (b - 1)`.
* `AddSubmonoid.two_mul_numericalGenus_closure_pair`: `2 g(⟨a, b⟩) = (a - 1) (b - 1)`.
* `AddSubmonoid.isSymmetricNumericalSemigroup_closure_pair`: `⟨a, b⟩` is symmetric.

## References

* A. Assi and P. A. García-Sánchez, *Numerical semigroups and applications* (2014),
  §1, Example 13; §2, Corollary 45.
-/

public section

namespace AddSubmonoid

variable {a b : ℕ}

/-- The Apéry set of `⟨a, b⟩` with respect to `a` consists of the multiples `j * b` with `j < a`
when `a` and `b` are coprime. -/
theorem aperySet_closure_pair (hab : a.Coprime b) :
    (closure ({a, b} : Set ℕ)).aperySet a = (· * b) '' Set.Iio a := by
  ext w
  simp only [mem_aperySet_iff_sub_notMem, mem_closure_pair, smul_eq_mul, Set.mem_image,
    Set.mem_Iio]
  constructor
  · rintro ⟨⟨u, v, rfl⟩, hw⟩
    have hpos : a ≠ 0 := by rintro rfl; exact hw (Nat.zero_le _) ⟨u, v, by simp⟩
    -- A summand `a`, or `a` copies of `b`, could be removed while staying in `⟨a, b⟩`.
    obtain rfl : u = 0 := by
      by_contra hu
      have hu : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu
      have hle : a ≤ u * a + v * b := by nlinarith
      exact hw hle ⟨u - 1, v, by zify [hu, hle]; ring⟩
    simp only [zero_mul, zero_add] at hw ⊢
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact ⟨0, Nat.pos_of_ne_zero hpos, by simp⟩
    refine ⟨v, lt_of_not_ge fun hv ↦ ?_, rfl⟩
    have hle : a ≤ v * b := by nlinarith
    exact hw hle ⟨b - 1, v - a, by zify [hv, hle, Nat.one_le_iff_ne_zero.mpr hb.ne']; ring⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨0, j, by ring⟩, fun hle ⟨u, v, huv⟩ ↦ ?_⟩
    -- `j * b - a = u * a + v * b` gives `(j - v) * b = (u + 1) * a` with `0 < j - v < a`.
    have hsum : (u * a + v * b + a : ℤ) = j * b := by
      have := congrArg (Nat.cast : ℕ → ℤ) huv
      push_cast [hle] at this
      linear_combination this
    have hvj : v < j := by
      have : (v * b : ℤ) < j * b := by nlinarith
      exact lt_of_mul_lt_mul_right (by exact_mod_cast this) (Nat.zero_le b)
    have hdvd : a ∣ (j - v) * b := ⟨u + 1, by zify [hvj.le]; linear_combination -hsum⟩
    have := Nat.le_of_dvd (by omega) (hab.dvd_of_dvd_mul_right hdvd)
    omega

/-- For coprime `a` and `b`, the sum of the Apéry set of `⟨a, b⟩` with respect to `a` satisfies
`2 Σ_{j < a} j b = a (a - 1) b`. -/
private theorem two_mul_finsum_aperySet_closure_pair (hab : a.Coprime b) :
    2 * ∑ᶠ w ∈ (closure ({a, b} : Set ℕ)).aperySet a, w = a * (a - 1) * b := by
  -- `j ↦ j * b` is injective on `{0, …, a - 1}`: if `b = 0` then `a = 1`.
  have hinj : Set.InjOn (· * b) (Set.Iio a) := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · obtain rfl : a = 1 := Nat.coprime_zero_right _ |>.mp hab
      intro i hi j hj _
      simp_all
    · exact fun i _ j _ h ↦ Nat.eq_of_mul_eq_mul_right hb h
  rw [aperySet_closure_pair hab, finsum_mem_image hinj, ← Finset.coe_range, finsum_mem_coe_finset,
    ← Finset.sum_mul, ← Finset.sum_range_id_mul_two]
  ring

/-- **Sylvester's formula** for the Frobenius number: for coprime `a` and `b`, the Frobenius
number of `⟨a, b⟩` is `a b - a - b`. This includes the pairs with `⟨a, b⟩ = ℕ`, whose Frobenius
number is `-1`; for `1 < a` and `1 < b` it agrees with Mathlib's `frobeniusNumber_pair`. -/
theorem numericalFrobenius_closure_pair (hab : a.Coprime b) :
    (closure ({a, b} : Set ℕ)).numericalFrobenius = a * b - a - b := by
  have h := (isNumericalSemigroup_closure_pair_iff a b).mpr hab
  rcases eq_or_ne a 0 with rfl | hpos
  · obtain rfl : b = 1 := Nat.coprime_zero_left _ |>.mp hab
    simp
  have hmax : IsGreatest ((closure ({a, b} : Set ℕ)).aperySet a) ((a - 1) * b) := by
    rw [aperySet_closure_pair hab]
    refine ⟨⟨a - 1, Set.mem_Iio.mpr (by omega), rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    exact Nat.mul_le_mul_right b (by have := Set.mem_Iio.mp hj; omega)
  rw [h.numericalFrobenius_eq_sSup_aperySet_sub hpos, hmax.csSup_eq]
  push_cast [Nat.one_le_iff_ne_zero.mpr hpos]
  ring

/-- **Sylvester's formula** for the conductor: for coprime `a` and `b`, the conductor of `⟨a, b⟩`
is `(a - 1) (b - 1)`. -/
theorem numericalConductor_closure_pair (hab : a.Coprime b) :
    (closure ({a, b} : Set ℕ)).numericalConductor = (a - 1) * (b - 1) := by
  have hF := numericalFrobenius_closure_pair hab
  have hC := (closure ({a, b} : Set ℕ)).numericalFrobenius_add_one
  -- The degenerate pairs `(0, 1)` and `(1, 0)` give conductor `0`.
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain rfl : b = 1 := Nat.coprime_zero_left _ |>.mp hab
    simp_all
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 1 := Nat.coprime_zero_right _ |>.mp hab
    have : ((closure ({1, 0} : Set ℕ)).numericalConductor : ℤ) = 0 := by rw [← hC, hF]; norm_num
    simpa using this
  zify [ha, hb]
  linear_combination hF - hC

/-- **Sylvester's formula** for the genus: for coprime `a` and `b`, twice the genus of `⟨a, b⟩` is
`(a - 1) (b - 1)`. -/
theorem two_mul_numericalGenus_closure_pair (hab : a.Coprime b) :
    2 * (closure ({a, b} : Set ℕ)).numericalGenus = (a - 1) * (b - 1) := by
  have h := (isNumericalSemigroup_closure_pair_iff a b).mpr hab
  rcases eq_or_ne a 0 with rfl | hpos
  · obtain rfl : b = 1 := Nat.coprime_zero_left _ |>.mp hab
    simp
  -- Compare Selmer's formula with the sum `Σ_{j < a} j b` over the Apéry set, then cancel `a`.
  have hS := h.two_mul_finsum_aperySet (subset_closure (Set.mem_insert a _)) hpos
  rw [two_mul_finsum_aperySet_closure_pair hab] at hS
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 1 := Nat.coprime_zero_right _ |>.mp hab
    simpa using hS
  zify [Nat.one_le_iff_ne_zero.mpr hpos, hb] at hS ⊢
  linear_combination -hS

/-- **Two-generator numerical semigroups are symmetric**: for coprime `a` and `b`, the numerical
semigroup `⟨a, b⟩` is symmetric. -/
theorem isSymmetricNumericalSemigroup_closure_pair (hab : a.Coprime b) :
    (closure ({a, b} : Set ℕ)).IsSymmetricNumericalSemigroup := by
  rw [((isNumericalSemigroup_closure_pair_iff a b).mpr hab)
      |>.isSymmetricNumericalSemigroup_iff_two_mul_numericalGenus_eq,
    two_mul_numericalGenus_closure_pair hab, numericalConductor_closure_pair hab]

/-- The semigroup generated by `4` and `9` has Frobenius number `23` and genus `12`. -/
example : (closure ({4, 9} : Set ℕ)).numericalFrobenius = 23 ∧
    (closure ({4, 9} : Set ℕ)).numericalGenus = 12 := by
  have hab : Nat.Coprime 4 9 := by decide
  refine ⟨by rw [numericalFrobenius_closure_pair hab]; norm_num, ?_⟩
  have := two_mul_numericalGenus_closure_pair hab
  omega

/-- The semigroup generated by `2` and an odd number `2 k + 1` is symmetric. -/
example (k : ℕ) : (closure ({2, 2 * k + 1} : Set ℕ)).IsSymmetricNumericalSemigroup :=
  isSymmetricNumericalSemigroup_closure_pair (by simp)

end AddSubmonoid
