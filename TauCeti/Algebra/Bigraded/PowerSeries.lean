/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Euler characteristics of unbounded bigraded formal power series

An unbounded bigraded Poincaré series with finite internal slices in each Maslov (cohomological)
degree is represented by an element `P : PowerSeries (LaurentPolynomial R)`, whose `n`-th
power-series coefficient is the Laurent polynomial of internal degrees in Maslov degree `n`.

Unlike `TauCeti.Bigraded.Series`, such a series need not have an Alexander-graded Euler
characteristic: a fixed internal degree can receive nonzero contributions from infinitely many
Maslov degrees (for instance `∑ n ≥ 0, tⁿ`), and negative internal degrees do not fit in an
ordinary formal power series. To avoid junk values on non-summable slices, this file packages
the exact slicewise finiteness and nonnegativity of internal support in
`TauCeti.Bigraded.HasEulerPowerSeries` and defines `TauCeti.Bigraded.eulerPowerSeries` only from
such a witness. Every series vanishing strictly below the diagonal (`a < n`) satisfies this
condition automatically, because internal degree `a` receives contributions only from `n ≤ a`.

By contrast, the Maslov-graded Euler series `TauCeti.Bigraded.maslovEulerPowerSeries` needs no
cohomological vanishing hypothesis: it specializes the internal Laurent variable to `1` in each
Maslov degree and rescales the formal variable by `-1`, forming a ring homomorphism
`PowerSeries (LaurentPolynomial R) →+* PowerSeries R`.

Over a strictly ordered commutative ring, for a series with nonnegative coefficients and no
support strictly below the diagonal, the Alexander-graded and Maslov-graded Euler formal power
series agree if and only if the series is supported on the diagonal `a = n`
(`TauCeti.Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff`). This extends
`TauCeti.Bigraded.euler_eq_maslovEuler_iff_isDiagonal` to unbounded cohomological support.

## Main definitions

* `TauCeti.Bigraded.HasEulerPowerSeries`: vanishing in negative internal degrees together with
  finite Maslov support in each nonnegative internal degree.
* `TauCeti.Bigraded.eulerPowerSeries`: the Alexander-graded Euler formal power series of a series
  satisfying `HasEulerPowerSeries`.
* `TauCeti.Bigraded.maslovEulerPowerSeries`: the Maslov-graded Euler formal power series, as a
  ring homomorphism `PowerSeries (LaurentPolynomial R) →+* PowerSeries R`.

## Main results

* `TauCeti.Bigraded.HasEulerPowerSeries.of_lowerTriangular` and
  `TauCeti.Bigraded.coeff_eulerPowerSeries_of_lowerTriangular`: lower-triangular bigraded formal
  power series have well-defined Alexander-graded Euler series truncated at `a + 1` in degree `a`.
* `TauCeti.Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff`: on nonnegative
  lower-triangular bigraded formal power series, the two Euler series agree if and only if all
  off-diagonal coefficients vanish.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for diagonal bigraded Ext and formal Poincaré/Hilbert series identities.
* L. Positselski, *The correspondence between Hilbert series of quadratically dual algebras does
  not imply their having the Koszul property*, Funct. Anal. Appl. **29** (1995), 213--217.
-/

public section

namespace TauCeti.Bigraded

open LaurentPolynomial

section HasEulerPowerSeries

variable {R : Type*} [Semiring R]

/-- Slicewise finiteness hypothesis under which `P : PowerSeries (LaurentPolynomial R)` has a
well-defined Alexander-graded Euler formal power series in `PowerSeries R`: negative internal
degrees vanish, and each nonnegative internal degree is supported in finitely many Maslov
degrees. -/
structure HasEulerPowerSeries (P : PowerSeries (LaurentPolynomial R)) : Prop where
  /-- Every negative internal degree has zero coefficient in all Maslov degrees. -/
  coeff_eq_zero_of_neg (n : ℕ) {a : ℤ} (ha : a < 0) : (PowerSeries.coeff n P).coeff a = 0
  /-- Each nonnegative internal degree is nonzero in only finitely many Maslov degrees. -/
  finite_support (a : ℕ) : {n : ℕ | (PowerSeries.coeff n P).coeff (a : ℤ) ≠ 0}.Finite

/-- The zero series has an Alexander-graded Euler power series. -/
theorem HasEulerPowerSeries.zero :
    HasEulerPowerSeries (0 : PowerSeries (LaurentPolynomial R)) where
  coeff_eq_zero_of_neg _ _ _ := by simp
  finite_support _ := by simp

/-- The multiplicative identity has an Alexander-graded Euler power series. -/
theorem HasEulerPowerSeries.one :
    HasEulerPowerSeries (1 : PowerSeries (LaurentPolynomial R)) where
  coeff_eq_zero_of_neg n a ha := by
    rw [PowerSeries.coeff_one]
    split_ifs with hn
    · simp [ha.ne]
    · simp
  finite_support a := by
    refine ({0} : Finset ℕ).finite_toSet.subset fun n hn ↦ ?_
    simp only [Set.mem_ofPred_eq, PowerSeries.coeff_one] at hn
    by_contra hn0
    simp [Finset.mem_singleton.not.mp hn0] at hn

/-- `HasEulerPowerSeries` is closed under addition. -/
theorem HasEulerPowerSeries.add {P Q : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P) (hQ : HasEulerPowerSeries Q) :
    HasEulerPowerSeries (P + Q) where
  coeff_eq_zero_of_neg n a ha := by
    simp [hP.coeff_eq_zero_of_neg n ha, hQ.coeff_eq_zero_of_neg n ha]
  finite_support a :=
    ((hP.finite_support a).union (hQ.finite_support a)).subset fun n hn ↦ by
      simp only [Set.mem_ofPred_eq, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hn
      by_contra hmem
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hmem
      exact hn (by simp [hmem.1, hmem.2])

/-- Any bigraded formal power series vanishing strictly below the diagonal (`a < n`) has an
Alexander-graded Euler formal power series: negative internal degrees satisfy `a < 0 ≤ n`, and
internal degree `a ≥ 0` vanishes for all `n > a`. -/
theorem HasEulerPowerSeries.of_lowerTriangular {P : PowerSeries (LaurentPolynomial R)}
    (hl : ∀ (n : ℕ) (a : ℤ), a < n → (PowerSeries.coeff n P).coeff a = 0) :
    HasEulerPowerSeries P where
  coeff_eq_zero_of_neg n a ha := hl n a (ha.trans_le (Nat.cast_nonneg n))
  finite_support a :=
    (Finset.range (a + 1)).finite_toSet.subset fun n hn ↦ by
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hle
      exact hn (hl n a (by omega))

end HasEulerPowerSeries

section EulerPowerSeries

variable {R : Type*} [Ring R]

/-- The **Alexander-graded Euler formal power series** of `P : PowerSeries (LaurentPolynomial R)`
from a slicewise finiteness witness `hP`: its `a`-th power-series coefficient is the finite
alternating sum `∑ n, (-1)ⁿ [qᵃ][tⁿ] P`. -/
noncomputable def eulerPowerSeries {P : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P) : PowerSeries R :=
  PowerSeries.mk fun a ↦
    (hP.finite_support a).toFinset.sum fun n ↦
      (-1 : R) ^ n * (PowerSeries.coeff n P).coeff (a : ℤ)

/-- The `a`-th coefficient of `eulerPowerSeries` is the alternating sum over the finite Maslov
support in internal degree `a`. -/
@[simp]
theorem coeff_eulerPowerSeries {P : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P) (a : ℕ) :
    PowerSeries.coeff a (eulerPowerSeries hP) =
      (hP.finite_support a).toFinset.sum fun n ↦
        (-1 : R) ^ n * (PowerSeries.coeff n P).coeff (a : ℤ) := by
  simp [eulerPowerSeries]

/-- Equal series have equal Alexander-graded Euler power series regardless of the finiteness
witnesses used. -/
theorem eulerPowerSeries_congr {P Q : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P) (hQ : HasEulerPowerSeries Q) (h : P = Q) :
    eulerPowerSeries hP = eulerPowerSeries hQ := by
  subst h
  rfl

/-- In internal degree `a`, the coefficient of `eulerPowerSeries` may be computed by truncating at
any Maslov bound `N` above which `(PowerSeries.coeff n P).coeff a` vanishes. -/
theorem coeff_eulerPowerSeries_eq_sum {P : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P) (a N : ℕ)
    (hN : ∀ n ≥ N, (PowerSeries.coeff n P).coeff (a : ℤ) = 0) :
    PowerSeries.coeff a (eulerPowerSeries hP) =
      ∑ n ∈ Finset.range N, (-1 : R) ^ n * (PowerSeries.coeff n P).coeff (a : ℤ) := by
  rw [coeff_eulerPowerSeries]
  refine Finset.sum_subset (fun n hn ↦ ?_) (fun n _ hn ↦ ?_)
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hn
    rw [Finset.mem_range]
    by_contra hge
    exact hn (hN n (Nat.le_of_not_lt hge))
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hn
    simp [hn]

/-- For a lower-triangular bigraded formal power series (`a < n → [qᵃ][tⁿ] P = 0`), the `a`-th
coefficient of `eulerPowerSeries` is the finite alternating sum over `n ≤ a`. -/
theorem coeff_eulerPowerSeries_of_lowerTriangular {P : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P)
    (hl : ∀ (n : ℕ) (a : ℤ), a < n → (PowerSeries.coeff n P).coeff a = 0) (a : ℕ) :
    PowerSeries.coeff a (eulerPowerSeries hP) =
      ∑ n ∈ Finset.range (a + 1), (-1 : R) ^ n * (PowerSeries.coeff n P).coeff (a : ℤ) :=
  coeff_eulerPowerSeries_eq_sum hP a (a + 1) fun n hn ↦ hl n a (by omega)

/-- The Alexander-graded Euler power series of `0` is `0`, for any finiteness witness. -/
@[simp]
theorem eulerPowerSeries_zero
    (h0 : HasEulerPowerSeries (0 : PowerSeries (LaurentPolynomial R))) :
    eulerPowerSeries h0 = 0 := by
  ext a
  rw [coeff_eulerPowerSeries_eq_sum _ a 0 (by simp)]
  simp

/-- The Alexander-graded Euler power series of `1` is `1`, for any finiteness witness. -/
@[simp]
theorem eulerPowerSeries_one
    (h1 : HasEulerPowerSeries (1 : PowerSeries (LaurentPolynomial R))) :
    eulerPowerSeries h1 = 1 := by
  ext a
  rw [coeff_eulerPowerSeries_eq_sum _ a 1 fun n hn ↦ by
    rw [PowerSeries.coeff_one, ite_eq_right (by omega)]
    simp]
  rcases eq_or_ne a 0 with rfl | ha
  · simp [PowerSeries.coeff_one]
  · simp [PowerSeries.coeff_one, ha]

/-- `eulerPowerSeries` is additive with respect to any finiteness witnesses. -/
theorem eulerPowerSeries_add {P Q : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P) (hQ : HasEulerPowerSeries Q)
    (hPQ : HasEulerPowerSeries (P + Q)) :
    eulerPowerSeries hPQ = eulerPowerSeries hP + eulerPowerSeries hQ := by
  ext a
  classical
  let s := (hP.finite_support a).toFinset ∪ (hQ.finite_support a).toFinset
  have hsP : ∀ n ≥ s.sup id + 1, (PowerSeries.coeff n P).coeff (a : ℤ) = 0 := by
    intro n hn
    by_contra h0
    have hmem : n ∈ s := Finset.mem_union_left _ ((hP.finite_support a).mem_toFinset.mpr h0)
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hmem
    omega
  have hsQ : ∀ n ≥ s.sup id + 1, (PowerSeries.coeff n Q).coeff (a : ℤ) = 0 := by
    intro n hn
    by_contra h0
    have hmem : n ∈ s := Finset.mem_union_right _ ((hQ.finite_support a).mem_toFinset.mpr h0)
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hmem
    omega
  rw [map_add, coeff_eulerPowerSeries_eq_sum hPQ a (s.sup id + 1)
      (fun n hn ↦ by simp [hsP n hn, hsQ n hn]),
    coeff_eulerPowerSeries_eq_sum hP a (s.sup id + 1) hsP,
    coeff_eulerPowerSeries_eq_sum hQ a (s.sup id + 1) hsQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp [mul_add]

end EulerPowerSeries

section MaslovEulerPowerSeries

variable {R : Type*} [CommRing R]

/-- The **Maslov-graded Euler formal power series** of `P : PowerSeries (LaurentPolynomial R)`, as
a ring homomorphism: it evaluates the internal Laurent variable at `1` in each Maslov degree and
rescales the formal cohomological variable by `-1`. -/
noncomputable def maslovEulerPowerSeries : PowerSeries (LaurentPolynomial R) →+* PowerSeries R :=
  (PowerSeries.rescale (-1 : R)).comp (PowerSeries.map (laurentEval (1 : Rˣ)).toRingHom)

/-- Applying `maslovEulerPowerSeries` maps each Maslov coefficient by `laurentEval 1` and rescales
by `-1`. -/
theorem maslovEulerPowerSeries_apply (P : PowerSeries (LaurentPolynomial R)) :
    maslovEulerPowerSeries P =
      PowerSeries.rescale (-1 : R) (PowerSeries.map (laurentEval (1 : Rˣ)).toRingHom P) :=
  (rfl)

/-- The `n`-th coefficient of `maslovEulerPowerSeries P` is `(-1)ⁿ` times the sum of all internal
coefficients in Maslov degree `n`. -/
@[simp]
theorem coeff_maslovEulerPowerSeries (P : PowerSeries (LaurentPolynomial R)) (n : ℕ) :
    PowerSeries.coeff n (maslovEulerPowerSeries P) =
      (-1 : R) ^ n * laurentEval (1 : Rˣ) (PowerSeries.coeff n P) := by
  simp [maslovEulerPowerSeries]

/-- On a diagonally supported bigraded formal power series, `maslovEulerPowerSeries` has `n`-th
coefficient `(-1)ⁿ [qⁿ][tⁿ] P`. -/
theorem coeff_maslovEulerPowerSeries_of_diagonal {P : PowerSeries (LaurentPolynomial R)}
    (hdiag : ∀ (n : ℕ) (a : ℤ), (n : ℤ) ≠ a → (PowerSeries.coeff n P).coeff a = 0) (n : ℕ) :
    PowerSeries.coeff n (maslovEulerPowerSeries P) =
      (-1 : R) ^ n * (PowerSeries.coeff n P).coeff (n : ℤ) := by
  classical
  rw [coeff_maslovEulerPowerSeries, laurentEval_one_eq_sum, Finsupp.sum]
  congr 1
  by_cases hn : (n : ℤ) ∈ (PowerSeries.coeff n P).coeff.support
  · exact Finset.sum_eq_single (n : ℤ)
      (fun a ha hne ↦ False.elim (Finsupp.mem_support_iff.mp ha (hdiag n a hne.symm)))
      (fun hnot ↦ False.elim (hnot hn))
  · rw [Finset.sum_eq_zero fun a ha ↦ ?_, Finsupp.notMem_support_iff.mp hn]
    by_cases hna : (n : ℤ) = a
    · subst hna
      exact False.elim (hn ha)
    · exact hdiag n a hna

end MaslovEulerPowerSeries

section DiagonalCriterion

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The Alexander-graded and Maslov-graded Euler formal power series agree exactly on diagonal
series**, for any series with nonnegative coefficients and no support strictly below the diagonal.
Unlike `TauCeti.Bigraded.euler_eq_maslovEuler_iff_isDiagonal`, no cohomological vanishing bound is
required. -/
theorem eulerPowerSeries_eq_maslovEulerPowerSeries_iff {P : PowerSeries (LaurentPolynomial R)}
    (hP : HasEulerPowerSeries P)
    (hnonneg : ∀ (n : ℕ) (a : ℤ), 0 ≤ (PowerSeries.coeff n P).coeff a)
    (hl : ∀ (n : ℕ) (a : ℤ), a < n → (PowerSeries.coeff n P).coeff a = 0) :
    eulerPowerSeries hP = maslovEulerPowerSeries P ↔
      ∀ (n : ℕ) (a : ℤ), (n : ℤ) ≠ a → (PowerSeries.coeff n P).coeff a = 0 := by
  classical
  constructor
  · intro heq n
    -- Strong induction on the Maslov degree `n` inductively eliminates lower-degree
    -- contributions to internal degree `n` before comparing the two `n`-th coefficients.
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a hna
      have hcoeff := congrArg (PowerSeries.coeff n) heq
      rw [coeff_eulerPowerSeries_of_lowerTriangular hP hl n, Finset.sum_range_succ,
        Finset.sum_eq_zero (fun m hm ↦ by
          rw [Finset.mem_range] at hm
          rw [ih m hm n (by omega), mul_zero]),
        zero_add, coeff_maslovEulerPowerSeries, laurentEval_one_eq_sum] at hcoeff
      -- Multiply by `(-1) ^ n` to cancel the common sign in Maslov degree `n`.
      have hsum : (PowerSeries.coeff n P).coeff (n : ℤ) =
          (PowerSeries.coeff n P).coeff.sum fun _ c ↦ c := by
        have hmul := congrArg ((-1 : R) ^ n * ·) hcoeff
        simpa only [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] using hmul
      let S := (PowerSeries.coeff n P).coeff.support ∪ {(n : ℤ)}
      have hS : (PowerSeries.coeff n P).coeff.sum (fun _ c ↦ c) =
          ∑ b ∈ S, (PowerSeries.coeff n P).coeff b :=
        Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (fun _ _ ↦ rfl)
      rw [hS, ← Finset.add_sum_erase S _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))]
        at hsum
      have herase : ∑ b ∈ S.erase (n : ℤ), (PowerSeries.coeff n P).coeff b = 0 :=
        add_left_cancel (hsum.symm.trans (add_zero _).symm)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ hnonneg n b)] at herase
      by_cases hmem : a ∈ (PowerSeries.coeff n P).coeff.support
      · exact herase a (Finset.mem_erase.mpr ⟨hna.symm, Finset.mem_union_left _ hmem⟩)
      · exact Finsupp.notMem_support_iff.mp hmem
  · intro hdiag
    ext a
    rw [coeff_eulerPowerSeries_of_lowerTriangular hP hl a,
      coeff_maslovEulerPowerSeries_of_diagonal hdiag a, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun m hm ↦ by
        rw [Finset.mem_range] at hm
        rw [hdiag m a (by omega), mul_zero]),
      zero_add]

end DiagonalCriterion

end TauCeti.Bigraded
