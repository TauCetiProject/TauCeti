/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Cartier operators on power series

The Cartier operator of modulus `q` and index `r` selects coefficients at the indices
`q * n + r`. It is linear in the series. For an actual residue `r < q`, it commutes with
multiplication by an expanded series, and the expanded Cartier components reconstruct the
original series. Over a finite field, expansion by its cardinality is the Frobenius power,
so these identities give the usual Cartier identities used in residue averaging.

The definition and finite-field multiplication identity follow Section 3, definition and
Proposition 4, of Rowland–Stipulanti–Yassawi, *An elementary proof of Bridy's theorem*
(<https://arxiv.org/html/2308.10977v2>). The substitution identities use Mathlib's
`PowerSeries.expand`; the finite-field specializations use
`FiniteField.PowerSeries.expand_card`.
-/

public section

namespace PowerSeries

section Semiring

variable (R : Type*) [Semiring R]

/-- The Cartier operator selects the coefficients at `q * n + r`. It is defined for every
index `r`; the multiplication identities require `r < q`. -/
noncomputable def cartier (q r : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun F := mk fun n ↦ F.coeff (q * n + r)
  map_add' F G := by ext n; simp
  map_smul' a F := by ext n; simp

variable {R}

/-- The defining coefficient equation of a Cartier operator. -/
@[simp]
theorem coeff_cartier (q r n : ℕ) (F : PowerSeries R) :
    (cartier R q r F).coeff n = F.coeff (q * n + r) := by
  simp [cartier]

/-- The residue-zero Cartier operator of modulus one is the identity. -/
@[simp]
theorem cartier_one_zero : cartier R 1 0 = LinearMap.id := by
  ext F n
  simp

/-- At nonzero modulus, the Cartier components of `1` vanish except at residue zero. This
holds even when `r` lies outside the residue range. -/
@[simp]
theorem cartier_one (q r : ℕ) (hq : q ≠ 0) :
    cartier R q r 1 = if r = 0 then 1 else 0 := by
  ext n
  by_cases hr : r = 0 <;> simp [hr, coeff_one, hq]

/-- On a monomial, a Cartier operator keeps precisely its residue class. -/
@[simp]
theorem cartier_monomial (q r m : ℕ) (hq : q ≠ 0) (hr : r < q) (a : R) :
    cartier R q r (monomial m a) =
      if m % q = r then monomial (m / q) a else 0 := by
  ext n
  have hq' := Nat.pos_of_ne_zero hq
  have hn : q * n + r = m ↔ m % q = r ∧ n = m / q := by
    constructor
    · rintro rfl
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div hq', Nat.div_eq_of_lt hr]
    · rintro ⟨hm, rfl⟩
      simpa [hm, Nat.add_comm] using Nat.mod_add_div m q
  simp only [coeff_cartier, coeff_monomial, hn]
  split_ifs <;> simp_all [coeff_monomial]

/-- At nonzero modulus, a Cartier operator sends a polynomial to a polynomial whose degree is at
most the original degree divided by the modulus. This holds for every index `r`. -/
theorem exists_cartier_coe_polynomial_eq (q r : ℕ) (hq : q ≠ 0) (P : Polynomial R) :
    ∃ P' : Polynomial R, P'.natDegree ≤ P.natDegree / q ∧ cartier R q r (P : R⟦X⟧) = P' := by
  classical
  refine ⟨∑ n ∈ Finset.range (P.natDegree / q + 1), Polynomial.monomial n (P.coeff (q * n + r)),
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn ↦
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)),
    ?_⟩
  ext n
  simp only [coeff_cartier, Polynomial.coeff_coe, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hn
  · rfl
  · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    have hlt : P.natDegree / q < n := by omega
    have := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hq)).mp hlt
    nlinarith

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Multiplication by an expanded series passes through a Cartier operator at an actual
residue. -/
theorem cartier_expand_mul (q r : ℕ) (hq : q ≠ 0) (hr : r < q)
    (F G : PowerSeries R) :
    cartier R q r (expand q hq F * G) = F * cartier R q r G := by
  classical
  ext n
  rw [coeff_cartier, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_bij_ne_zero
    (fun ij _ _ ↦ (q * ij.1, q * ij.2 + r)) ?_ ?_ ?_ ?_
  · intro ij hij _
    rw [Finset.mem_antidiagonal] at hij ⊢
    nlinarith [hij]
  · intro ij hij _ kl hkl _ heq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    have hq' := Nat.pos_of_ne_zero hq
    apply Prod.ext <;> nlinarith
  · intro ij hij hne
    have hi : q ∣ ij.1 := by
      by_contra hi
      simp [coeff_expand_of_not_dvd q hq F hi] at hne
    obtain ⟨i, hi⟩ := hi
    have heq := Finset.mem_antidiagonal.mp hij
    have hq' := Nat.pos_of_ne_zero hq
    have hin : i ≤ n := by nlinarith
    have hj : ij.2 = q * (n - i) + r := by
      have := Nat.sub_add_cancel hin
      nlinarith
    refine ⟨(i, n - i), Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le hin), ?_, ?_⟩
    · simpa [hi, hj, coeff_cartier] using hne
    · exact Prod.ext hi.symm hj.symm
  · intro ij hij _
    simp [coeff_cartier]

/-- Every series is the sum of its expanded Cartier components, one for each residue. -/
theorem sum_X_pow_mul_expand_cartier (q : ℕ) (hq : q ≠ 0) (F : PowerSeries R) :
    F = ∑ r ∈ Finset.range q, X ^ r * expand q hq (cartier R q r F) := by
  classical
  ext n
  rw [map_sum]
  have hq' := Nat.pos_of_ne_zero hq
  symm
  rw [Finset.sum_eq_single (n % q)]
  · have hle := Nat.mod_le n q
    rw [coeff_X_pow_mul', ite_eq_left hle]
    have hn : n - n % q = q * (n / q) := by
      have := Nat.mod_add_div n q
      omega
    rw [hn, coeff_expand_mul, coeff_cartier]
    simpa [Nat.add_comm] using congrArg (fun k ↦ F.coeff k) (Nat.mod_add_div n q)
  · intro r hr hne
    rw [coeff_X_pow_mul']
    split_ifs with hle
    · have hnd : ¬ q ∣ n - r := by
        intro hd
        have hmod : n % q = r := by
          obtain ⟨i, hi⟩ := hd
          have hn : n = q * i + r := by omega
          rw [hn, Nat.add_mod]
          simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
        exact hne hmod.symm
      exact coeff_expand_of_not_dvd q hq _ hnd
    · rfl
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.mod_lt n hq'))).elim

end CommRing

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- Over a finite field, multiplication by a cardinality power passes through a Cartier
operator at an actual residue. -/
theorem cartier_pow_card_mul (r : ℕ) (hr : r < Fintype.card K) (F G : PowerSeries K) :
    cartier K (Fintype.card K) r (F ^ Fintype.card K * G) =
      F * cartier K (Fintype.card K) r G := by
  rw [← FiniteField.PowerSeries.expand_card]
  exact cartier_expand_mul _ _ Fintype.card_ne_zero hr F G

/-- Over a finite field, a series is the sum of the cardinality powers of its Cartier
components multiplied by the corresponding powers of `X`. -/
theorem eq_sum_X_pow_mul_cartier_pow (F : PowerSeries K) :
    F = ∑ r ∈ Finset.range (Fintype.card K),
      X ^ r * (cartier K (Fintype.card K) r F) ^ Fintype.card K := by
  simpa only [FiniteField.PowerSeries.expand_card] using
    sum_X_pow_mul_expand_cartier (Fintype.card K) Fintype.card_ne_zero F

end FiniteField

/-! The small examples also check the residue restriction in the multiplication identities. -/

example : cartier (ZMod 3) 3 1 (monomial 7 (1 : ZMod 3)) = monomial 2 1 ∧
    cartier (ZMod 3) 3 0 (monomial 7 (1 : ZMod 3)) = 0 := by
  constructor <;> simp [cartier_monomial]

example (F : PowerSeries ℤ) : cartier ℤ 1 0 F = F := by simp

example (F : PowerSeries (ZMod 3)) : cartier (ZMod 3) 3 0 (F ^ 3) = F := by
  simpa using cartier_pow_card_mul (K := ZMod 3) 0 (by decide) F 1

example : cartier ℤ 1 1 (expand 1 one_ne_zero (X : PowerSeries ℤ) * 1) = 1 ∧
    (X : PowerSeries ℤ) * cartier ℤ 1 1 1 = 0 := by
  constructor
  · ext n
    simp [coeff_X, coeff_one]
  · simp

example : cartier (ZMod 3) 3 3 ((X : PowerSeries (ZMod 3)) ^ 3 * 1) = 1 ∧
    (X : PowerSeries (ZMod 3)) * cartier (ZMod 3) 3 3 1 = 0 := by
  constructor
  · ext n
    simp [coeff_X_pow, coeff_one]
  · simp

end PowerSeries
