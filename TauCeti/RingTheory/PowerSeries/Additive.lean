/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.Ring.NamePowerVars

/-!
# Additive formal power series

Over a commutative ring killed by a prime `p`, the identity `f(X + Y) = f(X) + f(Y)`
holds exactly when the coefficients of `f` vanish outside the degrees `p ^ k`.
No reducedness or field hypothesis is needed. The series `linearizedSeries p a`
parametrizes these additive series by the sequence of their coefficients in degrees `p ^ k`.
Here `X₀` and `X₁` are the two variables of `MvPowerSeries (Fin 2) R`, so
`f.subst (X₀ + X₁)` expresses `f(X + Y)`.
The proof uses Mathlib’s `PowerSeries.coeff_subst_X_zero_add_X_one` and the
Lucas criterion `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`.
At `p = 2` this classification determines the ambiguity in strict logarithms of
formal groups killed by two: their additive coordinate changes have arbitrary
coefficients in degrees `2 ^ k`, with coefficient one in degree one.

## Main results

* `subst_add_eq_iff_constantCoeff_eq_zero_and_choose_mul_coeff_eq_zero`:
  the coefficient criterion over an arbitrary ring.
* `subst_add_eq_iff_coeff_eq_zero`: the prime-characteristic support criterion.
* `eq_linearizedSeries_of_subst_add`: the canonical linearized expansion of an additive series.
* `subst_add_eq_iff_existsUnique_linearizedSeries`: the unique linearized expansion.

These results are in the `TauCeti` namespace. For example,
`TauCeti.subst_add_eq_iff_coeff_eq_zero f hp hR` gives the support criterion for `f`.

## References

* M. Hazewinkel, *Formal Groups and Applications*, Chapter I, §1 (additive series).
-/

public section

namespace TauCeti

open PowerSeries

variable {R : Type*}

name_power_vars X₀, X₁ over R

section CommRing

variable [CommRing R]

/-- A series is additive precisely when its constant term is zero and each mixed
binomial coefficient annihilates the corresponding coefficient of the series. -/
theorem subst_add_eq_iff_constantCoeff_eq_zero_and_choose_mul_coeff_eq_zero (f : PowerSeries R) :
    f.subst (X₀ + X₁) = f.subst X₀ + f.subst X₁ ↔
      f.constantCoeff = 0 ∧ ∀ i j : ℕ, 0 < i → 0 < j →
        ((i + j).choose i : R) * f.coeff (i + j) = 0 := by
  have hcoeff (d : Fin 2 →₀ ℕ) :
      MvPowerSeries.coeff d
        (f.subst X₀ + f.subst X₁) =
      (if d 1 = 0 then f.coeff (d 0) else 0) +
        (if d 0 = 0 then f.coeff (d 1) else 0) := by
    simp [PowerSeries.coeff_subst_single, Finsupp.ext_iff, Fin.forall_fin_two]
  constructor
  · intro h
    have hc := congrArg (MvPowerSeries.coeff 0) h
    rw [coeff_subst_X_zero_add_X_one, hcoeff] at hc
    simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add, Nat.choose_zero_right,
      Nat.cast_one, one_mul, ite_true] at hc
    refine ⟨?_, ?_⟩
    · simpa only [coeff_zero_eq_constantCoeff, add_eq_left] using hc.symm
    · intro i j hi hj
      have hd := congrArg (MvPowerSeries.coeff
        (Finsupp.single 0 i + Finsupp.single 1 j)) h
      rw [coeff_subst_X_zero_add_X_one, hcoeff] at hd
      simpa [hi.ne', hj.ne'] using hd
  · rintro ⟨hc, h⟩
    ext d
    rw [coeff_subst_X_zero_add_X_one, hcoeff]
    by_cases h0 : d 0 = 0
    · simp [h0, hc, coeff_zero_eq_constantCoeff]
    by_cases h1 : d 1 = 0
    · simp [h1, h0]
    simpa [h0, h1] using h (d 0) (d 1) (by omega) (by omega)

/-- In a ring killed by a prime `p`, additive series are precisely the series supported
in degrees `p ^ k`. This includes rings with nilpotents and the zero ring. -/
theorem subst_add_eq_iff_coeff_eq_zero (f : PowerSeries R) {p : ℕ} (hp : p.Prime)
    (hR : (p : R) = 0) :
    f.subst (X₀ + X₁) = f.subst X₀ + f.subst X₁ ↔
      ∀ n : ℕ, (¬ ∃ k : ℕ, n = p ^ k) → f.coeff n = 0 := by
  rw [subst_add_eq_iff_constantCoeff_eq_zero_and_choose_mul_coeff_eq_zero]
  constructor
  · rintro ⟨hc, h⟩ n hn
    by_cases hn0 : n = 0
    · simpa [hn0, coeff_zero_eq_constantCoeff] using hc
    by_contra hfn
    have : Fact p.Prime := ⟨hp⟩
    apply hn
    refine ⟨_, Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat
      (Nat.pos_of_ne_zero hn0) ?_⟩
    intro i hi
    obtain ⟨hi, hin⟩ := Finset.mem_Icc.mp hi
    rw [Nat.modEq_zero_iff_dvd]
    by_contra hpi
    have hmix := h i (n - i) hi (by omega)
    rw [Nat.add_sub_of_le (by omega)] at hmix
    apply hfn
    exact (nsmul_eq_zero_iff_of_coprime (hp.coprime_iff_not_dvd.mpr hpi)).mp
      ⟨by simp [nsmul_eq_mul, hR], by simpa [nsmul_eq_mul] using hmix⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff]
      exact h 0 (by rintro ⟨k, hk⟩; exact (pow_ne_zero k hp.ne_zero) hk.symm)
    · intro i j hi hj
      by_cases hn : ∃ k : ℕ, i + j = p ^ k
      · obtain ⟨k, hk⟩ := hn
        have hd := hp.dvd_choose_pow (n := k) hi.ne' (by omega : i ≠ p ^ k)
        obtain ⟨a, ha⟩ := hd
        rw [hk, ha, Nat.cast_mul, hR, zero_mul, zero_mul]
      · rw [h (i + j) hn, mul_zero]

end CommRing

section Semiring

variable [Semiring R]

/-- The formal sum `∑ₖ aₖ X^(p^k)`, defined coefficientwise.
The intended bases satisfy `1 < p`; no topology on the coefficient ring is required. -/
noncomputable def linearizedSeries (p : ℕ) (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => if n = p ^ Nat.log p n then a (Nat.log p n) else 0

/-- The coefficients of the linearized expansion, including its vanishing coefficients. -/
theorem coeff_linearizedSeries (p : ℕ) (a : ℕ → R) (n : ℕ) :
    (linearizedSeries p a).coeff n =
      if n = p ^ Nat.log p n then a (Nat.log p n) else 0 := by
  simp [linearizedSeries]

/-- The coefficient in degree `p ^ k` is the prescribed `k`th coefficient. -/
@[simp]
theorem coeff_pow_linearizedSeries {p : ℕ} (hp : 1 < p) (a : ℕ → R) (k : ℕ) :
    (linearizedSeries p a).coeff (p ^ k) = a k := by
  simp [coeff_linearizedSeries, Nat.log_pow hp]

/-- Coefficients outside the powers of `p` vanish. -/
theorem coeff_linearizedSeries_eq_zero {p n : ℕ} (a : ℕ → R)
    (hn : ¬ ∃ k : ℕ, n = p ^ k) : (linearizedSeries p a).coeff n = 0 := by
  rw [coeff_linearizedSeries, ite_eq_right (fun h => hn ⟨_, h⟩)]

/-- A linearized expansion has zero constant term. -/
@[simp]
theorem constantCoeff_linearizedSeries (p : ℕ) (a : ℕ → R) :
    (linearizedSeries p a).constantCoeff = 0 := by
  simp [← coeff_zero_eq_constantCoeff, coeff_linearizedSeries]

/-- The linear coefficient of a linearized expansion is its zeroth parameter; thus
strict additive coordinates have `a 0 = 1`. -/
@[simp]
theorem coeff_one_linearizedSeries (p : ℕ) (a : ℕ → R) :
    (linearizedSeries p a).coeff 1 = a 0 := by
  simp [coeff_linearizedSeries]

/-- For `1 < p`, a linearized expansion determines its coefficient sequence. -/
theorem linearizedSeries_injective {p : ℕ} (hp : 1 < p) :
    Function.Injective (linearizedSeries (R := R) p) := by
  intro a b h
  funext k
  simpa [coeff_pow_linearizedSeries hp] using congrArg (PowerSeries.coeff (p ^ k)) h

/-- Changing coefficients commutes with a linearized expansion. -/
@[simp]
theorem map_linearizedSeries {S : Type*} [Semiring S] (φ : R →+* S) (p : ℕ) (a : ℕ → R) :
    PowerSeries.map φ (linearizedSeries p a) = linearizedSeries p (φ ∘ a) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_linearizedSeries, Function.comp_apply]
  split_ifs <;> simp

end Semiring

section CommRing

variable [CommRing R]

/-- Linearized expansions are additive over every ring killed by the prime `p`. -/
theorem subst_add_linearizedSeries {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (a : ℕ → R) :
    (linearizedSeries p a).subst (X₀ + X₁) =
      (linearizedSeries p a).subst X₀ + (linearizedSeries p a).subst X₁ := by
  exact (subst_add_eq_iff_coeff_eq_zero _ hp hR).mpr fun _ hn =>
    coeff_linearizedSeries_eq_zero a hn

/-- Over a commutative ring killed by a prime `p`, an additive series equals the
linearized expansion of its coefficients in degrees `p ^ k`. -/
theorem eq_linearizedSeries_of_subst_add (f : PowerSeries R) {p : ℕ}
    (hp : p.Prime) (hR : (p : R) = 0)
    (h : f.subst (X₀ + X₁) = f.subst X₀ + f.subst X₁) :
    f = linearizedSeries p (fun k => f.coeff (p ^ k)) := by
  have hcoeff := (subst_add_eq_iff_coeff_eq_zero f hp hR).mp h
  ext n
  rw [coeff_linearizedSeries]
  split_ifs with hn
  · rw [← hn]
  · exact hcoeff n (by rintro ⟨k, rfl⟩; exact hn (by rw [Nat.log_pow hp.one_lt]))

/-- Over a commutative ring killed by a prime `p`, a series is additive if and only if
it has a unique linearized expansion. -/
theorem subst_add_eq_iff_existsUnique_linearizedSeries (f : PowerSeries R) {p : ℕ}
    (hp : p.Prime) (hR : (p : R) = 0) :
    f.subst (X₀ + X₁) = f.subst X₀ + f.subst X₁ ↔
      ∃! a : ℕ → R, f = linearizedSeries p a := by
  constructor
  · intro h
    have hf := eq_linearizedSeries_of_subst_add f hp hR h
    refine ⟨fun k => f.coeff (p ^ k), hf, ?_⟩
    intro a ha
    exact linearizedSeries_injective hp.one_lt (ha.symm.trans hf)
  · rintro ⟨a, rfl, _⟩
    exact subst_add_linearizedSeries hp hR a

end CommRing

end TauCeti
