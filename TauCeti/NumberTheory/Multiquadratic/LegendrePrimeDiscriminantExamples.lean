/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.LegendrePrimeDiscriminants
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
# Concrete Legendre criteria for the first genus-field examples

The multiquadratic roadmap's genus-field worked examples begin with the prime-discriminant
lists `[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. This file records the
corresponding concrete Legendre-character criteria, so later worked-example code can consume
the familiar congruence and reciprocal-symbol conditions directly.

The prime-discriminant convention follows Cox's *Primes of the Form x² + ny²* and
Lemmermeyer's *Reciprocity Laws*, as in the prime-discriminant splitting API this file reuses.

## Main results

* `TauCeti.Multiquadratic.forall_legendreSym_neg_four_five_eq_one_iff`: the `-5`
  genus-field character list `[-4, 5]` is trivial at an odd prime `p` exactly when
  `p ≡ 1 (mod 4)` and `(p / 5) = 1`.
* `TauCeti.Multiquadratic.forall_legendreSym_neg_four_neg_three_neg_seven_eq_one_iff`: the
  `-21` genus-field character list `[-4, -3, -7]` is trivial exactly when
  `p ≡ 1 (mod 4)`, `(p / 3) = 1`, and `(p / 7) = 1`.
-/

public section

namespace TauCeti.Multiquadratic

/-- The complex number `i√n` squares to `-n`. -/
private theorem I_mul_real_sqrt_nat_sq (n : ℕ) :
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 = -(n : ℂ) := by
  have hsqrt : (((Real.sqrt n : ℝ) : ℂ) ^ 2) = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  calc
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 =
        Complex.I ^ 2 * (((Real.sqrt n : ℝ) : ℂ) ^ 2) := by
      ring
    _ = -(n : ℂ) := by
      simp [Complex.I_sq, hsqrt]

/-- The chosen complex square root of `-3`, namely `i√3`. -/
noncomputable abbrev sqrtNegThree : ℂ :=
  Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)

/-- The chosen root `sqrtNegThree` squares to `-3`. -/
@[simp]
theorem sqrtNegThree_sq : sqrtNegThree ^ 2 = (-3 : ℂ) := by
  simpa [sqrtNegThree] using I_mul_real_sqrt_nat_sq 3

/-- The chosen complex square root of `-7`, namely `i√7`. -/
noncomputable abbrev sqrtNegSeven : ℂ :=
  Complex.I * ((Real.sqrt 7 : ℝ) : ℂ)

/-- The chosen root `sqrtNegSeven` squares to `-7`. -/
@[simp]
theorem sqrtNegSeven_sq : sqrtNegSeven ^ 2 = (-7 : ℂ) := by
  simpa [sqrtNegSeven] using I_mul_real_sqrt_nat_sq 7

/-- The prime-discriminant list `[-4, 5]` for the genus-field generators of `ℚ(√-5)`. -/
abbrev negFourFivePrimeDiscriminants : Fin 2 → ℤ :=
  ![(-4 : ℤ), 5]

/-- The prime-discriminant list `[-4, -3, -7]` for the genus-field generators of
`ℚ(√-21)`. -/
abbrev negFourNegThreeNegSevenPrimeDiscriminants : Fin 3 → ℤ :=
  ![(-4 : ℤ), -3, -7]

/-- The chosen roots `i`, `i√3`, and `i√7` square to the radicands attached to the prime
discriminants `-4`, `-3`, and `-7`. -/
theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) :
          ℚ)) := by
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminants, hrad]

/-- Each member of the `[-4, -3, -7]` worked-example list is a prime discriminant. -/
theorem isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants :
    ∀ i : Fin 3, IsPrimeDiscriminant (negFourNegThreeNegSevenPrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

/-- The worked-example prime-discriminant list `[-4, -3, -7]` is injective. -/
theorem injective_negFourNegThreeNegSevenPrimeDiscriminants :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

/-- The worked-example prime-discriminant list `[-4, -3, -7]` does not contain all three even
prime discriminants. -/
theorem not_all_even_negFourNegThreeNegSevenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

/-- The range of the chosen roots for `[-4, -3, -7]` is exactly `{i, i√3, i√7}`. -/
theorem range_roots_neg_four_neg_three_neg_seven :
    (Set.range fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
      = {Complex.I, sqrtNegThree, sqrtNegSeven} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hx]⟩
    · exact ⟨2, by simp [hx]⟩

/-- **The `ℚ(√-5)` genus-field character condition.** For an odd prime `p`, the Legendre
symbols of the prime-discriminant list `[-4, 5]` are all `1` exactly when
`p ≡ 1 (mod 4)` and the reciprocal symbol `(p / 5)` is `1`. -/
@[simp]
theorem forall_legendreSym_neg_four_five_eq_one_iff {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (∀ i, legendreSym p (negFourFivePrimeDiscriminants i) = 1) ↔
      p % 4 = 1 ∧ @legendreSym 5 ⟨by decide⟩ (p : ℤ) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · intro h
    constructor
    · have h0 := h 0
      simpa using
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mp h0
    · have h1 := h 1
      simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 5) (q := p) (by norm_num) hodd).mp h1
  · rintro ⟨hfour, hfive⟩ i
    fin_cases i
    · exact
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mpr hfour
    · simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 5) (q := p) (by norm_num) hodd).mpr hfive

/-- **The `ℚ(√-21)` genus-field character condition.** For an odd prime `p`, the Legendre
symbols of the prime-discriminant list `[-4, -3, -7]` are all `1` exactly when
`p ≡ 1 (mod 4)`, `(p / 3) = 1`, and `(p / 7) = 1`. -/
@[simp]
theorem forall_legendreSym_neg_four_neg_three_neg_seven_eq_one_iff {p : ℕ}
    [Fact p.Prime] (hodd : p ≠ 2) :
    (∀ i, legendreSym p (negFourNegThreeNegSevenPrimeDiscriminants i) = 1) ↔
      p % 4 = 1 ∧ @legendreSym 3 ⟨by decide⟩ (p : ℤ) = 1 ∧
        @legendreSym 7 ⟨by decide⟩ (p : ℤ) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  constructor
  · intro h
    constructor
    · have h0 := h 0
      simpa using
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mp h0
    · constructor
      · have h1 := h 1
        simpa [oddPrimeDiscriminant] using
          (legendreSym_oddPrimeDiscriminant_eq_one_iff
            (p := 3) (q := p) (by norm_num) hodd).mp h1
      · have h2 := h 2
        simpa [oddPrimeDiscriminant] using
          (legendreSym_oddPrimeDiscriminant_eq_one_iff
            (p := 7) (q := p) (by norm_num) hodd).mp h2
  · rintro ⟨hfour, hthree, hseven⟩ i
    fin_cases i
    · exact
        (legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (q := p) hodd).mpr hfour
    · simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 3) (q := p) (by norm_num) hodd).mpr hthree
    · simpa [oddPrimeDiscriminant] using
        (legendreSym_oddPrimeDiscriminant_eq_one_iff
          (p := 7) (q := p) (by norm_num) hodd).mpr hseven

end TauCeti.Multiquadratic
