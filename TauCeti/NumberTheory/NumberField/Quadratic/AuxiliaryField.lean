/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.Algebra.Squarefree
import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
import TauCeti.NumberTheory.ClassNumberOne.HeegnerNumbers
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.Model

/-!
# An imaginary quadratic field in which `2` splits and a given odd prime is inert

For every odd prime `p` there is an imaginary quadratic field `K` in which `2` splits into two
distinct prime ideals, `p` is inert, and `p` does not divide the class number of `K`
(`TauCeti.NumberField.exists_auxiliaryQuadraticField`). Burungale, Kobayashi and Ota use such a
field as the auxiliary CM field of their proof of Rubin's conjecture on local units in the
anticyclotomic tower at an inert prime [BKO21, Lemma 3.1]; there `p ≥ 5`, and the argument also
covers `p = 3`. No such field exists for `p = 2`: if `2 𝓞 K` were both prime and a product of two
distinct primes, cancelling it would make one factor the unit ideal.

The field is `ℚ(√(-n))` for a squarefree `n ≡ 7 (mod 8)` with `-n` a nonresidue modulo `p`. Its
discriminant is `-n ≡ 1 (mod 8)`, so `χ_{-n}(2) = 1` and `2` splits; `χ_{-n}(p)` is the Legendre
symbol of `-n` modulo `p`, so `p` is inert. It remains to make the class number smaller than `p`.

* For `p ≥ 37`, take a nonresidue `-a` with `0 ≤ a < p` and `0 ≤ k < 8` with `a + k p ≡ 7 (mod 8)`,
  which exists because `p` is odd, and let `n` be the squarefree part of `a + k p`. The removed
  square is odd and prime to `p`, so `n ≡ 7 (mod 8)`, `-n` is still a nonresidue, and `n < 8 p`.
  The analytic class number bound `h ≤ √|D| (1 + log |D|) / π`
  (`TauCeti.NumberField.classNumber_le_sqrt_mul_one_add_log_of_discr_ne`) then gives `h < p`.
* For the odd primes `p < 37`, one of the fields of discriminant `-7`, `-15` and `-31`, with class
  numbers `1`, `2` and `3` counted by reduced forms, has `p` inert.

## Main results

* `TauCeti.NumberField.exists_auxiliaryQuadraticField`: for every odd prime `p` there is an
  imaginary quadratic field in which `2` splits into two distinct primes, `p` is inert, and `p`
  does not divide the class number.

## References

* A. A. Burungale, S. Kobayashi and K. Ota, *Rubin's conjecture on local units in the
  anticyclotomic tower at inert primes*, Ann. of Math. 194 (2021), Lemma 3.1.
-/

public section

open Module NumberField TauCeti.Multiquadratic
open scoped NumberField Real

namespace TauCeti.NumberField

/-- For `37 ≤ p` and `0 < n < 8 p`, the quantity `√n (1 + log n)` is less than `π p`. Writing
`t = √n`, the tangent line of `log` at `16` gives `log n = 2 log t ≤ 8 log 2 - 2 + t / 8`. -/
private theorem sqrt_mul_one_add_log_lt_pi_mul {n p : ℝ} (hn : 0 < n) (hnp : n < 8 * p)
    (hp : 37 ≤ p) : √n * (1 + Real.log n) < π * p := by
  set t := √n
  have ht0 : 0 < t := Real.sqrt_pos.mpr hn
  have hts : t ^ 2 = n := Real.sq_sqrt hn.le
  have hlog_n : Real.log n = 2 * Real.log t := by
    rw [← hts, Real.log_pow]
    norm_num
  have hlog_t : Real.log t ≤ 4 * Real.log 2 + t / 16 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t / 16 by positivity)
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_div ht0.ne' (by norm_num), h16] at h
    linarith
  have hl2 := Real.log_two_lt_d9
  have hpi := Real.pi_gt_d2
  have hkey : t * (1 + Real.log n) ≤ 4.5452 * t + n / 8 := by
    rw [hlog_n, ← hts]
    nlinarith
  have ht_le : 4.5452 * t ≤ 2.14 * p := by
    nlinarith
  have hpi_mul : 3.14 * p < π * p := by nlinarith
  linarith

section Model

variable (n : ℕ) [NeZero n]

/-- The discriminant of `ℚ(√(-n))` is `-n` when `n` is squarefree and `n ≡ 3 (mod 4)`. -/
private theorem discr_neg_eq (hsf : Squarefree n) (hn4 : n % 4 = 3) :
    discr (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) = -n :=
  QuadraticAlgebra.discr_eq_of_mod_four_eq_one (Int.squarefree_natCast.mpr hsf).neg (by omega)

/-- `ℚ(√(-n))` has the properties of `exists_auxiliaryQuadraticField` as soon as `n` is squarefree
with `n ≡ 7 (mod 8)`, `-n` is a quadratic nonresidue modulo `p`, and the class number of `ℚ(√(-n))`
is less than `p`. -/
private theorem exists_auxiliaryQuadraticField_of_squarefree (p : ℕ) [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hsf : Squarefree n) (hn8 : n % 8 = 7) (hleg : legendreSym p (-n) = -1)
    (hh : classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) < p) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ IsTotallyComplex K ∧
          ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
            Ideal.span ({2} : Set (𝓞 K)) = P * Q ∧
            (Ideal.span {(p : 𝓞 K)}).IsPrime ∧ ¬ p ∣ classNumber K := by
  have hK : finrank ℚ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) = 2 :=
    QuadraticAlgebra.finrank_eq_two _ _
  have hD := discr_neg_eq n hsf (by omega)
  have h2 : fundamentalDiscriminantChar _ (isFundamentalDiscr_discr hK) (2 : ℕ) = 1 := by
    rw [Nat.cast_ofNat]
    exact (fundamentalDiscriminantChar_two_eq_one_iff _).mpr (by rw [hD]; omega)
  have hχp : fundamentalDiscriminantChar _ (isFundamentalDiscr_discr hK) p = -1 := by
    have h := (fundamentalDiscriminantChar_natCast_eq_legendreSym (isFundamentalDiscr_discr hK)
      hp2).trans
      (by rwa [hD] : legendreSym p (discr (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) = -1)
    rwa [Int.cast_natCast] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, Q, hP, hQ, hPQ, hPQ2⟩ :=
    exists_span_natCast_eq_mul_of_fundamentalDiscriminantChar_discr_eq_one hK 2 h2
  refine ⟨_, inferInstance, inferInstance, hK,
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by simpa using NeZero.pos n),
    P, Q, hP, hQ, hPQ, by rw [← hPQ2, Nat.cast_ofNat],
    isPrime_span_natCast_of_fundamentalDiscriminantChar_discr_eq_neg_one hK p hχp,
    Nat.not_dvd_of_pos_of_lt (classNumber_pos _) hh⟩

end Model

/-- For every odd prime `p` there is a squarefree `n < 8 p` with `n ≡ 7 (mod 8)` such that `-n` is
not a square modulo `p`. -/
private theorem exists_squarefree_lt_not_isSquare_neg (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ n : ℕ, 0 < n ∧ n < 8 * p ∧ Squarefree n ∧ n % 8 = 7 ∧ ¬ IsSquare (-(n : ZMod p)) := by
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  -- `a` represents `-b`, and `a + k p ≡ 7 (mod 8)` for some `k < 8` because `p` is odd.
  set a := (-b).val with ha
  have ha_lt : a < p := ZMod.val_lt _
  have hp_odd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  obtain ⟨k, hk8, hk⟩ : ∃ k < 8, (a + k * p) % 8 = 7 := by
    obtain ⟨k, hk8, hk⟩ := (by decide : ∀ a' < 8, ∀ p' < 8, p' % 2 = 1 →
      ∃ k < 8, (a' + k * p') % 8 = 7) (a % 8) (Nat.mod_lt _ (by norm_num)) (p % 8)
      (Nat.mod_lt _ (by norm_num)) (by omega)
    exact ⟨k, hk8, by interval_cases k <;> omega⟩
  have hm0 : 0 < a + k * p := by omega
  have hm8p : a + k * p < 8 * p := by nlinarith
  -- Remove the square part: `a + k p = r ^ 2 * n` with `n` squarefree.
  obtain ⟨n, r, hn0, hr0, hrn, hsf⟩ := Nat.sq_mul_squarefree_of_pos hm0
  have hr8 : r ^ 2 % 8 = 1 := by
    have hodd : Odd (r ^ 2 * n) := Nat.odd_iff.mpr (by omega)
    have h8 := Nat.eight_dvd_sq_sub_one_of_odd
      ((Nat.odd_pow_iff two_ne_zero).mp (Nat.Odd.of_mul_left hodd))
    have : 0 < r ^ 2 := by positivity
    omega
  have hn8 : n % 8 = 7 := by
    have h := Nat.mul_mod (r ^ 2) n 8
    rw [hr8, hrn, hk] at h
    omega
  have hn_le : n ≤ a + k * p := hrn ▸ Nat.le_mul_of_pos_left n (by positivity)
  refine ⟨n, hn0, by omega, hsf, hn8, fun ⟨c, hc⟩ => hb ⟨r * c, ?_⟩⟩
  have hm : ((a + k * p : ℕ) : ZMod p) = -b := by
    simp [ha]
  rw [← hrn] at hm
  push_cast at hm
  linear_combination hm + (r : ZMod p) ^ 2 * hc

/-- For `p ≥ 37`, the class number of `ℚ(√(-n))` is less than `p` when `n < 8 p` is squarefree
with `n ≡ 7 (mod 8)`, by the analytic bound `h ≤ √n (1 + log n) / π`. -/
private theorem classNumber_lt_of_lt_eight_mul (n p : ℕ) [NeZero n] (hsf : Squarefree n)
    (hn8 : n % 8 = 7) (hnp : n < 8 * p) (hp : 37 ≤ p) :
    classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) < p := by
  have hK : finrank ℚ (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) = 2 :=
    QuadraticAlgebra.finrank_eq_two _ _
  have hD := discr_neg_eq n hsf (by omega)
  have : IsTotallyComplex (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by simpa using NeZero.pos n)
  have hbound := classNumber_le_sqrt_mul_one_add_log_of_discr_ne hK (by rw [hD]; omega)
    (by rw [hD]; omega)
  have habs : |((discr (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) : ℤ) : ℝ)| = n := by
    rw [hD]
    simp
  rw [habs] at hbound
  have hlt := sqrt_mul_one_add_log_lt_pi_mul (n := n) (p := p)
    (by exact_mod_cast NeZero.pos n) (by exact_mod_cast hnp) (by exact_mod_cast hp)
  rw [← div_lt_iff₀' Real.pi_pos] at hlt
  exact_mod_cast hbound.trans_lt hlt

/-- The odd primes `p < 37`: one of `ℚ(√(-7))`, `ℚ(√(-15))` and `ℚ(√(-31))`, of class numbers
`1`, `2` and `3`, has `p` inert. -/
private theorem exists_auxiliaryQuadraticField_of_lt (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hp37 : p < 37) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ IsTotallyComplex K ∧
          ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
            Ideal.span ({2} : Set (𝓞 K)) = P * Q ∧
            (Ideal.span {(p : 𝓞 K)}).IsPrime ∧ ¬ p ∣ classNumber K := by
  have hsmall : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨
      p = 29 ∨ p = 31 := by
    have := hp.out
    interval_cases p <;> first | omega | (exfalso; norm_num at this)
  -- `ℚ(√(-7))` serves `p = 3, 5, 13, 17, 19, 31`, `ℚ(√(-15))` serves `p = 7, 11, 29`, and
  -- `ℚ(√(-31))` serves `p = 23`.
  have h7 (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq : legendreSym q (-7) = -1)
      (hq1 : 1 < q) := exists_auxiliaryQuadraticField_of_squarefree 7 q hq2
    (by decide +kernel) (by decide) hq
    (by rwa [classNumber_neg_eq_one_of_mem_heegnerDiscriminants (by simp)])
  have h15 (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq : legendreSym q (-15) = -1)
      (hq1 : 2 < q) := exists_auxiliaryQuadraticField_of_squarefree 15 q hq2
    (by decide +kernel) (by decide) hq
    (by rwa [BinaryQuadraticForm.classNumber_neg_fifteen_eq_two])
  have h31 (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq : legendreSym q (-31) = -1)
      (hq1 : 3 < q) := exists_auxiliaryQuadraticField_of_squarefree 31 q hq2
    (by decide +kernel) (by decide) hq
    (by rwa [BinaryQuadraticForm.classNumber_neg_thirty_one_eq_three])
  rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h7 3 hp2 (by norm_num) (by norm_num)
  · exact h7 5 hp2 (by norm_num) (by norm_num)
  · exact h15 7 hp2 (by norm_num) (by norm_num)
  · exact h15 11 hp2 (by norm_num) (by norm_num)
  · exact h7 13 hp2 (by norm_num) (by norm_num)
  · exact h7 17 hp2 (by norm_num) (by norm_num)
  · exact h7 19 hp2 (by norm_num) (by norm_num)
  · exact h31 23 hp2 (by norm_num) (by norm_num)
  · exact h15 29 hp2 (by norm_num) (by norm_num)
  · exact h7 31 hp2 (by norm_num) (by norm_num)

/-- **An auxiliary imaginary quadratic field.** For every odd prime `p` there is an imaginary
quadratic field `K` in which `2` splits into two distinct prime ideals, `p` is inert, and `p` does
not divide the class number of `K` [BKO21, Lemma 3.1]. -/
theorem exists_auxiliaryQuadraticField (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
        finrank ℚ K = 2 ∧ IsTotallyComplex K ∧
          ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
            Ideal.span ({2} : Set (𝓞 K)) = P * Q ∧
            (Ideal.span {(p : 𝓞 K)}).IsPrime ∧ ¬ p ∣ classNumber K := by
  have := Fact.mk hp
  rcases lt_or_ge p 37 with hp37 | hp37
  · exact exists_auxiliaryQuadraticField_of_lt p hp2 hp37
  obtain ⟨n, hn0, hn8p, hsf, hn8, hsq⟩ := exists_squarefree_lt_not_isSquare_neg p hp2
  have : NeZero n := ⟨hn0.ne'⟩
  exact exists_auxiliaryQuadraticField_of_squarefree n p hp2 hsf hn8
    ((legendreSym.eq_neg_one_iff p).mpr (by push_cast; exact hsq))
    (classNumber_lt_of_lt_eight_mul n p hsf hn8 hn8p hp37)

end TauCeti.NumberField
