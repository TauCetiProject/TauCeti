/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.LegendreSymbol.SquareClass

/-!
# The fundamental discriminant of a squarefree radicand

For a squarefree integer `d`, the quadratic field `ℚ(√d)` has discriminant `d` when
`d ≡ 1 (mod 4)` and `4 * d` otherwise. This file packages that assignment as a function
`TauCeti.Multiquadratic.fundamentalDiscriminant` and proves the two facts the genus-field
constructions need of it: for squarefree `d` the value is a fundamental discriminant (so
`FundamentalDiscriminant/Factorization` splits it into prime discriminants), and it differs from
`d` by a square, so it names the *same* quadratic field `ℚ(√d)`.

The genus field of `ℚ(√d)` is the compositum of the `ℚ(√(radicand D*))` over the prime
discriminants `D*` dividing the discriminant of `ℚ(√d)`; this function supplies that discriminant
from the squarefree radicand `d`.

It also records which primes divide the fundamental discriminant, feeding the prime-ramification
law in `Quadratic/Ramification.lean`: a prime coprime to `2` divides it exactly when it divides
`d`, and `2` divides it exactly when `d ≢ 1 (mod 4)`.

## Main definitions and results

* `TauCeti.Multiquadratic.fundamentalDiscriminant`: `d` if `d ≡ 1 (mod 4)`, else `4 * d`, with its
  defining equation `fundamentalDiscriminant_def`.
* `TauCeti.Multiquadratic.isFundamentalDiscr_fundamentalDiscriminant`: for squarefree `d`,
  its fundamental discriminant is a fundamental discriminant.
* `TauCeti.Multiquadratic.exists_sq_mul_eq_fundamentalDiscriminant`: it equals `c² * d` for some
  `c ∈ {1, 2}`, so it lies in the square class of `d`.
* `TauCeti.Multiquadratic.dvd_fundamentalDiscriminant_iff`: for `p` coprime to `2`,
  `p ∣ fundamentalDiscriminant d ↔ p ∣ d` (the ramified odd primes are the divisors of `d`).
* `TauCeti.Multiquadratic.two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one`:
  `2 ∤ fundamentalDiscriminant d ↔ d ≡ 1 (mod 4)` (`2` is unramified exactly then).
* `TauCeti.Multiquadratic.fundamentalDiscriminant_ne_zero`: it is nonzero for nonzero `d`.
* `TauCeti.Multiquadratic.fundamentalDiscriminant_injective`,
  `TauCeti.Multiquadratic.isFundamentalDiscr_fundamentalDiscriminant_iff`,
  `TauCeti.Multiquadratic.existsUnique_squarefree_fundamentalDiscriminant_eq`:
  `fundamentalDiscriminant` is injective on `ℤ` and bijects squarefree integers `d` onto
  fundamental discriminants `D`, with inverse `D` when `D ≡ 1 (mod 4)` and `D / 4` otherwise.
* `TauCeti.Multiquadratic.isSquare_fundamentalDiscriminant_iff`,
  `TauCeti.Multiquadratic.legendreSym_fundamentalDiscriminant`: `fundamentalDiscriminant d` and `d`
  have the same square status whenever `2` is invertible and the same Legendre symbol at every odd
  prime `p`.
* `TauCeti.Multiquadratic.fundamentalDiscriminant_primeDiscriminantRadicand`: a prime discriminant
  is the fundamental discriminant of its own radicand.
-/

public section

namespace TauCeti.Multiquadratic

/-- The **fundamental discriminant** attached to an integer `d`: the discriminant of the quadratic
field `ℚ(√d)` for squarefree `d`, namely `d` when `d ≡ 1 (mod 4)` and `4 * d` otherwise. -/
def fundamentalDiscriminant (d : ℤ) : ℤ := if d % 4 = 1 then d else 4 * d

@[simp] theorem fundamentalDiscriminant_of_mod_four_eq_one {d : ℤ} (hd : d % 4 = 1) :
    fundamentalDiscriminant d = d := ite_eq_left hd

@[simp] theorem fundamentalDiscriminant_of_mod_four_ne_one {d : ℤ} (hd : d % 4 ≠ 1) :
    fundamentalDiscriminant d = 4 * d := ite_eq_right hd

theorem fundamentalDiscriminant_def (d : ℤ) :
    fundamentalDiscriminant d = if d % 4 = 1 then d else 4 * d := by
  by_cases h : d % 4 = 1
  · rw [ite_eq_left h]; exact fundamentalDiscriminant_of_mod_four_eq_one h
  · rw [ite_eq_right h]; exact fundamentalDiscriminant_of_mod_four_ne_one h

/-- `fundamentalDiscriminant d` is `d` or `4 * d`. Implementation helper for
`exists_sq_mul_eq_fundamentalDiscriminant`. -/
private theorem fundamentalDiscriminant_eq_self_or_four_mul (d : ℤ) :
    fundamentalDiscriminant d = d ∨ fundamentalDiscriminant d = 4 * d := by
  by_cases h : d % 4 = 1
  · exact Or.inl (fundamentalDiscriminant_of_mod_four_eq_one h)
  · exact Or.inr (fundamentalDiscriminant_of_mod_four_ne_one h)

/-- `c² * d = fundamentalDiscriminant d` for some `c ∈ {1, 2}`: the fundamental discriminant
differs from `d` by a nonzero square, so `ℚ(√(fundamentalDiscriminant d)) = ℚ(√d)`. The
`c = 1 ∨ c = 2` restriction is part of the statement, so the multiplier is genuinely a
unit-or-`2` square (not the vacuous `c = 0`). -/
theorem exists_sq_mul_eq_fundamentalDiscriminant (d : ℤ) :
    ∃ c : ℤ, (c = 1 ∨ c = 2) ∧ c ^ 2 * d = fundamentalDiscriminant d := by
  rcases fundamentalDiscriminant_eq_self_or_four_mul d with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
  · exact ⟨2, Or.inr rfl, by rw [h]; ring⟩

/-- **The fundamental discriminant of a nonzero integer is nonzero**, being a nonzero square
multiple of it. -/
theorem fundamentalDiscriminant_ne_zero {d : ℤ} (hd : d ≠ 0) :
    fundamentalDiscriminant d ≠ 0 := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  rw [← hcd]
  exact mul_ne_zero (pow_ne_zero 2 (by rcases hc with rfl | rfl <;> norm_num)) hd

/-- **The fundamental discriminant of a squarefree integer is a fundamental discriminant.** When
`d ≡ 1 (mod 4)` the value is `d` itself (`≡ 1 (mod 4)`, squarefree); otherwise `d ≡ 2` or
`3 (mod 4)` (it cannot be `0 (mod 4)`, as `4 = 2²` would break squarefreeness) and the value is
`4 * d`. -/
theorem isFundamentalDiscr_fundamentalDiscriminant {d : ℤ} (hd : Squarefree d) :
    Int.IsFundamentalDiscr (fundamentalDiscriminant d) := by
  have h4 : d % 4 ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ : (4 : ℤ) ∣ d := by omega
    exact absurd (hd 2 ⟨q, by rw [hq]; ring⟩) (by norm_num [Int.isUnit_iff])
  by_cases hmod : d % 4 = 1
  · rw [fundamentalDiscriminant_of_mod_four_eq_one hmod]
    exact Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hmod, hd⟩)
  · rw [fundamentalDiscriminant_of_mod_four_ne_one hmod]
    exact Int.isFundamentalDiscr_four_mul.mpr ⟨hd, by omega⟩

/-- For `p` coprime to `2`, divisibility by `fundamentalDiscriminant d` is the same as divisibility
by `d`: the only extra factor in the `d ≢ 1 (mod 4)` case is `4`, which is coprime to `p`. -/
@[simp] theorem dvd_fundamentalDiscriminant_iff {d p : ℤ} (hp : IsCoprime p 2) :
    p ∣ fundamentalDiscriminant d ↔ p ∣ d := by
  rw [fundamentalDiscriminant_def]
  split_ifs with h
  · exact Iff.rfl
  · -- `p` is coprime to `2`, hence to `4 = 2 * 2`; so `p ∣ 4 * d ↔ p ∣ d`.
    have hp4 : IsCoprime p 4 := by
      have h : IsCoprime p (2 * 2) := hp.mul_right hp
      norm_num at h; exact h
    refine ⟨fun hpd => hp4.dvd_of_dvd_mul_right ?_, fun hpd => hpd.mul_left 4⟩
    rwa [mul_comm] at hpd

/-- The fundamental discriminant is odd exactly when `d ≡ 1 (mod 4)` (otherwise it is `4d`).
Not `@[simp]`: `Int.two_dvd_ne_zero` already normalises `¬ 2 ∣ x` to `x % 2 = 1`, so this `¬ ∣`
left-hand side is not a simp normal form (it is applied explicitly instead). -/
theorem two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one (d : ℤ) :
    ¬ (2 : ℤ) ∣ fundamentalDiscriminant d ↔ d % 4 = 1 := by
  rw [fundamentalDiscriminant_def]; split_ifs with h <;> omega

/-- `fundamentalDiscriminant` is injective on `ℤ`. -/
theorem fundamentalDiscriminant_injective : Function.Injective fundamentalDiscriminant := by
  intro d₁ d₂ h
  rw [fundamentalDiscriminant_def, fundamentalDiscriminant_def] at h
  split_ifs at h <;> omega

/-- Two integers have the same `fundamentalDiscriminant` if and only if they are equal. -/
@[simp] theorem fundamentalDiscriminant_eq_iff {d₁ d₂ : ℤ} :
    fundamentalDiscriminant d₁ = fundamentalDiscriminant d₂ ↔ d₁ = d₂ :=
  fundamentalDiscriminant_injective.eq_iff

/-- `fundamentalDiscriminant d` is a fundamental discriminant if and only if `d` is squarefree. -/
@[simp] theorem isFundamentalDiscr_fundamentalDiscriminant_iff {d : ℤ} :
    Int.IsFundamentalDiscr (fundamentalDiscriminant d) ↔ Squarefree d := by
  refine ⟨fun h ↦ ?_, isFundamentalDiscr_fundamentalDiscriminant⟩
  by_cases hmod : d % 4 = 1
  · rw [fundamentalDiscriminant_of_mod_four_eq_one hmod] at h
    exact ((Int.isFundamentalDiscr_iff_squarefree.mp h).resolve_right (by omega)).2
  · rw [fundamentalDiscriminant_of_mod_four_ne_one hmod] at h
    exact (Int.isFundamentalDiscr_four_mul.mp h).1

/-- The squarefree radicand of a fundamental discriminant `D`, namely `D` when `D ≡ 1 (mod 4)` and
`D / 4` otherwise, is squarefree. -/
theorem squarefree_ite_of_isFundamentalDiscr {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    Squarefree (if D % 4 = 1 then D else D / 4) := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, hsf⟩ | ⟨h0, hsf, -⟩
  · rwa [ite_eq_left h1]
  · rwa [ite_eq_right (by omega)]

/-- Every fundamental discriminant `D` is `fundamentalDiscriminant` of `D` when `D ≡ 1 (mod 4)` and
of `D / 4` otherwise. -/
theorem fundamentalDiscriminant_ite_of_isFundamentalDiscr {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminant (if D % 4 = 1 then D else D / 4) = D := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, -⟩ | ⟨h0, -, hm4⟩
  · rw [ite_eq_left h1, fundamentalDiscriminant_of_mod_four_eq_one h1]
  · rw [ite_eq_right (by omega), fundamentalDiscriminant_of_mod_four_ne_one (by omega)]
    omega

/-- For a fundamental discriminant `D`, `fundamentalDiscriminant d = D` holds if and only if `d` is
`D` (when `D ≡ 1 (mod 4)`) or `D / 4` (otherwise). -/
theorem fundamentalDiscriminant_eq_iff_of_isFundamentalDiscr {D d : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminant d = D ↔ d = if D % 4 = 1 then D else D / 4 := by
  conv_lhs => rw [← fundamentalDiscriminant_ite_of_isFundamentalDiscr hD]
  exact fundamentalDiscriminant_eq_iff

/-- **Bijection between squarefree radicands and fundamental discriminants.** Every fundamental
discriminant `D` is `fundamentalDiscriminant d` for a unique squarefree integer `d`, namely `D`
when `D ≡ 1 (mod 4)` and `D / 4` otherwise. -/
theorem existsUnique_squarefree_fundamentalDiscriminant_eq {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    ∃! d : ℤ, Squarefree d ∧ fundamentalDiscriminant d = D :=
  ⟨if D % 4 = 1 then D else D / 4,
    ⟨squarefree_ite_of_isFundamentalDiscr hD,
      fundamentalDiscriminant_ite_of_isFundamentalDiscr hD⟩,
    fun _ ⟨_, hd⟩ ↦ (fundamentalDiscriminant_eq_iff_of_isFundamentalDiscr hD).mp hd⟩

/-- In any commutative ring in which `2` is a unit, `fundamentalDiscriminant d` is a square if and
only if `d` is a square. -/
theorem isSquare_fundamentalDiscriminant_iff {R : Type*} [CommRing R] (h2 : IsUnit (2 : R))
    (d : ℤ) : IsSquare (fundamentalDiscriminant d : R) ↔ IsSquare (d : R) := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  have hc' : IsUnit (c : R) := by
    rcases hc with rfl | rfl
    · simp
    · simpa using h2
  rw [← hcd, Int.cast_mul, Int.cast_pow]
  refine ⟨fun h ↦ ?_, fun h ↦ (IsSquare.sq (c : R)).mul h⟩
  obtain ⟨u, hu⟩ := hc'
  simpa [← hu, sq, mul_assoc] using (IsSquare.mul_self (↑u⁻¹ : R)).mul h

/-- At an odd prime `p`, `fundamentalDiscriminant d` has the same Legendre symbol as `d`, including
`0` when `p ∣ d`. -/
@[simp]
theorem legendreSym_fundamentalDiscriminant {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (d : ℤ) :
    legendreSym p (fundamentalDiscriminant d) = legendreSym p d := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  rw [← hcd, mul_comm]
  refine TauCeti.legendreSym_mul_sq ?_
  rcases hc with rfl | rfl
  · exact mod_cast (Fact.out : p.Prime).not_dvd_one
  · exact mod_cast mt (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp

/-- **A prime discriminant is the fundamental discriminant of its own radicand.** For an odd prime
discriminant this is the congruence `p* ≡ 1 (mod 4)`; for `-4`, `8`, `-8` it is the factor `4`
removed by `primeDiscriminantRadicand`. So `ℚ(√(radicand D))` is the quadratic field of
discriminant `D`. -/
theorem fundamentalDiscriminant_primeDiscriminantRadicand {D : ℤ} (hD : IsPrimeDiscriminant D) :
    fundamentalDiscriminant (primeDiscriminantRadicand D) = D := by
  rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, _hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hev]
    rcases hev with rfl | rfl | rfl <;> norm_num [fundamentalDiscriminant_def]
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd,
      fundamentalDiscriminant_of_mod_four_eq_one
        (oddPrimeDiscriminant_mod_four_eq_one_iff.mpr hodd)]

end TauCeti.Multiquadratic
