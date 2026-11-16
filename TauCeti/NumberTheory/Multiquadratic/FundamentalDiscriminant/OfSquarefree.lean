/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic

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
* `TauCeti.Multiquadratic.fundamentalDiscriminant_primeDiscriminantRadicand`: a prime discriminant
  is the fundamental discriminant of its own radicand.
* `TauCeti.Multiquadratic.fundamentalDiscriminantRadicand`: `D` if `D ≡ 1 (mod 4)`, else `D / 4`,
  the left inverse of `fundamentalDiscriminant` on all integers and its two-sided inverse between
  squarefree integers and fundamental discriminants (`fundamentalDiscriminantEquiv`).
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

/-! ### The squarefree radicand of a fundamental discriminant -/

/-- The **squarefree radicand** attached to a fundamental discriminant `D`: `D` itself when
`D ≡ 1 (mod 4)` and `D / 4` otherwise, so that `ℚ(√D) = ℚ(√(fundamentalDiscriminantRadicand D))`. -/
def fundamentalDiscriminantRadicand (D : ℤ) : ℤ := if D % 4 = 1 then D else D / 4

/-- `fundamentalDiscriminantRadicand D = D` when `D ≡ 1 (mod 4)`. -/
@[simp] theorem fundamentalDiscriminantRadicand_of_mod_four_eq_one {D : ℤ} (hD : D % 4 = 1) :
    fundamentalDiscriminantRadicand D = D := ite_eq_left hD

/-- `fundamentalDiscriminantRadicand D = D / 4` when `D ≢ 1 (mod 4)`. -/
@[simp] theorem fundamentalDiscriminantRadicand_of_mod_four_ne_one {D : ℤ} (hD : D % 4 ≠ 1) :
    fundamentalDiscriminantRadicand D = D / 4 := ite_eq_right hD

/-- Defining equation for `fundamentalDiscriminantRadicand`. -/
theorem fundamentalDiscriminantRadicand_def (D : ℤ) :
    fundamentalDiscriminantRadicand D = if D % 4 = 1 then D else D / 4 := by rfl

/-- `fundamentalDiscriminantRadicand` is a left inverse to `fundamentalDiscriminant` on all
integers (no squarefreeness needed). -/
@[simp] theorem fundamentalDiscriminantRadicand_fundamentalDiscriminant (d : ℤ) :
    fundamentalDiscriminantRadicand (fundamentalDiscriminant d) = d := by
  by_cases hd : d % 4 = 1
  · rw [fundamentalDiscriminant_of_mod_four_eq_one hd,
      fundamentalDiscriminantRadicand_of_mod_four_eq_one hd]
  · rw [fundamentalDiscriminant_of_mod_four_ne_one hd,
      fundamentalDiscriminantRadicand_of_mod_four_ne_one (by omega),
      Int.mul_ediv_cancel_left d (by norm_num)]

/-- `fundamentalDiscriminantRadicand` is a left inverse of `fundamentalDiscriminant`. -/
theorem leftInverse_fundamentalDiscriminantRadicand :
    Function.LeftInverse fundamentalDiscriminantRadicand fundamentalDiscriminant :=
  fundamentalDiscriminantRadicand_fundamentalDiscriminant

/-- `fundamentalDiscriminant` is injective on `ℤ`. -/
theorem fundamentalDiscriminant_injective : Function.Injective fundamentalDiscriminant :=
  leftInverse_fundamentalDiscriminantRadicand.injective

/-- Two integers have the same `fundamentalDiscriminant` if and only if they are equal. -/
@[simp] theorem fundamentalDiscriminant_inj {d₁ d₂ : ℤ} :
    fundamentalDiscriminant d₁ = fundamentalDiscriminant d₂ ↔ d₁ = d₂ :=
  fundamentalDiscriminant_injective.eq_iff

/-- `fundamentalDiscriminant d = 0` if and only if `d = 0`. -/
@[simp] theorem fundamentalDiscriminant_eq_zero_iff {d : ℤ} :
    fundamentalDiscriminant d = 0 ↔ d = 0 := by
  simpa using @fundamentalDiscriminant_inj d 0

/-- `fundamentalDiscriminant d = 1` if and only if `d = 1`. -/
@[simp] theorem fundamentalDiscriminant_eq_one_iff {d : ℤ} :
    fundamentalDiscriminant d = 1 ↔ d = 1 := by
  simpa using @fundamentalDiscriminant_inj d 1

/-- `fundamentalDiscriminant d` has the same sign as `d`. -/
@[simp] theorem sign_fundamentalDiscriminant (d : ℤ) :
    (fundamentalDiscriminant d).sign = d.sign := by
  rw [fundamentalDiscriminant_def]
  split_ifs with h
  · rfl
  · rw [Int.sign_mul, Int.sign_eq_one_of_pos (by norm_num), one_mul]

/-- The radicand of a fundamental discriminant is squarefree. -/
theorem squarefree_fundamentalDiscriminantRadicand {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    Squarefree (fundamentalDiscriminantRadicand D) := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, hsf⟩ | ⟨h0, hsf, -⟩
  · rwa [fundamentalDiscriminantRadicand_of_mod_four_eq_one h1]
  · rwa [fundamentalDiscriminantRadicand_of_mod_four_ne_one (by omega)]

/-- Every fundamental discriminant is the `fundamentalDiscriminant` of its radicand. -/
theorem fundamentalDiscriminant_fundamentalDiscriminantRadicand {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminant (fundamentalDiscriminantRadicand D) = D := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨h1, -⟩ | ⟨h0, -, hmod⟩
  · rw [fundamentalDiscriminantRadicand_of_mod_four_eq_one h1,
      fundamentalDiscriminant_of_mod_four_eq_one h1]
  · rw [fundamentalDiscriminantRadicand_of_mod_four_ne_one (by omega),
      fundamentalDiscriminant_of_mod_four_ne_one (by rcases hmod with h | h <;> omega),
      Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h0)]

/-- The radicand of a fundamental discriminant is nonzero. -/
theorem fundamentalDiscriminantRadicand_ne_zero {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantRadicand D ≠ 0 :=
  (squarefree_fundamentalDiscriminantRadicand hD).ne_zero

/-- The radicand of a fundamental discriminant has the same sign as the discriminant. -/
theorem sign_fundamentalDiscriminantRadicand {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantRadicand D).sign = D.sign := by
  conv_rhs => rw [← fundamentalDiscriminant_fundamentalDiscriminantRadicand hD,
    sign_fundamentalDiscriminant]

/-- On prime discriminants, `fundamentalDiscriminantRadicand` agrees with
`primeDiscriminantRadicand`. -/
theorem fundamentalDiscriminantRadicand_eq_primeDiscriminantRadicand {P : ℤ}
    (hP : IsPrimeDiscriminant P) :
    fundamentalDiscriminantRadicand P = primeDiscriminantRadicand P := by
  conv_lhs => rw [← fundamentalDiscriminant_primeDiscriminantRadicand hP,
    fundamentalDiscriminantRadicand_fundamentalDiscriminant]

/-- An integer is a fundamental discriminant if and only if it is `fundamentalDiscriminant d` for
some squarefree integer `d`. -/
theorem isFundamentalDiscr_iff_exists_squarefree {D : ℤ} :
    Int.IsFundamentalDiscr D ↔ ∃ d : ℤ, Squarefree d ∧ fundamentalDiscriminant d = D :=
  ⟨fun hD => ⟨fundamentalDiscriminantRadicand D, squarefree_fundamentalDiscriminantRadicand hD,
      fundamentalDiscriminant_fundamentalDiscriminantRadicand hD⟩,
    fun ⟨_, hd, h⟩ => h ▸ isFundamentalDiscr_fundamentalDiscriminant hd⟩

/-- Every fundamental discriminant is `fundamentalDiscriminant d` for a unique squarefree integer
`d`, namely `fundamentalDiscriminantRadicand D`. -/
theorem existsUnique_squarefree_fundamentalDiscriminant_eq {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    ∃! d : ℤ, Squarefree d ∧ fundamentalDiscriminant d = D :=
  ⟨fundamentalDiscriminantRadicand D,
    ⟨squarefree_fundamentalDiscriminantRadicand hD,
      fundamentalDiscriminant_fundamentalDiscriminantRadicand hD⟩,
    fun _ ⟨_, hd⟩ => fundamentalDiscriminant_injective
      (hd.trans (fundamentalDiscriminant_fundamentalDiscriminantRadicand hD).symm)⟩

/-- `fundamentalDiscriminant` and `fundamentalDiscriminantRadicand` form a bijection between
squarefree integers and fundamental discriminants. -/
def fundamentalDiscriminantEquiv :
    {d : ℤ // Squarefree d} ≃ {D : ℤ // Int.IsFundamentalDiscr D} where
  toFun d := ⟨fundamentalDiscriminant d.1, isFundamentalDiscr_fundamentalDiscriminant d.2⟩
  invFun D := ⟨fundamentalDiscriminantRadicand D.1, squarefree_fundamentalDiscriminantRadicand D.2⟩
  left_inv d := Subtype.ext (fundamentalDiscriminantRadicand_fundamentalDiscriminant d.1)
  right_inv D := Subtype.ext (fundamentalDiscriminant_fundamentalDiscriminantRadicand D.2)

/-- Coercing `fundamentalDiscriminantEquiv d` to `ℤ` applies `fundamentalDiscriminant`. -/
@[simp] theorem coe_fundamentalDiscriminantEquiv (d : {d : ℤ // Squarefree d}) :
    (fundamentalDiscriminantEquiv d : ℤ) = fundamentalDiscriminant d := by rfl

/-- Coercing `fundamentalDiscriminantEquiv.symm D` to `ℤ` applies
`fundamentalDiscriminantRadicand`. -/
@[simp] theorem coe_fundamentalDiscriminantEquiv_symm (D : {D : ℤ // Int.IsFundamentalDiscr D}) :
    (fundamentalDiscriminantEquiv.symm D : ℤ) = fundamentalDiscriminantRadicand D := by rfl

end TauCeti.Multiquadratic
