/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.MulChar.Real
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# The primitive discriminant and squarefree radicand of a quadratic character

Every quadratic Dirichlet character `χ` of nonzero level `N`, with values in any commutative ring
`R`, agrees at all integers coprime to `N` with the character of a unique fundamental discriminant
`D` whose absolute value is `χ.conductor`
(`DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`). Explicitly, `D` is `χ.conductor`
when `χ (-1) = 1` and `-χ.conductor` otherwise; the principal character corresponds to `D = 1`.
Conversely, any character at level `N` agreeing on units with a fundamental-discriminant character
is quadratic.

For a complex character `χ`, `MulChar.isQuadratic_iff_forall_im_eq_zero` identifies `χ.IsQuadratic`
with all values of `χ` being real (`∀ a, (χ a).im = 0`), so this attaches a unique primitive
fundamental discriminant to every real Dirichlet character at any positive level.

The assignment is invariant under `DirichletCharacter.changeLevel`: lifting `χ` along `N ∣ M`
preserves both the conductor and the value at `-1`, hence leaves `D` unchanged.

Composing with the bijection `TauCeti.Multiquadratic.fundamentalDiscriminant` between squarefree
integers and fundamental discriminants attaches a unique squarefree radicand `d` (`D` when
`D ≡ 1 (mod 4)` and `D / 4` otherwise) with `|d| ≤ χ.conductor`. At every odd prime `p ∤ N`,
`χ p` is the cast of `legendreSym p D = legendreSym p d`, and when `2 ≠ 0` in `R`, `χ p = -1` holds
if and only if `p ∤ N` and `D` (equivalently `d`) is not a square modulo `p`. The prime `2` is a
genuine exception: `fundamentalDiscriminantChar 5 _ 2 = -1`, whereas `legendreSym 2 5 = 1`.

## Main results

* `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  primitive fundamental discriminant `D` of a quadratic character at any nonzero level `N`.
* `DirichletCharacter.isQuadratic_iff_exists_isFundamentalDiscr_apply_eq`: a character of nonzero
  level is quadratic iff it agrees at integers coprime to `N` with a fundamental-discriminant
  character of level `χ.conductor`.
* `DirichletCharacter.isFundamentalDiscr_conductor_ite`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantCharCast_conductor_ite`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantChar_conductor_ite`: explicit formula
  `if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor` and evaluations in `R` and via `ℤ`.
* `DirichletCharacter.isFundamentalDiscr_changeLevel_apply_eq_iff`: naturality of the primitive
  discriminant under `changeLevel`.
* `DirichletCharacter.existsUnique_squarefree_fundamentalDiscriminant_apply_eq`: existence and
  uniqueness of the squarefree radicand `d` with `|d| ≤ χ.conductor`.
* `DirichletCharacter.apply_prime_eq_legendreSym_of_not_dvd`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare_radicand`: the odd-prime Legendre and
  nonsquare dictionary for both `D` and `d`.

## References

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
Cambridge University Press, 2007, §9.3, pp. 295–297 (Theorem 9.13).
-/

public section

open TauCeti.Multiquadratic

namespace DirichletCharacter

section PrimitiveDiscriminant

variable {R : Type*} [CommRing R]

/-- Any Dirichlet character agreeing on integers coprime to its level with a
fundamental-discriminant character is quadratic. -/
theorem isQuadratic_of_forall_isCoprime_apply_eq_fundamentalDiscriminantCharCast {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    rw [hval n ((ZMod.isUnit_intCast_iff_isCoprime n N).mp ha).symm]
    exact fundamentalDiscriminantCharCast_isQuadratic hD n
  · exact Or.inl (MulChar.map_nonunit χ ha)

/-- A quadratic Dirichlet character `χ` of nonzero level `N` agrees on all integers coprime to `N`
with the character of a fundamental discriminant `D` of absolute value `χ.conductor`. -/
theorem exists_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDc, hval⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_isFundamentalDiscr_apply_eq hχ.primitiveCharacter
  refine ⟨D, hD, hDc, fun n hn ↦ ?_⟩
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn, hval]

/-- **The primitive discriminant of a quadratic character.** Every quadratic Dirichlet character
`χ` of nonzero level `N`, with values in any commutative ring `R`, agrees at all integers coprime
to `N` with the character of a unique fundamental discriminant `D` satisfying `|D| = χ.conductor`
(Montgomery–Vaughan, Theorem 9.13). The principal character corresponds to `D = 1`. -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  obtain ⟨D, hD, hDc, hval⟩ := exists_isFundamentalDiscr_apply_eq hχ
  refine ⟨D, ⟨hD, hDc, hval⟩, fun D' ⟨hD', hD'c, hval'⟩ ↦ ?_⟩
  have hneg : IsCoprime (-1 : ℤ) N := IsCoprime.neg_left isCoprime_one_left
  have hsign : χ (-1) = D.sign := by
    simpa [fundamentalDiscriminantChar_neg_one] using hval (-1) hneg
  have hsign' : χ (-1) = D'.sign := by
    simpa [fundamentalDiscriminantChar_neg_one] using hval' (-1) hneg
  exact (eq_conductor_ite_of_isFundamentalDiscr hχ hD' hD'c hsign').trans
    (eq_conductor_ite_of_isFundamentalDiscr hχ hD hDc hsign).symm

/-- A Dirichlet character `χ` of nonzero level `N` is quadratic if and only if it agrees on all
integers coprime to `N` with the character of a fundamental discriminant of absolute value
`χ.conductor`. -/
theorem isQuadratic_iff_exists_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) :
    χ.IsQuadratic ↔ ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n :=
  ⟨exists_isFundamentalDiscr_apply_eq,
    fun ⟨_, hD, _, hval⟩ ↦ isQuadratic_of_forall_isCoprime_apply_eq_fundamentalDiscriminantCharCast
      hD hval⟩

end PrimitiveDiscriminant

section ExplicitFormula

variable {R : Type*} [CommRing R] [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- For a quadratic character `χ` of nonzero level `N`, its unique fundamental discriminant is
`χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise. -/
private theorem exists_eq_conductor_ite_apply_eq (hχ : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D),
      D = (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDc, hval⟩ := exists_isFundamentalDiscr_apply_eq hχ
  have hsign : χ (-1) = D.sign := by
    simpa [fundamentalDiscriminantChar_neg_one] using
      hval (-1) (IsCoprime.neg_left isCoprime_one_left)
  exact ⟨D, hD, eq_conductor_ite_of_isFundamentalDiscr hχ hD hDc hsign, hval⟩

/-- For any quadratic Dirichlet character `χ` of nonzero level `N`, the integer `χ.conductor` (when
`χ (-1) = 1`) or `-χ.conductor` (otherwise) is a fundamental discriminant. -/
theorem isFundamentalDiscr_conductor_ite (hχ : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  obtain ⟨D, hD, rfl, -⟩ := exists_eq_conductor_ite_apply_eq hχ
  exact hD

/-- At every integer `n` coprime to `N`, a quadratic Dirichlet character `χ` of nonzero level `N`
agrees with `fundamentalDiscriminantCharCast` of `if χ (-1) = 1 then χ.conductor else -χ.conductor`.
-/
theorem apply_eq_fundamentalDiscriminantCharCast_conductor_ite (hχ : χ.IsQuadratic) {n : ℤ}
    (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_conductor_ite hχ) n := by
  obtain ⟨D, hD, rfl, hval⟩ := exists_eq_conductor_ite_apply_eq hχ
  exact hval n hn

/-- Integer-valued form of `apply_eq_fundamentalDiscriminantCharCast_conductor_ite`: at integers
coprime to `N`, `χ n` is the cast to `R` of `fundamentalDiscriminantChar` at the primitive
discriminant. -/
theorem apply_eq_fundamentalDiscriminantChar_conductor_ite (hχ : χ.IsQuadratic) {n : ℤ}
    (hn : IsCoprime n N) :
    χ n = (fundamentalDiscriminantChar _ (isFundamentalDiscr_conductor_ite hχ) n : R) :=
  (apply_eq_fundamentalDiscriminantCharCast_conductor_ite hχ hn).trans
    (fundamentalDiscriminantCharCast_apply _ _)

/-- The cast to `R` of the sign of the primitive discriminant of `χ` equals `χ (-1)`. -/
theorem sign_conductor_ite_cast (hχ : χ.IsQuadratic) :
    ((if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor).sign : R) = χ (-1) := by
  simpa [fundamentalDiscriminantChar_neg_one] using
    (apply_eq_fundamentalDiscriminantChar_conductor_ite hχ
      (IsCoprime.neg_left isCoprime_one_left)).symm

/-- The primitive discriminant formula is positive if and only if `χ` is even (`χ (-1) = 1`). -/
theorem conductor_ite_pos_iff (χ : DirichletCharacter R N) :
    0 < (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) ↔ χ.Even := by
  have hpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  rw [DirichletCharacter.Even]
  split_ifs with h <;> simp [h, hpos]

/-- When `2 ≠ 0` in `R`, the primitive discriminant of a quadratic character `χ` is negative if and
only if `χ` is odd (`χ (-1) = -1`). -/
theorem conductor_ite_neg_iff_odd [NeZero (2 : R)] (hχ : χ.IsQuadratic) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) < 0 ↔ χ.Odd := by
  have hpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  rw [DirichletCharacter.Odd]
  rcases hχ.apply_eq_one_or_eq_neg_one isUnit_one.neg with h | h <;> rw [h]
  · rw [ite_eq_left rfl]
    exact iff_of_false (not_lt_of_gt (Nat.cast_pos.mpr hpos))
      fun h1 ↦ NeZero.ne (2 : R) (by linear_combination h1)
  · have hne : (-1 : R) ≠ 1 := fun h1 ↦ NeZero.ne (2 : R) (by linear_combination -h1)
    rw [ite_eq_right hne]
    exact iff_of_true (neg_neg_of_pos (Nat.cast_pos.mpr hpos)) rfl

/-- The primitive discriminant formula equals `1` if and only if `χ` is principal. -/
theorem conductor_ite_eq_one_iff (χ : DirichletCharacter R N) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 ↔ χ = 1 := by
  refine ⟨fun h ↦ eq_one_iff_conductor_eq_one.mpr ?_, ?_⟩
  · split_ifs at h <;> omega
  · rintro rfl
    rw [conductor_one, MulChar.one_apply isUnit_one.neg, ite_eq_left rfl, Nat.cast_one]

end ExplicitFormula

section Naturality

variable {R : Type*} [CommRing R] {N M : ℕ}

/-- Agreement of `χ` with a fundamental-discriminant character on integers coprime to `N` descends
to agreement of `changeLevel hNM χ` on integers coprime to `M`. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_forall_isCoprime (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn]
  exact hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))

/-- **Naturality of the primitive discriminant under `changeLevel`.** For a quadratic character `χ`
and `N ∣ M`, a fundamental discriminant `D` is the primitive discriminant of `changeLevel hNM χ` at
level `M` if and only if it is the primitive discriminant of `χ` at level `N`. -/
theorem isFundamentalDiscr_changeLevel_apply_eq_iff [NeZero M] (hNM : N ∣ M)
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    (D.natAbs = (changeLevel hNM χ).conductor ∧
        ∀ n : ℤ, IsCoprime n M →
          changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n) ↔
      (D.natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) := by
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ hNM))⟩
  refine ⟨fun ⟨hDc, hvalM⟩ ↦ ?_, fun ⟨hDc, hvalN⟩ ↦ ⟨by rwa [conductor_changeLevel], fun n hn ↦
    changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_forall_isCoprime hNM hD hvalN hn⟩⟩
  obtain ⟨D₀, ⟨hD₀, hD₀c, hval₀⟩, _⟩ := existsUnique_isFundamentalDiscr_apply_eq hχ
  obtain ⟨_, _, huniqM⟩ := existsUnique_isFundamentalDiscr_apply_eq (hχ.changeLevel hNM)
  have hDD₀ : D = D₀ :=
    (huniqM D ⟨hD, hDc, hvalM⟩).trans
      (huniqM D₀ ⟨hD₀, by rwa [conductor_changeLevel], fun n hn ↦
        changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_forall_isCoprime hNM hD₀ hval₀
          hn⟩).symm
  subst hDD₀
  exact ⟨hD₀c, hval₀⟩

end Naturality

section RadicandAndOddPrimes

variable {R : Type*} [CommRing R] {N : ℕ} {χ : DirichletCharacter R N}

/-- **The squarefree radicand of a quadratic character.** Every quadratic Dirichlet character `χ`
of nonzero level `N` agrees at all integers coprime to `N` with the character of
`fundamentalDiscriminant d` for a unique squarefree integer `d` satisfying
`|fundamentalDiscriminant d| = χ.conductor`. -/
theorem existsUnique_squarefree_fundamentalDiscriminant_apply_eq [NeZero N]
    (hχ : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d,
      (fundamentalDiscriminant d).natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N →
          χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
            (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniqD⟩ := existsUnique_isFundamentalDiscr_apply_eq hχ
  obtain ⟨d, ⟨hd, rfl⟩, -⟩ := existsUnique_squarefree_fundamentalDiscriminant_eq hD
  refine ⟨d, ⟨hd, hDc, hval⟩, fun d' ⟨hd', hd'c, hval'⟩ ↦ fundamentalDiscriminant_injective ?_⟩
  exact huniqD (fundamentalDiscriminant d')
    ⟨isFundamentalDiscr_fundamentalDiscriminant hd', hd'c, hval'⟩

/-- The squarefree radicand `d` of a quadratic character satisfies `|d| ≤ χ.conductor`. -/
theorem natAbs_le_conductor_of_fundamentalDiscriminant_natAbs_eq {d : ℤ}
    (hdc : (fundamentalDiscriminant d).natAbs = χ.conductor) :
    d.natAbs ≤ χ.conductor :=
  hdc ▸ natAbs_le_natAbs_fundamentalDiscriminant d

/-- The squarefree radicand `d` of a quadratic character equals `1` if and only if `χ = 1`. -/
theorem eq_one_iff_of_squarefree_fundamentalDiscriminant_natAbs_eq [NeZero N] {d : ℤ}
    (hd : Squarefree d) (hdc : (fundamentalDiscriminant d).natAbs = χ.conductor) :
    d = 1 ↔ χ = 1 := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact eq_one_iff_conductor_eq_one.mpr (by simpa using hdc.symm)
  · rintro rfl
    rw [conductor_one] at hdc
    have hD := (isFundamentalDiscr_fundamentalDiscriminant hd).emod_four_eq_zero_or_one
    have hfd : fundamentalDiscriminant d = 1 := by omega
    exact fundamentalDiscriminant_eq_one_iff.mp hfd

/-- At any odd natural number `m` coprime to `N`, a character agreeing with
`fundamentalDiscriminantCharCast R D hD` on integers coprime to `N` takes the value
`jacobiSym D m`. -/
theorem apply_odd_eq_jacobiSym_of_coprime {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {m : ℕ} (hm : _root_.Odd m) (hcop : m.Coprime N) :
    χ m = (jacobiSym D m : R) := by
  have hm' := hval m (Nat.isCoprime_iff_coprime.mpr hcop)
  rw [Int.cast_natCast] at hm'
  rw [hm', fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hm]

/-- **Odd-prime dictionary for the primitive discriminant.** At an odd prime `p ∤ N`, a character
agreeing with `fundamentalDiscriminantCharCast R D hD` on integers coprime to `N` takes the value
`legendreSym p D`. -/
theorem apply_prime_eq_legendreSym_of_not_dvd {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have hp : p.Prime := Fact.out
  have hp' := hval p (Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hpN))
  rw [Int.cast_natCast] at hp'
  rw [hp', fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2]

/-- **Odd-prime dictionary for the squarefree radicand.** At an odd prime `p ∤ N`, a character
agreeing with the character of `D = fundamentalDiscriminant d` on integers coprime to `N` takes the
value `legendreSym p d`. -/
theorem apply_prime_eq_legendreSym_radicand_of_not_dvd {d : ℤ} (hd : Squarefree d)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R
      (fundamentalDiscriminant d) (isFundamentalDiscr_fundamentalDiscriminant hd) n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p d : R) := by
  rw [apply_prime_eq_legendreSym_of_not_dvd _ hval hp2 hpN,
    legendreSym_fundamentalDiscriminant hp2]

/-- Explicit odd-prime formula: for a quadratic character `χ` and an odd prime `p ∤ N`, `χ p` is
the cast of `legendreSym p (if χ (-1) = 1 then χ.conductor else -χ.conductor)`. -/
theorem apply_prime_eq_legendreSym_conductor_ite [NeZero N] [DecidableEq R] (hχ : χ.IsQuadratic)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) : R) :=
  apply_prime_eq_legendreSym_of_not_dvd (isFundamentalDiscr_conductor_ite hχ)
    (fun _ hn ↦ apply_eq_fundamentalDiscriminantCharCast_conductor_ite hχ hn) hp2 hpN

/-- An integer whose absolute value is `χ.conductor` is nonzero modulo any `p ∤ N`. -/
private theorem intCast_ne_zero_of_natAbs_eq_conductor {D : ℤ} (hDc : D.natAbs = χ.conductor)
    {p : ℕ} (hpN : ¬ p ∣ N) : (D : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  exact fun hdvd ↦ hpN (hdvd.trans (hDc ▸ χ.conductor_dvd_level))

/-- When `2 ≠ 0` in `R`, at an odd prime `p`, `χ p = -1` holds if and only if `p ∤ N` and the
primitive discriminant `D` is not a square modulo `p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare [NeZero (2 : R)] {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) (hDc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (D : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd, not_not])]
    exact iff_of_false (fun h ↦ NeZero.ne (2 : R) (by linear_combination 2 * h)) fun ⟨h, _⟩ ↦ h hpN
  · rw [apply_prime_eq_legendreSym_of_not_dvd hD hval hp2 hpN, ← legendreSym.eq_neg_one_iff,
      and_iff_right hpN]
    rcases legendreSym.eq_one_or_neg_one p (intCast_ne_zero_of_natAbs_eq_conductor hDc hpN)
      with h | h <;> rw [h]
    · exact iff_of_false (fun h1 ↦ NeZero.ne (2 : R) (by linear_combination h1)) (by decide)
    · simp

/-- When `2 ≠ 0` in `R`, at an odd prime `p`, `χ p = 1` holds if and only if `p ∤ N` and the
primitive discriminant `D` is a square modulo `p`. -/
theorem apply_prime_eq_one_iff_isSquare [NeZero (2 : R)] {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) (hDc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    χ p = 1 ↔ ¬ p ∣ N ∧ IsSquare (D : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd, not_not])]
    exact iff_of_false (fun h ↦ NeZero.ne (2 : R) (by linear_combination -2 * h))
      fun ⟨h, _⟩ ↦ h hpN
  · have hpD := intCast_ne_zero_of_natAbs_eq_conductor hDc hpN
    rw [apply_prime_eq_legendreSym_of_not_dvd hD hval hp2 hpN, ← legendreSym.eq_one_iff p hpD,
      and_iff_right hpN]
    rcases legendreSym.eq_one_or_neg_one p hpD with h | h <;> rw [h]
    · simp
    · exact iff_of_false (fun h1 ↦ NeZero.ne (2 : R) (by linear_combination -h1)) (by decide)

/-- When `2 ≠ 0` in `R`, at an odd prime `p`, `χ p = -1` holds if and only if `p ∤ N` and the
squarefree radicand `d` of `χ` is not a square modulo `p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare_radicand [NeZero (2 : R)] {d : ℤ}
    (hd : Squarefree d) (hdc : (fundamentalDiscriminant d).natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R
      (fundamentalDiscriminant d) (isFundamentalDiscr_fundamentalDiscriminant hd) n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (d : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [apply_prime_eq_neg_one_iff_not_isSquare (isFundamentalDiscr_fundamentalDiscriminant hd) hdc
    hval hp hp2, ← legendreSym.eq_neg_one_iff, ← legendreSym.eq_neg_one_iff,
    legendreSym_fundamentalDiscriminant hp2]

/-- When `2 ≠ 0` in `R`, at an odd prime `p`, `χ p = 1` holds if and only if `p ∤ N` and the
squarefree radicand `d` of `χ` is a square modulo `p`. -/
theorem apply_prime_eq_one_iff_isSquare_radicand [NeZero (2 : R)] {d : ℤ}
    (hd : Squarefree d) (hdc : (fundamentalDiscriminant d).natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R
      (fundamentalDiscriminant d) (isFundamentalDiscr_fundamentalDiscriminant hd) n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    χ p = 1 ↔ ¬ p ∣ N ∧ IsSquare (d : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [apply_prime_eq_one_iff_isSquare (isFundamentalDiscr_fundamentalDiscriminant hd) hdc hval hp
    hp2]
  refine and_congr_right fun hpN ↦ ?_
  have hpD := intCast_ne_zero_of_natAbs_eq_conductor hdc hpN
  have hpd : (d : ZMod p) ≠ 0 := by
    obtain ⟨c, _, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
    intro hz
    apply hpD
    rw [← hcd, Int.cast_mul, hz, mul_zero]
  rw [← legendreSym.eq_one_iff p hpD, ← legendreSym.eq_one_iff p hpd,
    legendreSym_fundamentalDiscriminant hp2]

/-- Direct nonsquare witness for the explicit primitive discriminant at an odd prime `p` with
`χ p = -1`. -/
theorem not_isSquare_conductor_ite_of_apply_prime_eq_neg_one [NeZero N] [DecidableEq R]
    [NeZero (2 : R)] (hχ : χ.IsQuadratic) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hval : χ p = -1) :
    ¬ IsSquare (((if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor : ℤ)) : ZMod p) :=
  ((apply_prime_eq_neg_one_iff_not_isSquare (isFundamentalDiscr_conductor_ite hχ)
    (by split_ifs <;> simp)
    (fun _ hn ↦ apply_eq_fundamentalDiscriminantCharCast_conductor_ite hχ hn) hp hp2).mp hval).2

end RadicandAndOddPrimes

/-! ### Concrete checks -/

section ConcreteChecks

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- Fundamental discriminants `1, -4, 8, -8, 5, -3, 12` vs non-fundamental `-1` and `-12`.
private example :
    Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧ Int.IsFundamentalDiscr 8 ∧
      Int.IsFundamentalDiscr (-8) ∧ Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
      Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-1) ∧
      ¬ Int.IsFundamentalDiscr (-12) := by
  have h1 : Int.IsFundamentalDiscr 1 := by
    simpa [fundamentalDiscriminant_of_mod_four_eq_one (d := 1) rfl] using
      isFundamentalDiscr_fundamentalDiscriminant (d := 1) squarefree_one
  have h5 : Int.IsFundamentalDiscr 5 := by
    simpa [oddPrimeDiscriminant_of_mod_four_eq_one (p := 5) (by norm_num)] using
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_five (by decide)).isFundamentalDiscr
  have hm3 : Int.IsFundamentalDiscr (-3) := by
    simpa [oddPrimeDiscriminant_of_mod_four_eq_three (p := 3) (by norm_num)] using
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_three (by decide)).isFundamentalDiscr
  have h12 : Int.IsFundamentalDiscr 12 := by
    simpa using isPrimeDiscriminant_neg_four.isFundamentalDiscr.mul hm3 (by decide)
  refine ⟨h1, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr, isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    h5, hm3, h12, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.emod_four_eq_zero_or_one
    omega
  · have h12' : (-12 : ℤ) = 4 * (-3) := by norm_num
    rw [h12', Int.isFundamentalDiscr_four_mul] at h
    omega

-- A real complex character at any positive level has a unique fundamental discriminant.
private example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hreal : ∀ a, (χ a).im = 0) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast ℂ D hD n :=
  existsUnique_isFundamentalDiscr_apply_eq (MulChar.isQuadratic_iff_forall_im_eq_zero.mpr hreal)

-- Principal character at level `6`: conductor `1` and primitive discriminant `D = 1`.
private example :
    let χ : DirichletCharacter ℂ 6 := 1
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 :=
  (conductor_ite_eq_one_iff (1 : DirichletCharacter ℂ 6)).mpr rfl

-- `χ₄` lifted to level `12`: conductor `4`, primitive discriminant `-4`, value `0` at `3` while
-- `fundamentalDiscriminantChar (-4) _ 3 = -1`.
private example :
    let χ : DirichletCharacter ℤ 12 := changeLevel (by decide : 4 ∣ 12) ZMod.χ₄
    χ.conductor = 4 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = -4 ∧
      χ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr
        (3 : ℤ) = -1 := by
  dsimp only
  have hc : (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄).conductor = 4 := by
    rw [conductor_changeLevel]
    exact conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [hc, changeLevel_apply_neg_one]
    decide
  · exact MulChar.map_nonunit _ (by decide)
  · rw [fundamentalDiscriminantChar_neg_four]
    decide

-- Running conductor-`12` example `χ₄ · (Legendre mod 3)`: conductor `12`, discriminant `D = 12`
-- (radicand `d = 3`), values `-1, -1, 1` at `5, 7, 11`, and unchanged under lift to level `24`.
private example :
    let χ₁₂ : DirichletCharacter ℤ 12 :=
      changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
        changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))
    χ₁₂.conductor = 12 ∧
      (if χ₁₂ (-1) = 1 then (χ₁₂.conductor : ℤ) else -χ₁₂.conductor) = 12 ∧
      χ₁₂ (5 : ℤ) = -1 ∧ χ₁₂ (7 : ℤ) = -1 ∧ χ₁₂ (11 : ℤ) = 1 ∧
      (if changeLevel (by decide : 12 ∣ 24) χ₁₂ (-1) = 1
        then ((changeLevel (by decide : 12 ∣ 24) χ₁₂).conductor : ℤ)
        else -(changeLevel (by decide : 12 ∣ 24) χ₁₂).conductor) = 12 ∧
      fundamentalDiscriminant 3 = 12 ∧
      legendreSym 5 12 = -1 ∧ legendreSym 5 3 = -1 ∧
      legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0 := by
  dsimp only
  have hid : (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℤ) = quadraticChar (ZMod 3) :=
    MulChar.ext fun _ ↦ by simp
  have hc4 : (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄).conductor = 4 := by
    rw [conductor_changeLevel]
    exact conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  have hc3 : (changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))).conductor = 3 := by
    rw [← hid]
    exact conductor_changeLevel_quadraticChar (R := ℤ) (by simp) (by decide) (by decide : 3 ∣ 12)
  have hc12 : (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
      changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))).conductor = 12 := by
    rw [conductor_mul_of_coprime (by rw [hc4, hc3]; decide), hc4, hc3]
  have hneg : (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
      changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))) (-1) = 1 := by
    rw [MulChar.mul_apply, changeLevel_apply_neg_one, changeLevel_apply_neg_one]
    decide
  have hite : (if (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
      changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))) (-1) = 1
      then ((changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
        changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))).conductor : ℤ)
      else -(changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
        changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))).conductor) = 12 := by
    rw [hneg, hc12, ite_eq_left rfl]
    rfl
  refine ⟨hc12, hite, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [MulChar.mul_apply,
      changeLevel_eq_cast_of_dvd' _ (by decide) (by decide : IsCoprime (5 : ℤ) 12),
      changeLevel_eq_cast_of_dvd' _ (by decide) (by decide : IsCoprime (5 : ℤ) 12)]
    decide
  · rw [MulChar.mul_apply,
      changeLevel_eq_cast_of_dvd' _ (by decide) (by decide : IsCoprime (7 : ℤ) 12),
      changeLevel_eq_cast_of_dvd' _ (by decide) (by decide : IsCoprime (7 : ℤ) 12)]
    decide
  · rw [MulChar.mul_apply,
      changeLevel_eq_cast_of_dvd' _ (by decide) (by decide : IsCoprime (11 : ℤ) 12),
      changeLevel_eq_cast_of_dvd' _ (by decide) (by decide : IsCoprime (11 : ℤ) 12)]
    decide
  · rw [changeLevel_apply_neg_one, conductor_changeLevel, hite]
  · rw [fundamentalDiscriminant_def]
    norm_num

-- At `p = 2`, the Kronecker character of `D = 5` is `-1` while `legendreSym 2 5 = 1`.
private example :
    ∃ h5 : Int.IsFundamentalDiscr 5,
      fundamentalDiscriminantChar 5 h5 2 = -1 ∧ legendreSym 2 5 = 1 := by
  have h5 : Int.IsFundamentalDiscr 5 := by
    simpa [oddPrimeDiscriminant_of_mod_four_eq_one (p := 5) (by norm_num)] using
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_five (by decide)).isFundamentalDiscr
  refine ⟨h5, ?_, by norm_num⟩
  rw [fundamentalDiscriminantChar_two]
  decide

end ConcreteChecks

end DirichletCharacter
