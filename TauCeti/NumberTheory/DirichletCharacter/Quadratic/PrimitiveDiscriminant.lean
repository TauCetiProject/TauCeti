/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.MulChar.Real
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# The primitive discriminant of a quadratic Dirichlet character

A quadratic Dirichlet character `χ` of any nonzero level `N`, with values in any commutative ring
`R`, agrees at every integer coprime to `N` with the scalar realization
`fundamentalDiscriminantCharCast R D hD` of the character of a unique fundamental discriminant `D`
whose absolute value is `χ.conductor`
(`MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`). Equivalently, `χ` is the lift via
`DirichletCharacter.changeLevel` of `fundamentalDiscriminantCharCast R D hD` from level
`|D| = χ.conductor` to level `N`
(`MulChar.IsQuadratic.eq_changeLevel_fundamentalDiscriminantCharCast_conductor_ite`). Explicitly,
`D` is `χ.conductor` when `χ (-1) = 1` and `-χ.conductor` otherwise, including `D = 1` for the
principal character at any positive level. For complex characters,
`MulChar.isQuadratic_iff_forall_im_eq_zero` identifies the quadratic characters with the
real-valued ones (`∀ a, (χ a).im = 0`).

The proof passes to `χ.primitiveCharacter`, which is primitive and quadratic at the nonzero level
`χ.conductor` and has the same value at `-1` as `χ`. Applying the primitive classification
`DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite` gives `D` and the
agreement of `χ.primitiveCharacter` with `fundamentalDiscriminantCharCast R D hD` at all integers,
hence the agreement of `χ` at integers coprime to `N`. Uniqueness uses `|D| = χ.conductor` together
with `χ (-1) = sign D` when `2 ≠ 0` in `R`, and `|D| = 1 ⟹ D = 1` when `2 = 0` (where every
quadratic character is principal). Note that in characteristic zero, `|D| = χ.conductor` is
automatic for any lift of `fundamentalDiscriminantCharCast R D hD`
(`MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_eq_changeLevel`), whereas when `2 = 0` in `R`
both `D = 1` and `D = -4` lift to the trivial character modulo `4`, so fixing `|D| = χ.conductor`
is what makes `D` unique over every commutative ring.

Combining this with `Int.IsFundamentalDiscr.existsUnique_squarefree_fundamentalDiscriminant_eq`
between fundamental discriminants `D` and squarefree radicands `d` (`D = fundamentalDiscriminant d`)
yields the unique squarefree radicand of `χ`
(`MulChar.IsQuadratic.existsUnique_squarefree_fundamentalDiscriminant_apply_eq`) and the odd-prime
dictionary: at an odd prime `p ∤ N`, `χ p` is the cast of `legendreSym p D = legendreSym p d`, and
when `2 ≠ 0` in `R` a value `χ p = -1` at an odd prime `p` (which automatically forces `p ∤ N`)
certifies that neither `D` nor `d` is a square modulo `p`.

## Main results

* `MulChar.IsQuadratic.isFundamentalDiscr_conductor_ite`,
  `MulChar.IsQuadratic.eq_changeLevel_fundamentalDiscriminantCharCast_conductor_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_conductor_ite`: the signed conductor
  `if χ (-1) = 1 then χ.conductor else -χ.conductor` of a quadratic character at level `N ≠ 0` is a
  fundamental discriminant whose character lifts to `χ`.
* `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  fundamental discriminant `D` with `|D| = χ.conductor` whose character agrees with `χ` on integers
  coprime to `N`.
* `DirichletCharacter.isQuadratic_iff_exists_isFundamentalDiscr_eq_changeLevel`,
  `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_eq_changeLevel`: characterization of
  quadratic Dirichlet characters at level `N ≠ 0` as lifts of fundamental-discriminant characters,
  with uniqueness of `D` in characteristic zero without specifying `|D| = χ.conductor`.
* `DirichletCharacter.conductor_ite_changeLevel`,
  `DirichletCharacter.changeLevel_apply_eq_fundamentalDiscriminantCharCast`: invariance of the
  signed conductor and coprime-integer agreement under `DirichletCharacter.changeLevel`.
* `MulChar.IsQuadratic.existsUnique_squarefree_fundamentalDiscriminant_apply_eq`: the unique
  squarefree radicand `d` attached to a quadratic Dirichlet character.
* `DirichletCharacter.apply_natCast_eq_jacobiSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_natCast_prime_eq_legendreSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_natCast_prime_eq_legendreSym_of_fundamentalDiscriminant_eq`: evaluation
  at odd naturals and odd primes via Jacobi and Legendre symbols in `D` and in `d`.
* `DirichletCharacter.not_isSquare_of_apply_natCast_prime_eq_neg_one`,
  `DirichletCharacter.not_isSquare_of_fundamentalDiscriminant_eq_of_apply_natCast_prime_eq_neg_one`:
  when `2 ≠ 0` in `R` and `p` is an odd prime with `χ p = -1`, neither `D` nor `d` is a square
  modulo `p`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge University Press, 2007, Theorem 9.2 (p. 283) and §9.3, Theorem 9.13 (pp. 295–297).
-/

public section

open TauCeti.Multiquadratic

namespace DirichletCharacter

section SignedConductor

variable {R : Type*} [CommMonoidWithZero R] [DecidableEq R]

/-- The signed conductor `if χ (-1) = 1 then χ.conductor else -χ.conductor` has absolute value
`χ.conductor`. -/
@[simp]
theorem natAbs_conductor_ite {N : ℕ} (χ : DirichletCharacter R N) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor).natAbs = χ.conductor := by
  split_ifs <;> simp

/-- The absolute value of the signed conductor divides the level. -/
theorem natAbs_conductor_ite_dvd_level {N : ℕ} (χ : DirichletCharacter R N) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor).natAbs ∣ N :=
  (natAbs_conductor_ite χ).symm ▸ χ.conductor_dvd_level

/-- Raising a Dirichlet character to a nonzero multiple of its level preserves both its value at
`-1` and its conductor, hence its signed conductor. -/
theorem conductor_ite_changeLevel {N M : ℕ} [NeZero M] (hNM : N ∣ M)
    (χ : DirichletCharacter R N) :
    (if changeLevel hNM χ (-1) = 1 then ((changeLevel hNM χ).conductor : ℤ)
      else -(changeLevel hNM χ).conductor) =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  rw [changeLevel_apply_neg_one, conductor_changeLevel]

end SignedConductor

variable {R : Type*} [CommRing R]

/-- Any fundamental discriminant `D` with `|D| = χ.conductor` whose character agrees at `-1` with a
quadratic character `χ` of level `N ≠ 0` equals `χ.conductor` when `χ (-1) = 1` and `-χ.conductor`
otherwise. -/
theorem _root_.MulChar.IsQuadratic.eq_conductor_ite_of_isFundamentalDiscr [DecidableEq R]
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic)
    {D : ℤ} (hD : Int.IsFundamentalDiscr D) (hDc : D.natAbs = χ.conductor)
    (hneg : χ (-1 : ℤ) = fundamentalDiscriminantCharCast R D hD (-1 : ℤ)) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hneg' : χ.primitiveCharacter (-1 : ℤ) = fundamentalDiscriminantCharCast R D hD (-1 : ℤ) := by
    rw [χ.primitiveCharacter_apply_of_isCoprime (IsCoprime.neg_left isCoprime_one_left), hneg]
  simpa [← changeLevel_apply_neg_one χ.conductor_dvd_level χ.primitiveCharacter,
    changeLevel_primitiveCharacter] using
    χ.primitiveCharacter_isPrimitive.eq_ite_of_isFundamentalDiscr hχ.primitiveCharacter hD hDc hneg'

/-- The signed conductor of a quadratic Dirichlet character of nonzero level is a fundamental
discriminant. -/
theorem _root_.MulChar.IsQuadratic.isFundamentalDiscr_conductor_ite [DecidableEq R] {N : ℕ}
    [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hχ.primitiveCharacter
  rwa [← changeLevel_apply_neg_one χ.conductor_dvd_level χ.primitiveCharacter,
    changeLevel_primitiveCharacter] at h

/-- **Every quadratic Dirichlet character is the lift of the Kronecker character of its signed
conductor.** -/
theorem _root_.MulChar.IsQuadratic.eq_changeLevel_fundamentalDiscriminantCharCast_conductor_ite
    [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    χ = changeLevel (natAbs_conductor_ite_dvd_level χ)
      (fundamentalDiscriminantCharCast R _ hχ.isFundamentalDiscr_conductor_ite) := by
  refine MulChar.ext' fun x ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  refine apply_intCast_eq_of_forall_isCoprime rfl (fun m hm ↦ ?_) n
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite
    hχ.primitiveCharacter m
  rw [← χ.primitiveCharacter_apply_of_isCoprime hm, hprim, changeLevel_eq_cast_of_dvd' _ _ hm]
  simp only [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast]
  rw [← changeLevel_apply_neg_one χ.conductor_dvd_level χ.primitiveCharacter,
    changeLevel_primitiveCharacter]

/-- At every integer coprime to the level `N`, a quadratic Dirichlet character agrees with the
character of its signed conductor. -/
theorem _root_.MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_conductor_ite
    [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic)
    {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ hχ.isFundamentalDiscr_conductor_ite n := by
  conv_lhs => rw [hχ.eq_changeLevel_fundamentalDiscriminantCharCast_conductor_ite]
  exact changeLevel_eq_cast_of_dvd' _ _ hn

/-- **The primitive discriminant of a quadratic Dirichlet character.** For a quadratic Dirichlet
character `χ` of any nonzero level `N`, there is a unique fundamental discriminant `D` with
`|D| = χ.conductor` such that `χ n = fundamentalDiscriminantCharCast R D hD n` at every integer `n`
coprime to `N`. The principal character corresponds to `D = 1` (Montgomery–Vaughan, Theorem 9.13).
-/
theorem _root_.MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  refine ⟨if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor,
    ⟨hχ.isFundamentalDiscr_conductor_ite, natAbs_conductor_ite χ,
      fun n hn ↦ hχ.apply_eq_fundamentalDiscriminantCharCast_conductor_ite hn⟩,
    fun D ⟨hD, hDc, hval⟩ ↦ hχ.eq_conductor_ite_of_isFundamentalDiscr hD hDc
      (hval (-1) (IsCoprime.neg_left isCoprime_one_left))⟩

/-- A Dirichlet character of nonzero level `N` is quadratic if and only if it is the lift to level
`N` of the character of a fundamental discriminant `D` with `|D| ∣ N`. -/
theorem isQuadratic_iff_exists_isFundamentalDiscr_eq_changeLevel {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) :
    χ.IsQuadratic ↔ ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D) (hdvd : D.natAbs ∣ N),
      χ = changeLevel hdvd (fundamentalDiscriminantCharCast R D hD) := by
  classical
  refine ⟨fun hχ ↦ ⟨_, hχ.isFundamentalDiscr_conductor_ite, natAbs_conductor_ite_dvd_level χ,
    hχ.eq_changeLevel_fundamentalDiscriminantCharCast_conductor_ite⟩, ?_⟩
  rintro ⟨D, hD, hdvd, rfl⟩
  exact (fundamentalDiscriminantCharCast_isQuadratic hD).changeLevel hdvd

/-- In characteristic zero, every quadratic Dirichlet character of nonzero level `N` is the lift of
`fundamentalDiscriminantCharCast R D hD` for a unique fundamental discriminant `D`, without
needing to stipulate `|D| = χ.conductor` separately (since `fundamentalDiscriminantCharCast` is
primitive of conductor `|D|`). -/
theorem _root_.MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_eq_changeLevel [CharZero R]
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ (hD : Int.IsFundamentalDiscr D) (hdvd : D.natAbs ∣ N),
      χ = changeLevel hdvd (fundamentalDiscriminantCharCast R D hD) := by
  classical
  refine ⟨if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor,
    ⟨hχ.isFundamentalDiscr_conductor_ite, natAbs_conductor_ite_dvd_level χ,
      hχ.eq_changeLevel_fundamentalDiscriminantCharCast_conductor_ite⟩, ?_⟩
  rintro D ⟨hD, hdvd, rfl⟩
  have hcond :
      D.natAbs = (changeLevel hdvd (fundamentalDiscriminantCharCast R D hD)).conductor := by
    rw [conductor_changeLevel, conductor_fundamentalDiscriminantCharCast]
  refine hχ.eq_conductor_ite_of_isFundamentalDiscr hD hcond ?_
  simp [changeLevel_apply_neg_one]

/-- **Naturality under `changeLevel`.** If `χ` agrees with `fundamentalDiscriminantCharCast R D hD`
at all integers coprime to `N` and `N ∣ M`, then `changeLevel hNM χ` agrees with it at all integers
coprime to `M`. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast {N M : ℕ} (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn,
    hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))]

/-- **The unique squarefree radicand of a quadratic Dirichlet character.** Every quadratic Dirichlet
character `χ` of nonzero level `N` corresponds to a unique squarefree integer `d` such that
`|fundamentalDiscriminant d| = χ.conductor` and `χ` agrees with the character of
`fundamentalDiscriminant d` at all integers coprime to `N`. -/
theorem _root_.MulChar.IsQuadratic.existsUnique_squarefree_fundamentalDiscriminant_apply_eq
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d, (fundamentalDiscriminant d).natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R
        (fundamentalDiscriminant d) (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  obtain ⟨d, ⟨hd, rfl⟩, -⟩ := hD.existsUnique_squarefree_fundamentalDiscriminant_eq
  refine ⟨d, ⟨hd, hDc, hval⟩, fun d' ⟨hd', hDc', hval'⟩ ↦ fundamentalDiscriminant_injective ?_⟩
  exact huniq (fundamentalDiscriminant d') ⟨isFundamentalDiscr_fundamentalDiscriminant hd',
    hDc', hval'⟩

section OddPrimeDictionary

variable {N : ℕ} {χ : DirichletCharacter R N} {D d : ℤ} {hD : Int.IsFundamentalDiscr D}

/-- At an odd natural number `n` coprime to `N`, a character agreeing on coprime integers with
`fundamentalDiscriminantCharCast R D hD` takes the value `(jacobiSym D n : R)`. -/
theorem apply_natCast_eq_jacobiSym_of_forall_isCoprime
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {n : ℕ} (hn : _root_.Odd n) (hcop : n.Coprime N) :
    χ n = (jacobiSym D n : R) := by
  have h := hval n (Nat.isCoprime_iff_coprime.mpr hcop)
  rw [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hn] at h
  simpa using h

/-- At an odd prime `p ∤ N`, a character agreeing on coprime integers with
`fundamentalDiscriminantCharCast R D hD` takes the value `(legendreSym p D : R)`, including `0`
when `p ∣ D` (which cannot occur when `|D| ∣ N` and `p ∤ N`, though the lemma requires no
divisibility between `|D|` and `N`). -/
theorem apply_natCast_prime_eq_legendreSym_of_forall_isCoprime
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have h := hval p
    (Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN))
  rw [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2] at h
  simpa using h

/-- At an odd prime `p ∤ N`, if `fundamentalDiscriminant d = D`, then `χ p = (legendreSym p d : R)`.
-/
theorem apply_natCast_prime_eq_legendreSym_of_fundamentalDiscriminant_eq
    (hdD : fundamentalDiscriminant d = D)
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p d : R) := by
  rw [apply_natCast_prime_eq_legendreSym_of_forall_isCoprime hval hp2 hpN, ← hdD,
    legendreSym_fundamentalDiscriminant d hp2]

/-- **Nonsquare criterion for the discriminant `D` from `χ p = -1`.** When `2 ≠ 0` in `R` and `p`
is an odd prime with `χ p = -1`, `p` is automatically coprime to `N` and `D` is not a square in
`ZMod p`. -/
theorem not_isSquare_of_apply_natCast_prime_eq_neg_one [NeZero (2 : R)]
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    ¬ IsSquare (D : ZMod p) := by
  have : Nontrivial R := ⟨2, 0, NeZero.ne 2⟩
  have h01 : (-1 : R) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hu : IsUnit (p : ZMod N) := by
    by_contra hnu
    exact h01 (hp.symm.trans (χ.map_nonunit hnu))
  have hpN : ¬ p ∣ N :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p N).mp hu)
  have hleg : (legendreSym p D : R) = -1 :=
    (apply_natCast_prime_eq_legendreSym_of_forall_isCoprime hval hp2 hpN).symm.trans hp
  rw [← legendreSym.eq_neg_one_iff]
  rcases jacobiSym.trichotomy D p with h | h | h <;>
    rw [jacobiSym.legendreSym.to_jacobiSym] at hleg
  · rw [h, Int.cast_zero] at hleg
    exact absurd hleg.symm h01
  · rw [h, Int.cast_one, eq_neg_iff_add_eq_zero, one_add_one_eq_two] at hleg
    exact absurd hleg (NeZero.ne (2 : R))
  · rwa [jacobiSym.legendreSym.to_jacobiSym]

/-- **Nonsquare criterion for the radicand `d` from `χ p = -1`.** When `2 ≠ 0` in `R`,
`fundamentalDiscriminant d = D`, and `p` is an odd prime with `χ p = -1`, `d` is not a square in
`ZMod p`. -/
theorem not_isSquare_of_fundamentalDiscriminant_eq_of_apply_natCast_prime_eq_neg_one
    [NeZero (2 : R)] (hdD : fundamentalDiscriminant d = D)
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    ¬ IsSquare (d : ZMod p) := by
  rw [← legendreSym.eq_neg_one_iff, ← legendreSym_fundamentalDiscriminant d hp2, hdD,
    legendreSym.eq_neg_one_iff]
  exact not_isSquare_of_apply_natCast_prime_eq_neg_one hval hp2 hp

end OddPrimeDictionary

end DirichletCharacter

/-! ### Examples and negative controls -/

section Examples

open DirichletCharacter

-- `-12 = 4 * (-3)` with `-3 ≡ 1 (mod 4)` is not a fundamental discriminant, while `1, -4, 8, -8,
-- 5, -3, 12` are.
example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧ Int.IsFundamentalDiscr 8 ∧
    Int.IsFundamentalDiscr (-8) ∧ Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) := by
  have hsf3 : Squarefree (3 : ℤ) :=
    (Int.prime_iff_natAbs_prime (k := 3) |>.mpr Nat.prime_three).squarefree
  have hsfm3 : Squarefree (-3 : ℤ) :=
    (Int.prime_iff_natAbs_prime (k := -3) |>.mpr (by simpa using Nat.prime_three)).squarefree
  have hsf5 : Squarefree (5 : ℤ) :=
    (Int.prime_iff_natAbs_prime (k := 5) |>.mpr Nat.prime_five).squarefree
  refine ⟨Int.isFundamentalDiscr_one,
    isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr,
    isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    by simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf5,
    by simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsfm3,
    by simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf3,
    ?_⟩
  rw [show (-12 : ℤ) = 4 * (-3) by norm_num, Int.isFundamentalDiscr_four_mul]
  omega

-- Running example: at level `12`, `χ₄ · (Legendre mod 3)` is real-valued, has conductor `12`,
-- value `1` at `-1`, primitive discriminant `D = 12` (radicand `d = 3`), values `-1, -1, 1` at
-- `5, 7, 11`, certifies that neither `12` nor `3` is a square modulo `5`, and lifting to level `24`
-- preserves both its conductor and its discriminant.
example :
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) *
        changeLevel (by norm_num : 3 ∣ 12)
          ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))
    (∀ a, (χ a).im = 0) ∧
      χ.conductor = 12 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 12 ∧
      χ (5 : ℕ) = -1 ∧ χ (7 : ℕ) = -1 ∧ χ (11 : ℕ) = 1 ∧
      ¬ IsSquare ((12 : ℤ) : ZMod 5) ∧ ¬ IsSquare ((3 : ℤ) : ZMod 5) ∧
      (changeLevel (by norm_num : 12 ∣ 24) χ).conductor = 12 ∧
      (if changeLevel (by norm_num : 12 ∣ 24) χ (-1) = 1
        then ((changeLevel (by norm_num : 12 ∣ 24) χ).conductor : ℤ)
        else -(changeLevel (by norm_num : 12 ∣ 24) χ).conductor) = 12 := by
  intro _ _ χ
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have hq : χ.IsQuadratic :=
    ((ZMod.isQuadratic_χ₄.comp _).changeLevel _).mul
      (((quadraticChar_isQuadratic _).comp _).changeLevel _)
  have hc : χ.conductor = 12 := by
    rw [conductor_mul_of_coprime] <;>
      simp only [conductor_changeLevel, conductor_χ₄_ringHomComp,
        conductor_changeLevel_quadraticChar hR (by norm_num : 3 ≠ 2)]
    norm_num
  have hneg : χ (-1) = 1 := by
    simp only [χ, MulChar.mul_apply, changeLevel_apply_neg_one, MulChar.ringHomComp_apply,
      eq_intCast]
    have h4 : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
    have h3 : quadraticChar (ZMod 3) (-1 : ZMod 3) = -1 := by
      change legendreSym 3 (-1) = -1
      norm_num
    rw [h4, h3]
    norm_num
  have hD : (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 12 := by
    rw [ite_eq_left hneg, hc]
    rfl
  have h12 : Int.IsFundamentalDiscr 12 := hD ▸ hq.isFundamentalDiscr_conductor_ite
  have hval : ∀ m : ℤ, IsCoprime m 12 →
      χ m = fundamentalDiscriminantCharCast ℂ 12 h12 m := fun m hm ↦ by
    rw [hq.apply_eq_fundamentalDiscriminantCharCast_conductor_ite hm]
    simp only [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast, hD]
  have hχ5 : χ (5 : ℕ) = -1 := by
    rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (by decide) (by decide)]
    norm_num
  have hd3 : fundamentalDiscriminant 3 = 12 := by norm_num [fundamentalDiscriminant_def]
  refine ⟨MulChar.isQuadratic_iff_forall_im_eq_zero.mp hq, hc, hD, hχ5, ?_, ?_,
    not_isSquare_of_apply_natCast_prime_eq_neg_one hval (by decide) hχ5,
    not_isSquare_of_fundamentalDiscriminant_eq_of_apply_natCast_prime_eq_neg_one hd3 hval
      (by decide) hχ5,
    ?_, ?_⟩
  · rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (by decide) (by decide)]
    norm_num
  · rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (by decide) (by decide)]
    norm_num
  · rw [conductor_changeLevel, hc]
  · rw [conductor_ite_changeLevel, hD]

-- Imprimitive example: `χ₄` lifted to level `12` has conductor `4` and `D = -4`, and vanishes at
-- `3` while `χ_{-4}(3) = -1`, showing that coprimality to the level `12` is needed.
example :
    let ψ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    ψ.conductor = 4 ∧
      (if ψ (-1) = 1 then (ψ.conductor : ℤ) else -ψ.conductor) = -4 ∧
      ψ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantCharCast ℂ (-4)
        isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) = -1 := by
  intro ψ
  have hc : ψ.conductor = 4 := by simp [ψ, conductor_changeLevel, conductor_χ₄_ringHomComp]
  have hneg : ψ (-1) ≠ 1 := by
    simp only [ψ, changeLevel_apply_neg_one, MulChar.ringHomComp_apply, eq_intCast]
    have h4 : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
    rw [h4]
    norm_num
  have h3 : ψ (3 : ℤ) = 0 :=
    ψ.map_nonunit (by rw [ZMod.isUnit_intCast_iff_isCoprime]; decide)
  have h3' : fundamentalDiscriminantCharCast ℂ (-4)
      isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) = -1 := by
    rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four]
    have h4 : ZMod.χ₄ ((3 : ℤ) : ZMod 4) = -1 := by decide
    rw [h4]
    norm_num
  refine ⟨hc, ?_, h3, h3'⟩
  rw [ite_eq_right hneg, hc]
  norm_num

-- Degenerate principal example: at level `6`, the principal character has conductor `1` and
-- primitive discriminant `D = 1`.
example :
    let χ : DirichletCharacter ℂ 6 := 1
    χ.conductor = 1 ∧ (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 ∧
      χ (5 : ℤ) = fundamentalDiscriminantCharCast ℂ 1 Int.isFundamentalDiscr_one (5 : ℤ) := by
  have h1 : (1 : DirichletCharacter ℂ 6) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  refine ⟨conductor_one, by rw [ite_eq_left h1, conductor_one, Nat.cast_one], ?_⟩
  rw [MulChar.isQuadratic_one.apply_eq_fundamentalDiscriminantCharCast_conductor_ite
    (N := 6) (n := 5) (by decide)]
  simp only [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast]
  rw [ite_eq_left h1, conductor_one, Nat.cast_one]

-- Sign separation at conductor `8`: `D = 8` and `D = -8` share `|D| = 8` and are separated by the
-- value at `-1`.
example :
    (fundamentalDiscriminantCharCast ℂ 8 isPrimeDiscriminant_eight.isFundamentalDiscr).conductor =
        8 ∧
      (fundamentalDiscriminantCharCast ℂ (-8)
          isPrimeDiscriminant_neg_eight.isFundamentalDiscr).conductor = 8 ∧
      fundamentalDiscriminantCharCast ℂ 8
          isPrimeDiscriminant_eight.isFundamentalDiscr (-1) = 1 ∧
      fundamentalDiscriminantCharCast ℂ (-8)
          isPrimeDiscriminant_neg_eight.isFundamentalDiscr (-1) = -1 := by
  refine ⟨conductor_fundamentalDiscriminantCharCast _,
    conductor_fundamentalDiscriminantCharCast _, ?_, ?_⟩
  · rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_one]
    norm_num
  · rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_one]
    norm_num

-- Odd-prime dictionary and radicands: `D = 12` has radicand `d = 3`, `D = -4` has radicand
-- `d = -1`, and at `p = 2` the character of `D = 5` is `-1` even though `5` is a square modulo `2`
-- (`legendreSym 2 5 = 1`), showing that `p ≠ 2` is indispensable.
example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let h5 : Int.IsFundamentalDiscr 5 := (by
      simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant
        ((Int.prime_iff_natAbs_prime (k := 5) |>.mpr Nat.prime_five).squarefree))
    (if (12 : ℤ) % 4 = 1 then (12 : ℤ) else 12 / 4) = 3 ∧
      (if (-4 : ℤ) % 4 = 1 then (-4 : ℤ) else -4 / 4) = -1 ∧
      legendreSym 5 12 = -1 ∧ legendreSym 5 3 = -1 ∧
      legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0 ∧
      fundamentalDiscriminantChar 5 h5 2 = -1 ∧
      legendreSym 2 5 = 1 ∧ IsSquare ((5 : ℤ) : ZMod 2) := by
  intro _ _ _ h5
  refine ⟨by decide, by decide, by norm_num, by norm_num, by norm_num, by norm_num, ?_,
    by norm_num, ⟨1, by decide⟩⟩
  rw [fundamentalDiscriminantChar_two]
  decide

end Examples
