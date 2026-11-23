/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# The primitive discriminant of a quadratic Dirichlet character

Every quadratic Dirichlet character `χ` at an arbitrary nonzero level `N` over a commutative ring
`R` has a unique **primitive discriminant**: a fundamental discriminant `D` with
`|D| = χ.conductor` whose character `fundamentalDiscriminantCharCast R D hD` agrees with `χ` at
every integer coprime to `N`. Explicitly, `D` is `χ.conductor` when `χ (-1) = 1` and
`-χ.conductor` otherwise, including in rings where `2 = 0` (where every quadratic character is
principal, `χ.conductor = 1`, and `D = 1`). The principal character at any nonzero level corresponds
to `D = 1`.

Passing along `fundamentalDiscriminant` gives the companion squarefree-radicand parameterization:
there is a unique squarefree integer `d` with `|fundamentalDiscriminant d| = χ.conductor` whose
associated character agrees with `χ` on integers coprime to `N`. Both descriptions are invariant
under lifting `χ` to a nonzero multiple of `N` via `DirichletCharacter.changeLevel`.

At an odd natural number `n` coprime to `N`, `χ n` is the Jacobi symbol `jacobiSym D n` (and
`jacobiSym d n`); at an odd prime `p ∤ N`, `χ p` is `legendreSym p D = legendreSym p d`. Over a
ring with `2 ≠ 0`, a value `χ n = -1` at an odd natural number `n` forces `n.Coprime N` and
certifies that `D` (hence `d`) is not a square modulo `n`; at an odd prime `p ∤ N` the converse
holds as well.

## Main results

* `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  primitive fundamental discriminant `D` of a quadratic character `χ` at any nonzero level `N`.
* `MulChar.IsQuadratic.isFundamentalDiscr_conductor_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_conductor_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_of_eq`: explicit formula
  `if χ (-1) = 1 then χ.conductor else -χ.conductor` for `D`, valid over any commutative ring.
* `DirichletCharacter.conductor_eq_natAbs_of_forall_isCoprime`: whenever `2 ≠ 0` in the
  coefficient ring, coprime agreement with `fundamentalDiscriminantCharCast R D hD` at a nonzero
  level `N` forces `χ.conductor = |D|`.
* `DirichletCharacter.changeLevel_apply_eq_fundamentalDiscriminantCharCast`,
  `DirichletCharacter.natAbs_eq_conductor_changeLevel_and_forall_isCoprime_iff`: naturality of the
  primitive discriminant under `changeLevel`.
* `MulChar.IsQuadratic.existsUnique_squarefree_apply_eq`: unique squarefree-radicand form at any
  nonzero level.
* `DirichletCharacter.apply_natCast_eq_jacobiSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_natCast_eq_legendreSym_of_forall_isCoprime`,
  `DirichletCharacter.not_isSquare_of_apply_natCast_eq_neg_one`: Jacobi/Legendre evaluation at odd
  coprime arguments and the nonsquare criterion from `χ n = -1` at an odd natural number `n`.
* `MulChar.IsQuadratic.apply_natCast_eq_legendreSym_conductor_ite`,
  `DirichletCharacter.apply_natCast_eq_neg_one_iff_not_isSquare`: at an odd prime `p ∤ N`, `χ p` is
  the Legendre symbol of the signed conductor, and `χ p = -1` exactly when `D` is not a square
  modulo `p`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Cambridge University Press, 2007, §9.3, pp. 295–297 (Theorem 9.13).
-/

public section

open TauCeti.Multiquadratic

namespace DirichletCharacter

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Existence, uniqueness, and explicit formula -/

/-- **The primitive discriminant of a quadratic Dirichlet character.** Every quadratic Dirichlet
character `χ` of nonzero level `N` over a commutative ring `R` agrees at the integers prime to `N`
with the character of a unique fundamental discriminant `D` of absolute value `χ.conductor`
(Montgomery–Vaughan, Theorem 9.13). The principal character corresponds to `D = 1`. -/
theorem _root_.MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      D.natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, habs, hvalp⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_isFundamentalDiscr_apply_eq hχ.primitiveCharacter
  have hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n :=
    fun n hn ↦ (primitiveCharacter_apply_of_isCoprime χ hn).symm.trans (hvalp n)
  refine ⟨D, ⟨hD, habs, hval⟩, ?_⟩
  rintro D' ⟨hD', habs', hval'⟩
  exact (eq_conductor_ite_of_forall_isCoprime habs' hval').trans
    (eq_conductor_ite_of_forall_isCoprime habs hval).symm

/-- For every quadratic Dirichlet character `χ` of nonzero level `N`, the signed conductor
`if χ (-1) = 1 then χ.conductor else -χ.conductor` is a fundamental discriminant. -/
theorem _root_.MulChar.IsQuadratic.isFundamentalDiscr_conductor_ite
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)]
    (hχ : χ.IsQuadratic) :
    Int.IsFundamentalDiscr
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) := by
  obtain ⟨D, ⟨hD, habs, hval⟩, -⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  rwa [← eq_conductor_ite_of_forall_isCoprime habs hval]

/-- **Evaluation of a quadratic character via its signed conductor.** At every integer `n` prime to
`N`, a quadratic Dirichlet character `χ` of nonzero level `N` agrees with the character of the
fundamental discriminant `if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_conductor_ite
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)]
    (hχ : χ.IsQuadratic) {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ hχ.isFundamentalDiscr_conductor_ite n := by
  obtain ⟨D, ⟨hD, habs, hval⟩, -⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  have hD_eq := eq_conductor_ite_of_forall_isCoprime habs hval
  subst hD_eq
  exact hval n hn

/-- When the signed conductor of a quadratic character `χ` equals `D`, `χ` agrees on integers
prime to `N` with `fundamentalDiscriminantCharCast R D hD` for any proof `hD` that `D` is a
fundamental discriminant. `N ≠ 0` follows automatically because `D ≠ 0`. -/
theorem _root_.MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_of_eq
    {N : ℕ} {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)]
    (hχ : χ.IsQuadratic) {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hD_eq : (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = D)
    {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R D hD n := by
  have : NeZero N := ⟨fun h0 ↦ hD.ne_zero <| by
    rw [← hD_eq, conductor_eq_zero_iff_level_eq_zero.mpr h0, Nat.cast_zero, neg_zero, ite_self]⟩
  subst hD_eq
  exact hχ.apply_eq_fundamentalDiscriminantCharCast_conductor_ite hn

/-- Whenever `2 ≠ 0` in the coefficient ring, agreement of a Dirichlet character `χ` of nonzero
level `N` on the integers prime to `N` with the character of a fundamental discriminant `D`
already forces `χ.conductor = |D|`. -/
theorem conductor_eq_natAbs_of_forall_isCoprime [NeZero (2 : R)] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    χ.conductor = D.natAbs := by
  have : NeZero D.natAbs := hD.neZero_natAbs
  have : NeZero (N * D.natAbs) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne D.natAbs)⟩
  have hEq : changeLevel (dvd_mul_right N D.natAbs) χ =
      changeLevel (dvd_mul_left D.natAbs N) (fundamentalDiscriminantCharCast R D hD) := by
    refine MulChar.ext' fun x ↦ ?_
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    refine apply_intCast_eq_of_forall_isCoprime rfl (fun m hm ↦ ?_) n
    have hmN : IsCoprime m N :=
      hm.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (dvd_mul_right N D.natAbs))
    rw [changeLevel_eq_cast_of_dvd' _ _ hm, changeLevel_eq_cast_of_dvd' _ _ hm, hval m hmN]
  have hc := congrArg conductor hEq
  rwa [conductor_changeLevel, conductor_changeLevel,
    conductor_fundamentalDiscriminantCharCast] at hc

/-! ### Naturality under level change -/

/-- Lifting a Dirichlet character `χ` along `N ∣ M` preserves agreement on coprime integers with
the character of a fundamental discriminant. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast {N M : ℕ} (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn]
  exact hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))

/-- **Naturality of the primitive discriminant under `changeLevel`.** At a nonzero multiple level
`M` of `N`, `changeLevel hNM χ` has conductor `|D|` and agrees on integers prime to `M` with the
character of `D` if and only if `χ` has conductor `|D|` and agrees on integers prime to `N` with
the character of `D`. -/
theorem natAbs_eq_conductor_changeLevel_and_forall_isCoprime_iff {N M : ℕ} [NeZero M]
    (hNM : N ∣ M) (χ : DirichletCharacter R N) {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    (D.natAbs = (changeLevel hNM χ).conductor ∧
      ∀ n : ℤ, IsCoprime n M →
        changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n) ↔
      D.natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [conductor_changeLevel]
  refine ⟨fun ⟨habs, hvalM⟩ ↦ ⟨habs, ?_⟩,
    fun ⟨habs, hvalN⟩ ↦ ⟨habs, fun n hnM ↦
      changeLevel_apply_eq_fundamentalDiscriminantCharCast hNM hvalN hnM⟩⟩
  have hDN : D.natAbs ∣ N := habs.symm ▸ χ.conductor_dvd_level
  have hχ : χ = changeLevel hDN (fundamentalDiscriminantCharCast R D hD) := by
    apply changeLevel_injective hNM
    rw [← changeLevel_trans]
    refine MulChar.ext' fun x ↦ ?_
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact apply_intCast_eq_of_forall_isCoprime rfl (fun k hk ↦ by
      rw [hvalM k hk, changeLevel_eq_cast_of_dvd' _ _ hk]) m
  exact fun n hnN ↦ by rw [hχ, changeLevel_eq_cast_of_dvd' _ hDN hnN]

/-! ### Squarefree radicand parameterization and odd-prime dictionary -/

/-- **Radicand form of the primitive discriminant at any level.** Every quadratic Dirichlet
character `χ` of nonzero level `N` over a commutative ring `R` agrees at the integers prime to `N`
with the character of `fundamentalDiscriminant d` for a unique squarefree integer `d` satisfying
`|fundamentalDiscriminant d| = χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.existsUnique_squarefree_apply_eq
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d,
      (fundamentalDiscriminant d).natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N →
          χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
            (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, habs, hval⟩, huniq⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  obtain ⟨d, ⟨hd, hdD⟩, -⟩ := hD.existsUnique_squarefree_fundamentalDiscriminant_eq
  subst hdD
  refine ⟨d, ⟨hd, habs, hval⟩, ?_⟩
  rintro d' ⟨hd', habs', hval'⟩
  exact fundamentalDiscriminant_injective
    (huniq (fundamentalDiscriminant d') ⟨isFundamentalDiscr_fundamentalDiscriminant hd',
      habs', hval'⟩)

/-- At an odd natural number `n` coprime to `N`, a character agreeing on integers prime to `N` with
`fundamentalDiscriminantCharCast R D hD` evaluates to `jacobiSym D n`. -/
theorem apply_natCast_eq_jacobiSym_of_forall_isCoprime {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {n : ℕ} (hn : _root_.Odd n) (hcop : n.Coprime N) :
    χ n = jacobiSym D n := by
  calc χ n = χ (n : ℤ) := by rw [Int.cast_natCast]
    _ = fundamentalDiscriminantCharCast R D hD (n : ℤ) :=
      hval n (Nat.isCoprime_iff_coprime.mpr hcop)
    _ = jacobiSym D n := by
      rw [fundamentalDiscriminantCharCast_apply,
        fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hn]

/-- At an odd prime `p ∤ N`, a character agreeing on integers prime to `N` with
`fundamentalDiscriminantCharCast R D hD` evaluates to `legendreSym p D`. -/
theorem apply_natCast_eq_legendreSym_of_forall_isCoprime {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = legendreSym p D := by
  have hp : p.Prime := Fact.out
  rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (hp.odd_of_ne_two hp2)
    (hp.coprime_iff_not_dvd.mpr hpN), jacobiSym.legendreSym.to_jacobiSym]

/-- At an odd prime `p ∤ N`, a quadratic Dirichlet character `χ` of nonzero level `N` evaluates to
the cast of the Legendre symbol modulo `p` of its primitive discriminant, the signed conductor
`if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.apply_natCast_eq_legendreSym_conductor_ite
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)]
    (hχ : χ.IsQuadratic) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = legendreSym p (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) :=
  apply_natCast_eq_legendreSym_of_forall_isCoprime (hD := hχ.isFundamentalDiscr_conductor_ite)
    (fun _ hn ↦ hχ.apply_eq_fundamentalDiscriminantCharCast_conductor_ite hn) hp2 hpN

/-- **Nonsquare dictionary at odd primes.** Over a ring with `2 ≠ 0`, if `χ` agrees on the
integers prime to `N` with the character of a fundamental discriminant `D`, then at an odd prime
`p ∤ N`, `χ p = -1` holds if and only if `D` is not a square modulo `p`. -/
theorem apply_natCast_eq_neg_one_iff_not_isSquare [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = -1 ↔ ¬ IsSquare (D : ZMod p) := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  have h := hval p hcop
  rw [Int.cast_natCast, Int.cast_natCast] at h
  rw [h, fundamentalDiscriminantCharCast_natCast_eq_neg_one_iff hD hp2]

/-- **Nonsquare criterion from a character value `-1` at an odd natural number.** Over a ring with
`2 ≠ 0`, if `χ` agrees on the integers prime to `N` with the character of a fundamental
discriminant `D`, and `χ n = -1` at an odd natural number `n`, then `D` is not a square modulo `n`.
Coprimality `n.Coprime N` follows automatically because failure of coprimality would make
`χ n = 0 ≠ -1`. -/
theorem not_isSquare_of_apply_natCast_eq_neg_one [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m)
    {n : ℕ} (hn : _root_.Odd n) (hχn : χ n = -1) :
    ¬ IsSquare (D : ZMod n) := by
  have : Nontrivial R := nontrivial_of_ne 2 0 two_ne_zero
  have hR : ringChar R ≠ 2 := fun h ↦
    two_ne_zero (Nat.cast_two (R := R) ▸ (ringChar.spec R 2).mpr h.dvd)
  have hcop : n.Coprime N := Nat.isCoprime_iff_coprime.mp <|
    (χ.apply_ne_zero_iff n).mp (by rw [Int.cast_natCast, hχn]; exact neg_ne_zero.mpr one_ne_zero)
  have hjac : (jacobiSym D n : R) = ((-1 : ℤ) : R) := by
    rw [← apply_natCast_eq_jacobiSym_of_forall_isCoprime hval hn hcop, hχn, Int.cast_neg,
      Int.cast_one]
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one
    (Int.cast_injOn_of_ringChar_ne_two hR (jacobiSym.trichotomy D n) (Or.inr (Or.inr rfl)) hjac)

end CommRing

/-! ### Concrete checks -/

-- Fundamental discriminants `1, -4, 8, -8, 5, -3, 12`, and `-12` as a non-fundamental
-- discriminant (`-12 = 4 · (-3)` with `-3 ≡ 1 (mod 4)`).
example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧ Int.IsFundamentalDiscr 8 ∧
    Int.IsFundamentalDiscr (-8) ∧ Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) := by
  have h5 : Int.IsFundamentalDiscr 5 :=
    Int.isFundamentalDiscr_iff_squarefree.mpr
      (Or.inl ⟨by norm_num, Int.squarefree_natAbs.mp Nat.prime_five.squarefree⟩)
  have h3 : Int.IsFundamentalDiscr (-3) :=
    Int.isFundamentalDiscr_iff_squarefree.mpr
      (Or.inl ⟨by norm_num, Int.squarefree_natAbs.mp Nat.prime_three.squarefree⟩)
  have h12 : Int.IsFundamentalDiscr 12 :=
    (Int.isFundamentalDiscr_four_mul (m := 3)).mpr
      ⟨Int.squarefree_natAbs.mp Nat.prime_three.squarefree, by norm_num⟩
  have hneg12 : ¬ Int.IsFundamentalDiscr (-12) := fun h ↦ by
    have := ((Int.isFundamentalDiscr_iff_squarefree.mp h).resolve_left (by omega)).right.right
    omega
  exact ⟨Int.isFundamentalDiscr_one, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr, isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    h5, h3, h12, hneg12⟩

-- At conductor `8`, `χ₈` and `χ₈'` have the same `|D| = 8` and are distinguished by their values
-- at `-1`, yielding `D = 8` and `D = -8`.
example :
    let ψ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
    let ψ' : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)
    (if ψ (-1) = 1 then (ψ.conductor : ℤ) else -(ψ.conductor : ℤ)) = 8 ∧
      (if ψ' (-1) = 1 then (ψ'.conductor : ℤ) else -(ψ'.conductor : ℤ)) = -8 := by
  intro ψ ψ'
  have h8 : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide
  have h8' : ZMod.χ₈' (-1 : ZMod 8) = -1 := by decide
  have h1 : ψ (-1) = 1 := by simp [ψ, h8]
  have h2 : ψ' (-1) = -1 := by simp [ψ', h8']
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  simp [ψ, ψ', conductor_χ₈_ringHomComp, conductor_χ₈'_ringHomComp, h1, h2, hne]

-- The principal character at level `6` has conductor `1`, primitive discriminant `D = 1`,
-- and squarefree radicand `d = 1`.
example :
    let χ : DirichletCharacter ℂ 6 := 1
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 1 ∧
      ∃! d : ℤ, ∃ hd : Squarefree d,
        (fundamentalDiscriminant d).natAbs = χ.conductor ∧
          ∀ n : ℤ, IsCoprime n 6 →
            χ n = fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)
              (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  refine ⟨?_, MulChar.isQuadratic_one.existsUnique_squarefree_apply_eq⟩
  have h1 : (1 : DirichletCharacter ℂ 6) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  rw [ite_eq_left h1, conductor_one, Nat.cast_one]

-- Lifting `χ₄` to level `12` gives primitive discriminant `D = -4`; agreement holds at integers
-- prime to `12`, while at `3` the lifted character vanishes whereas `χ_{-4}(3) = -1`.
example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by decide : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = -4 ∧
      χ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantCharCast ℂ (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr
        (3 : ℤ) = -1 := by
  intro χ
  have hneg : χ (-1) = -1 := by
    rw [changeLevel_apply_neg_one,
      MulChar.ringHomComp_intCast_apply_of_apply_eq ZMod.χ₄ (a := -1) (b := -1) (by decide)]
    norm_num
  have h3 : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  refine ⟨?_, χ.map_nonunit (by decide), ?_⟩
  · rw [ite_eq_right (by rw [hneg]; norm_num), conductor_changeLevel, conductor_χ₄_ringHomComp]
    norm_num
  · rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four]
    exact_mod_cast h3

-- The conductor-`12` character `χ₄ · (Legendre mod 3)` has primitive discriminant `D = 12`
-- (squarefree radicand `d = 3`), retains conductor `12` and discriminant `12` when lifted to
-- level `24`, takes values `-1, -1, 1` at `5, 7, 11`, and certifies `3` nonsquare modulo `5`.
example [Fact (Nat.Prime 3)] :
    let χ₄c : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
    let χ₃c : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by decide : 4 ∣ 12) χ₄c * changeLevel (by decide : 3 ∣ 12) χ₃c
    let χ₂₄ : DirichletCharacter ℂ 24 := changeLevel (by decide : 12 ∣ 24) χ
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 12 ∧
      (if χ₂₄ (-1) = 1 then (χ₂₄.conductor : ℤ) else -(χ₂₄.conductor : ℤ)) = 12 := by
  intro χ₄c χ₃c χ χ₂₄
  have h312 : 3 ∣ 12 := by decide
  have hR : ringChar ℂ ≠ 2 := by rw [ringChar.eq_zero]; decide
  have hcond3 : (changeLevel h312 χ₃c).conductor = 3 :=
    conductor_changeLevel_quadraticChar (R := ℂ) (p := 3) hR (by decide) h312
  have hcop : (changeLevel (by decide : 4 ∣ 12) χ₄c).conductor.Coprime
      (changeLevel h312 χ₃c).conductor := by
    rw [hcond3, conductor_changeLevel, conductor_χ₄_ringHomComp]
    decide
  have hq3 : quadraticChar (ZMod 3) (-1) = -1 := by
    rw [quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; decide), ZMod.card]
    decide
  have hneg : χ (-1) = 1 := by
    rw [MulChar.mul_apply, changeLevel_apply_neg_one, changeLevel_apply_neg_one,
      MulChar.ringHomComp_intCast_apply_of_apply_eq ZMod.χ₄ (a := -1) (b := -1) (by decide),
      MulChar.ringHomComp_intCast_apply_of_apply_eq (quadraticChar (ZMod 3)) hq3]
    norm_num
  have hite : (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 12 := by
    rw [ite_eq_left hneg, conductor_mul_of_coprime hcop, hcond3, conductor_changeLevel,
      conductor_χ₄_ringHomComp]
    norm_num
  exact ⟨hite, (conductor_ite_changeLevel (by decide : 12 ∣ 24) χ).trans hite⟩

example {χ : DirichletCharacter ℂ 12} (hq : χ.IsQuadratic)
    (hite : (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 12) :
    χ (5 : ℤ) = -1 ∧ χ (7 : ℤ) = -1 ∧ χ (11 : ℤ) = 1 ∧ ¬ IsSquare ((3 : ℤ) : ZMod 5) := by
  have h12 : Int.IsFundamentalDiscr 12 := by
    have h43 : (12 : ℤ) = 4 * 3 := by norm_num
    rw [h43, Int.isFundamentalDiscr_four_mul]
    exact ⟨(Int.squarefree_natAbs (n := 3)).mp Nat.prime_three.squarefree, by omega⟩
  have hval := fun n (hn : IsCoprime n 12) ↦
    hq.apply_eq_fundamentalDiscriminantCharCast_of_eq h12 hite hn
  have h5 : χ (5 : ℤ) = -1 := by
    have h := apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (n := 5) (by decide) (by decide)
    norm_num at h ⊢
    exact h
  have h7 : χ (7 : ℤ) = -1 := by
    have h := apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (n := 7) (by decide) (by decide)
    norm_num at h ⊢
    exact h
  have h11 : χ (11 : ℤ) = 1 := by
    have h := apply_natCast_eq_jacobiSym_of_forall_isCoprime hval (n := 11) (by decide) (by decide)
    norm_num at h ⊢
    exact h
  have hnsq12 : ¬ IsSquare ((12 : ℤ) : ZMod 5) :=
    not_isSquare_of_apply_natCast_eq_neg_one hval (n := 5) (by decide) (by simpa using h5)
  have hf3 : fundamentalDiscriminant 3 = 12 := by
    rw [fundamentalDiscriminant_of_mod_four_ne_one (by omega)]
    norm_num
  refine ⟨h5, h7, h11, ?_⟩
  rwa [← isSquare_fundamentalDiscriminant_zmod_iff 3 (n := 5) (by decide), hf3]

-- Exclusion of `p = 2`: `χ_5(2) = -1`, while `legendreSym 2 5 = 1` and `5` is a square modulo `2`.
example [Fact (Nat.Prime 2)] :
    have h5 : Int.IsFundamentalDiscr 5 :=
      Int.isFundamentalDiscr_iff_squarefree.mpr
        (Or.inl ⟨by omega, (Int.squarefree_natAbs (n := 5)).mp Nat.prime_five.squarefree⟩)
    fundamentalDiscriminantChar 5 h5 2 = -1 ∧
      legendreSym 2 5 = 1 ∧
      IsSquare ((5 : ℤ) : ZMod 2) := by
  refine ⟨?_, by norm_num, ⟨1, rfl⟩⟩
  rw [fundamentalDiscriminantChar_two]
  decide

-- Odd-prime dictionary: `D = 12` has squarefree radicand `d = 3`; at `p = 5` both Legendre
-- symbols are `-1`, through `12 = 2² · 3`; at `p = 3`, which divides `D`, both are `0`.
-- `D = -4` has squarefree radicand `d = -1`.
example [Fact (Nat.Prime 5)] :
    Squarefree (3 : ℤ) ∧ fundamentalDiscriminant 3 = 12 ∧
      legendreSym 5 12 = legendreSym 5 2 ∧ legendreSym 5 2 = -1 ∧ legendreSym 5 3 = -1 ∧
      legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0 ∧
      Squarefree (-1 : ℤ) ∧ fundamentalDiscriminant (-1) = -4 := by
  refine ⟨Int.prime_three.squarefree, ?_, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, isUnit_neg_one.squarefree, ?_⟩ <;>
  rw [fundamentalDiscriminant_of_mod_four_ne_one (by decide)] <;> norm_num

end DirichletCharacter
