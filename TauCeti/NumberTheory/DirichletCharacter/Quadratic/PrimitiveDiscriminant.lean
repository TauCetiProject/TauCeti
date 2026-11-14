/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
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
certifies that `D` (hence `d`) is not a square modulo `n`.

## Main results

* `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  primitive fundamental discriminant `D` of a quadratic character `χ` at any nonzero level `N`.
* `DirichletCharacter.eq_conductor_ite_of_forall_isCoprime`,
  `MulChar.IsQuadratic.isFundamentalDiscr_conductor_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_conductor_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_of_eq`: explicit formula
  `if χ (-1) = 1 then χ.conductor else -χ.conductor` for `D`, valid over any commutative ring.
* `DirichletCharacter.conductor_eq_natAbs_of_forall_isCoprime`: in characteristic zero, coprime
  agreement with `fundamentalDiscriminantCharCast R D hD` at a nonzero level `N` forces
  `χ.conductor = |D|`.
* `DirichletCharacter.changeLevel_apply_eq_fundamentalDiscriminantCharCast`,
  `DirichletCharacter.natAbs_eq_conductor_changeLevel_and_forall_isCoprime_iff`,
  `DirichletCharacter.conductor_ite_changeLevel`: naturality of the primitive discriminant under
  `changeLevel`.
* `MulChar.IsQuadratic.existsUnique_squarefree_apply_eq`: unique squarefree-radicand form at any
  nonzero level.
* `DirichletCharacter.apply_natCast_eq_jacobiSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_natCast_eq_legendreSym_of_forall_isCoprime`,
  `DirichletCharacter.not_isSquare_of_apply_natCast_eq_neg_one`: Jacobi/Legendre evaluation at odd
  coprime arguments and the nonsquare criterion from `χ n = -1` at an odd natural number `n`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Cambridge University Press, 2007, §9.3, pp. 295–297 (Theorem 9.13).
-/

public section

open TauCeti.Multiquadratic

namespace DirichletCharacter

/-- Lifting a Dirichlet character to a nonzero multiple of its level preserves the signed
conductor `if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem conductor_ite_changeLevel {S : Type*} [CommMonoidWithZero S]
    {N M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter S N)
    [Decidable (changeLevel hNM χ (-1) = 1)] [Decidable (χ (-1) = 1)] :
    (if changeLevel hNM χ (-1) = 1 then ((changeLevel hNM χ).conductor : ℤ)
      else -((changeLevel hNM χ).conductor : ℤ)) =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) := by
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ hNM))⟩
  rw [conductor_changeLevel]
  exact ite_congr (congrArg (· = 1) (changeLevel_apply_neg_one hNM χ))
    (fun _ ↦ rfl) (fun _ ↦ rfl)

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Existence, uniqueness, and explicit formula -/

/-- Any fundamental discriminant `D` with `|D| = χ.conductor` whose character agrees with `χ` at
every integer prime to the level `N` equals `if χ (-1) = 1 then χ.conductor else -χ.conductor`.
Neither `N ≠ 0` nor `χ.IsQuadratic` is assumed: `D ≠ 0` forces `N ≠ 0`, and agreement on the units
modulo `N` makes `χ` quadratic. -/
theorem eq_conductor_ite_of_forall_isCoprime {N : ℕ}
    {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)] {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (habs : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) := by
  have : NeZero N := ⟨fun h0 ↦ Int.natAbs_ne_zero.mpr hD.ne_zero
    (habs.trans (conductor_eq_zero_iff_level_eq_zero.mpr h0))⟩
  by_cases h2 : (2 : R) = 0
  · have hq : χ.IsQuadratic := fun a ↦ by
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
      by_cases ha : IsUnit (n : ZMod N)
      · rw [hval n (isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime n N).mp ha))]
        exact fundamentalDiscriminantCharCast_isQuadratic hD n
      · exact Or.inl (χ.map_nonunit ha)
    have hχ1 : χ = 1 := hq.eq_one_of_two_eq_zero h2
    have hc1 : χ.conductor = 1 := hχ1 ▸ conductor_one
    have hD1 : D = 1 := hD.natAbs_eq_one_iff.mp (habs.trans hc1)
    have hneg1 : χ (-1) = 1 := by
      rw [hχ1]
      exact MulChar.one_apply isUnit_one.neg
    rw [hD1, ite_eq_left hneg1, hc1, Nat.cast_one]
  · have hsign : χ (-1) = D.sign := by
      simpa [fundamentalDiscriminantChar_neg_one] using hval (-1) isCoprime_one_left.neg_left
    split_ifs with h1 <;> rw [hsign] at h1 <;> rcases hD.ne_zero.lt_or_gt with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero,
        one_add_one_eq_two] at h1
      exact absurd h1 h2
    · omega
    · omega
    · rw [Int.sign_eq_one_of_pos h, Int.cast_one] at h1
      exact absurd rfl h1

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
  have hqp : χ.primitiveCharacter.IsQuadratic :=
    (isQuadratic_changeLevel_iff χ.conductor_dvd_level).mp
      (by rwa [changeLevel_primitiveCharacter])
  obtain ⟨D, hD, habs, hvalp⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_isFundamentalDiscr_apply_eq hqp
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

/-- In characteristic zero, agreement of a Dirichlet character `χ` of nonzero level `N` on the
integers prime to `N` with the character of a fundamental discriminant `D` already forces
`χ.conductor = |D|`. -/
theorem conductor_eq_natAbs_of_forall_isCoprime [CharZero R] {N : ℕ} [NeZero N]
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
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ hNM))⟩
  rw [conductor_changeLevel]
  refine ⟨fun ⟨habs, hvalM⟩ ↦ ⟨habs, fun n hnN ↦ ?_⟩,
    fun ⟨habs, hvalN⟩ ↦ ⟨habs, fun n hnM ↦
      changeLevel_apply_eq_fundamentalDiscriminantCharCast hNM hvalN hnM⟩⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hNM (ZMod.unitOfIsCoprime n hnN)
  set m : ℤ := ((v : ZMod M).val : ℤ)
  have hm_cast : (m : ZMod M) = (v : ZMod M) := by
    simp [m]
  have hmM : IsCoprime m M :=
    isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime m M).mp (hm_cast ▸ v.isUnit))
  have hmN_eq : (m : ZMod N) = (n : ZMod N) := by
    rw [← ZMod.cast_intCast hNM m, hm_cast, ← ZMod.unitsMap_val hNM v, hv,
      ZMod.coe_unitOfIsCoprime]
  have hDN : D.natAbs ∣ N := habs.symm ▸ χ.conductor_dvd_level
  have hmD_eq : (m : ZMod D.natAbs) = (n : ZMod D.natAbs) := by
    simpa only [map_intCast] using congrArg (ZMod.castHom hDN (ZMod D.natAbs)) hmN_eq
  rw [← hmN_eq, ← changeLevel_eq_cast_of_dvd' χ hNM hmM, hvalM m hmM, ← hmD_eq]

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
  have h01 : (0 : R) ≠ -1 := fun h ↦ by
    have h10 : (1 : R) = 0 := neg_eq_zero.mp h.symm
    have h20 : (2 : R) = 0 := by
      rw [← one_add_one_eq_two, h10, add_zero]
    exact two_ne_zero h20
  have hcop : n.Coprime N := by
    by_contra hnc
    have hnu : ¬ IsUnit (n : ZMod N) := mt (ZMod.isUnit_iff_coprime n N).mp hnc
    exact h01 ((χ.map_nonunit hnu).symm.trans hχn)
  have hjac : (jacobiSym D n : R) = -1 := by
    rw [← apply_natCast_eq_jacobiSym_of_forall_isCoprime hval hn hcop, hχn]
  refine ZMod.nonsquare_of_jacobiSym_eq_neg_one ?_
  rcases jacobiSym.trichotomy D n with h | h | h
  · rw [h, Int.cast_zero] at hjac
    exact absurd hjac h01
  · rw [h, Int.cast_one] at hjac
    exact absurd (one_add_one_eq_two.symm.trans (eq_neg_iff_add_eq_zero.mp hjac)) two_ne_zero
  · exact h

end CommRing

/-! ### Concrete checks -/

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

end DirichletCharacter
