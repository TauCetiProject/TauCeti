/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Imprimitive odd quadratic twists

For a character `ψ` modulo eight and a nonzero natural number `d`,
`DirichletCharacter.oddQuadraticTwist ψ d` is the character modulo `8 * d` whose value
at an odd natural number `n` is `(d / n) * ψ(n)` and whose value at an even number is zero.
The index `d` need not be squarefree: primes dividing its square factors still give zero
coefficients. Its continued L-function agrees with the odd Jacobi-symbol series on the
half-plane of absolute convergence.

The construction uses the existing Kronecker character of discriminant `4 * d`, lifted to
level `8 * d`, rather than replacing `d` by a squarefree part.

## References

V. Blomer, *Subconvexity for a double Dirichlet series*, Compositio Math. 147 (2011),
§2.1, (7)–(13), pp. 358–359.
-/

public section

namespace DirichletCharacter

open TauCeti

variable {R : Type*} [CommRing R]

/-- The imprimitive quadratic twist on odd coefficients, at level `8 * d`.
No square factors of `d` are removed. -/
noncomputable def oddQuadraticTwist (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] :
    DirichletCharacter R (8 * d) :=
  changeLevel (by simpa only [Int.natAbs_natCast] using
    (show 4 * d ∣ 8 * d from ⟨2, by omega⟩)) (kroneckerChar R (↑(4 * d))
    (Or.inl (by simp [Int.modEq_zero_iff_dvd])) (by simp [NeZero.ne d])) *
      changeLevel (dvd_mul_right 8 d) ψ

/-- The twist vanishes on even inputs. -/
@[simp] theorem oddQuadraticTwist_natCast_of_even (ψ : DirichletCharacter R 8)
    (d : ℕ) [NeZero d] {n : ℕ} (hn : _root_.Even n) :
    oddQuadraticTwist ψ d n = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro h
  have ho := Nat.coprime_two_right.mp (h.of_dvd_right (by omega : 2 ∣ 8 * d))
  exact (Nat.not_even_iff_odd.mpr ho) hn

/-- The coefficient formula, including the zeros on even inputs and on nonunits of `d`. -/
theorem oddQuadraticTwist_natCast (ψ : DirichletCharacter R 8)
    (d : ℕ) [NeZero d] (n : ℕ) :
    oddQuadraticTwist ψ d n = (jacobiSym (d : ℤ) n : R) * ψ n := by
  by_cases hn : _root_.Odd n
  · by_cases hcop : n.Coprime (8 * d)
    · rw [oddQuadraticTwist, MulChar.mul_apply, changeLevel_natCast_of_coprime _ _ hcop,
        changeLevel_natCast_of_coprime _ _ hcop, kroneckerChar_natCast,
        kroneckerSym_eq_jacobiSym _ hn]
      have h4 : jacobiSym (4 : ℤ) n = 1 := by
        have h2 : (2 : ℤ).gcd n = 1 :=
          (Int.gcd_natCast_natCast 2 n).trans (Nat.coprime_two_left.mpr hn).gcd_eq_one
        simpa using jacobiSym.sq_one' h2
      simp [Nat.cast_mul, jacobiSym.mul_left, h4]
    have hnd : ¬ d.Coprime n := by
      intro h
      apply hcop
      exact (Nat.coprime_two_right.mpr hn).pow_right 3 |>.mul_right h.symm
    have hn0 : n ≠ 0 := by obtain ⟨k, hk⟩ := hn; omega
    have : NeZero n := ⟨hn0⟩
    rw [MulChar.map_nonunit _ (by simpa [ZMod.isUnit_iff_coprime] using hcop),
      jacobiSym.eq_zero_iff_not_coprime.mpr (by
        simpa [Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one] using hnd),
      Int.cast_zero, zero_mul]
  · have hψ : ψ n = 0 := MulChar.map_nonunit _ (by
      rw [ZMod.isUnit_iff_coprime]
      exact fun h ↦ hn (Nat.coprime_two_right.mp
        (h.of_dvd_right (by decide : 2 ∣ 8))))
    simp [oddQuadraticTwist_natCast_of_even ψ d (Nat.not_odd_iff_even.mp hn), hψ]

/-- Over a ring without zero divisors, the quadratic twist takes only the values `0`, `1`,
and `-1`. In particular this applies to every complex character of level eight. -/
theorem oddQuadraticTwist_isQuadratic [NoZeroDivisors R] (ψ : DirichletCharacter R 8)
    (d : ℕ) [NeZero d] : (oddQuadraticTwist ψ d).IsQuadratic := by
  rcases subsingleton_or_nontrivial R with h | h
  · intro a
    exact Or.inl (Subsingleton.elim _ _)
  have hψ : ψ.IsQuadratic := by
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow]
    have hu : (u : ZMod 8) ^ 2 = 1 := by revert u; decide
    rw [hu, map_one, MulChar.one_apply_coe]
  unfold oddQuadraticTwist
  exact (kroneckerChar_isQuadratic _ _).changeLevel _ |>.mul (hψ.changeLevel _)

/-- Twisting by `1` leaves the level-eight character unchanged. -/
@[simp] theorem oddQuadraticTwist_one (ψ : DirichletCharacter R 8) :
    oddQuadraticTwist ψ 1 = ψ := by
  apply MulChar.ext'
  intro a
  rw [← ZMod.natCast_zmod_val a, oddQuadraticTwist_natCast]
  simp [jacobiSym.one_left]

/-- A square factor deletes the coefficients at its prime divisors rather than changing
the other coefficients. The index and the square factor need not be odd. -/
theorem oddQuadraticTwist_mul_sq_natCast (ψ : DirichletCharacter R 8)
    (d k : ℕ) [NeZero d] [NeZero k] (n : ℕ) :
    oddQuadraticTwist ψ (d * k ^ 2) n =
      if k.Coprime n then oddQuadraticTwist ψ d n else 0 := by
  rw [oddQuadraticTwist_natCast, oddQuadraticTwist_natCast]
  rcases eq_zero_or_neZero n with rfl | hn
  · have hψ : ψ (0 : ZMod 8) = 0 := MulChar.map_nonunit ψ (by decide)
    simp [hψ]
  rw [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.pow_left]
  by_cases hk : k.Coprime n
  · have hkn : (k : ℤ).gcd n = 1 :=
      (Int.gcd_natCast_natCast k n).trans hk.gcd_eq_one
    simp [hk, jacobiSym.sq_one hkn]
  · have hkn : (k : ℤ).gcd n ≠ 1 := by
      simpa only [Int.gcd_natCast_natCast, ← Nat.coprime_iff_gcd_eq_one] using hk
    simp [hk, jacobiSym.eq_zero_iff_not_coprime.mpr hkn]

/-- The continued L-function of the imprimitive twist is the odd Jacobi series
on its half-plane of absolute convergence. -/
theorem LFunction_oddQuadraticTwist_eq_LSeries (ψ : DirichletCharacter ℂ 8)
    (d : ℕ) [NeZero d] {s : ℂ} (hs : 1 < s.re) :
    (oddQuadraticTwist ψ d).LFunction s =
      LSeries (fun n ↦ (jacobiSym (d : ℤ) n : ℂ) * ψ n) s := by
  rw [LFunction_eq_LSeries _ hs]
  congr 1
  funext n
  exact oddQuadraticTwist_natCast ψ d n

/-! The square-index test distinguishes an imprimitive twist from its primitive character. -/

example : oddQuadraticTwist (1 : DirichletCharacter ℂ 8) 9 3 = 0 := by
  have h := oddQuadraticTwist_natCast (1 : DirichletCharacter ℂ 8) 9 3
  have h9 : jacobiSym (9 : ℤ) 3 = 0 :=
    jacobiSym.eq_zero_iff_not_coprime.mpr (by decide)
  simpa [h9] using h

example : oddQuadraticTwist (1 : DirichletCharacter ℂ 8) 1 3 = 1 := by
  simp [MulChar.one_apply (by decide : IsUnit (3 : ZMod 8))]

example : oddQuadraticTwist (1 : DirichletCharacter ℂ 8) 9 2 = 0 := by
  exact oddQuadraticTwist_natCast_of_even _ _ (by decide)

example : oddQuadraticTwist (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) 1 3 = -1 := by
  rw [oddQuadraticTwist_one]
  rw [MulChar.ringHomComp_apply, show ZMod.χ₈ (3 : ZMod 8) = -1 by decide]
  norm_num

end DirichletCharacter
