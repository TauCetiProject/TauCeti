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

/-- The twist of `ψ` by the Jacobi symbol `(d / ·)`, at level `8 * d`: it takes odd `n`
to `(d / n) * ψ(n)` and even `n` to zero. It is the product of the lifts of `ψ` and the
Kronecker character of discriminant `4 * d`, with no square factors removed. -/
noncomputable def oddQuadraticTwist (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] :
    DirichletCharacter R (8 * d) :=
  changeLevel (by simpa only [Int.natAbs_natCast] using
    (show 4 * d ∣ 8 * d from ⟨2, by omega⟩)) (kroneckerChar R (↑(4 * d))
    (Or.inl (by simp [Int.modEq_zero_iff_dvd])) (by simp [NeZero.ne d])) *
      changeLevel (dvd_mul_right 8 d) ψ

/-- The twist vanishes on even residue classes. -/
@[simp] theorem oddQuadraticTwist_apply_eq_zero_of_even (ψ : DirichletCharacter R 8)
    (d : ℕ) [NeZero d] {a : ZMod (8 * d)} (ha : _root_.Even a) :
    oddQuadraticTwist ψ d a = 0 :=
  (oddQuadraticTwist ψ d).apply_eq_zero_of_even ((by decide : _root_.Even (8 : ℕ)).mul_right d) ha

/-- The coefficient formula, including the zeros on even inputs and on inputs not coprime to `d`. -/
theorem oddQuadraticTwist_natCast (ψ : DirichletCharacter R 8)
    (d : ℕ) [NeZero d] (n : ℕ) :
    oddQuadraticTwist ψ d n = (jacobiSym (d : ℤ) n : R) * ψ n := by
  by_cases hn : _root_.Odd n
  · by_cases hcop : n.Coprime (8 * d)
    · rw [oddQuadraticTwist, MulChar.mul_apply, changeLevel_natCast_of_coprime _ _ hcop,
        changeLevel_natCast_of_coprime _ _ hcop, kroneckerChar_natCast,
        kroneckerSym_eq_jacobiSym _ hn]
      simp [Nat.cast_mul, jacobiSym.mul_left, jacobiSym.at_four hn]
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
  · have he := Nat.not_odd_iff_even.mp hn
    rw [oddQuadraticTwist_apply_eq_zero_of_even ψ d he.natCast,
      ψ.apply_eq_zero_of_even (by decide) he.natCast, mul_zero]

/-- The twist and the original character have the same value at `-1`. -/
@[simp] theorem oddQuadraticTwist_neg_one (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] :
    oddQuadraticTwist ψ d (-1) = ψ (-1) := by
  have hd : 0 < (↑(4 * d) : ℤ) := by exact_mod_cast Nat.mul_pos (by decide) (NeZero.pos d)
  simp only [oddQuadraticTwist, MulChar.mul_apply, changeLevel_apply_neg_one,
    kroneckerChar_neg_one, Int.sign_eq_one_of_pos hd, Int.cast_one, one_mul]

/-- Twisting preserves and reflects even parity. -/
@[simp] theorem even_oddQuadraticTwist_iff (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] :
    (oddQuadraticTwist ψ d).Even ↔ ψ.Even := by
  rw [Even, Even, oddQuadraticTwist_neg_one]

/-- Twisting preserves and reflects odd parity. -/
@[simp] theorem odd_oddQuadraticTwist_iff (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] :
    (oddQuadraticTwist ψ d).Odd ↔ ψ.Odd := by
  rw [Odd, Odd, oddQuadraticTwist_neg_one]

/-- On integer inputs the Jacobi-symbol factor uses the absolute value of the denominator. -/
theorem oddQuadraticTwist_intCast (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] (a : ℤ) :
    oddQuadraticTwist ψ d a = (jacobiSym (d : ℤ) a.natAbs : R) * ψ a := by
  cases a with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, Int.natAbs_natCast, Int.cast_natCast] using
      oddQuadraticTwist_natCast ψ d n
  | negSucc n =>
    have hneg {N : ℕ} (χ : DirichletCharacter R N) (x : ZMod N) :
        χ (-x) = χ (-1) * χ x := by rw [← map_mul, neg_one_mul]
    rw [Int.natAbs_negSucc, Int.cast_negSucc, Int.cast_negSucc,
      hneg (oddQuadraticTwist ψ d) ↑(n + 1), hneg ψ ↑(n + 1),
      oddQuadraticTwist_neg_one, oddQuadraticTwist_natCast]
    ac_rfl

/-- Applying a ring homomorphism to the coefficients commutes with twisting. -/
@[simp] theorem ringHomComp_oddQuadraticTwist {S : Type*} [CommRing S]
    (ψ : DirichletCharacter R 8) (d : ℕ) [NeZero d] (f : R →+* S) :
    (oddQuadraticTwist ψ d).ringHomComp f = oddQuadraticTwist (ψ.ringHomComp f) d := by
  apply MulChar.ext'
  intro a
  rw [← ZMod.natCast_zmod_val a, MulChar.ringHomComp_apply, oddQuadraticTwist_natCast,
    oddQuadraticTwist_natCast, MulChar.ringHomComp_apply, map_mul, map_intCast]

/-- Twisting a quadratic character yields a quadratic character. -/
theorem _root_.MulChar.IsQuadratic.oddQuadraticTwist {ψ : DirichletCharacter R 8}
    (hψ : ψ.IsQuadratic) (d : ℕ) [NeZero d] : (oddQuadraticTwist ψ d).IsQuadratic := by
  unfold DirichletCharacter.oddQuadraticTwist
  exact (kroneckerChar_isQuadratic _ _).changeLevel _ |>.mul (hψ.changeLevel _)

/-- Over a ring without zero divisors, the twist of any level-eight character is quadratic. -/
theorem isQuadratic_oddQuadraticTwist [NoZeroDivisors R] (ψ : DirichletCharacter R 8)
    (d : ℕ) [NeZero d] : (oddQuadraticTwist ψ d).IsQuadratic :=
  ψ.isQuadratic_of_level_eight.oddQuadraticTwist d

/-- Twisting by `1` leaves the level-eight character unchanged. -/
@[simp] theorem oddQuadraticTwist_one (ψ : DirichletCharacter R 8) :
    oddQuadraticTwist ψ 1 = ψ := by
  apply MulChar.ext'
  intro a
  rw [← ZMod.natCast_zmod_val a, oddQuadraticTwist_natCast]
  simp [jacobiSym.one_left]

/-- Multiplying the twist index by a square raises its level without changing its primitive
character. -/
theorem oddQuadraticTwist_mul_sq (ψ : DirichletCharacter R 8) (d k : ℕ) [NeZero d] [NeZero k] :
    oddQuadraticTwist ψ (d * k ^ 2) =
      changeLevel (mul_dvd_mul_left 8 (dvd_mul_right d (k ^ 2))) (oddQuadraticTwist ψ d) := by
  refine MulChar.ext fun u ↦ ?_
  let n := (u : ZMod (8 * (d * k ^ 2))).val
  have hval : (n : ZMod (8 * (d * k ^ 2))) = u := ZMod.natCast_zmod_val _
  have hn : n.Coprime (8 * (d * k ^ 2)) := (ZMod.isUnit_iff_coprime _ _).mp (hval ▸ u.isUnit)
  have hdiv : k ∣ 8 * (d * k ^ 2) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_pow_self k two_ne_zero) d) 8
  have hk := (hn.of_dvd_right hdiv).symm
  have hg : (k : ℤ).gcd n = 1 := (Int.gcd_natCast_natCast _ _).trans hk.gcd_eq_one
  rw [← hval, changeLevel_natCast_of_coprime _ _ hn, oddQuadraticTwist_natCast,
    oddQuadraticTwist_natCast]
  simp [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.sq_one' hg]

/-- At a square index the twist is just the original character raised to the new level. -/
theorem oddQuadraticTwist_sq (ψ : DirichletCharacter R 8) (k : ℕ) [NeZero k] :
    oddQuadraticTwist ψ (k ^ 2) = changeLevel (dvd_mul_right 8 (k ^ 2)) ψ := by
  have h (m : ℕ) [NeZero m] (hm : 1 * k ^ 2 = m) :
      oddQuadraticTwist ψ m = changeLevel (dvd_mul_right 8 m) ψ := by
    subst m
    simpa only [oddQuadraticTwist_one] using oddQuadraticTwist_mul_sq ψ 1 k
  exact h _ (one_mul _)

/-- Multiplying the twist index by `k ^ 2` zeros the coefficients at inputs not coprime to `k`
and leaves the other coefficients unchanged. -/
theorem oddQuadraticTwist_mul_sq_natCast (ψ : DirichletCharacter R 8)
    (d k : ℕ) [NeZero d] [NeZero k] (n : ℕ) :
    oddQuadraticTwist ψ (d * k ^ 2) n =
      if k.Coprime n then oddQuadraticTwist ψ d n else 0 := by
  rw [oddQuadraticTwist_mul_sq]
  have hcop : n.Coprime (8 * (d * k ^ 2)) ↔ n.Coprime (8 * d) ∧ k.Coprime n := by
    rw [← mul_assoc, Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by decide : 0 < 2)]
    exact and_congr_right fun _ ↦ Nat.coprime_comm
  by_cases hk : k.Coprime n
  · rw [ite_eq_left hk]
    by_cases hd : n.Coprime (8 * d)
    · exact changeLevel_natCast_of_coprime _ _ (hcop.mpr ⟨hd, hk⟩)
    · rw [MulChar.map_nonunit _ (by simpa [ZMod.isUnit_iff_coprime, hcop, hk] using hd),
        MulChar.map_nonunit _ (by simpa [ZMod.isUnit_iff_coprime] using hd)]
  · rw [ite_eq_right hk, MulChar.map_nonunit _ (by simp [ZMod.isUnit_iff_coprime, hcop, hk])]

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
  exact oddQuadraticTwist_apply_eq_zero_of_even _ _ ⟨1, by decide⟩

example : oddQuadraticTwist (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) 1 3 = -1 := by
  rw [oddQuadraticTwist_one]
  rw [MulChar.ringHomComp_apply, show ZMod.χ₈ (3 : ZMod 8) = -1 by decide]
  norm_num

end DirichletCharacter
