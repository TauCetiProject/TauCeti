/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Quadratic
import TauCeti.Data.ZMod.UnitSquare

/-!
# Quadratic Dirichlet characters at a power-of-two level

A quadratic Dirichlet character of level `2 ^ k` is principal, or the lift of `ZMod.χ₄`
(possible for `k ≥ 2`), or the lift of `ZMod.χ₈` or of `ZMod.χ₈'` (possible for `k ≥ 3`).
So there is one quadratic character at levels `1` and `2`, two at level `4` and four at every
level `2 ^ k` with `k ≥ 3`.

The classification holds for characters with values in any commutative ring, with the classical
characters mapped by `Int.castRingHom`. When `2 = 0` in the coefficient ring the four listed
characters coincide; otherwise their conductors are `1`, `4`, `8` and `8`.

## Main results

* `DirichletCharacter.factorsThrough_eight_of_sq_eq_one`: a character of order dividing two at
  level `2 ^ k` with `k ≥ 3` factors through `8`, because the units congruent to `1` modulo `8`
  are squares.
* `DirichletCharacter.eq_one_or_eq_χ₄_of_isQuadratic`,
  `DirichletCharacter.eq_one_or_eq_χ₄_or_eq_χ₈_or_eq_χ₈'_of_isQuadratic`: the quadratic
  characters at levels `4` and `8`.
* `DirichletCharacter.isQuadratic_iff_of_level_two_pow`: the quadratic characters at level
  `2 ^ k`.
* `DirichletCharacter.conductor_eq_one_or_four_or_eight_of_isQuadratic`: a quadratic character
  of level `2 ^ k` has conductor `1`, `4` or `8`.
* `DirichletCharacter.conductor_χ₄_ringHomComp`, `DirichletCharacter.conductor_χ₈_ringHomComp`,
  `DirichletCharacter.conductor_χ₈'_ringHomComp`: the conductors of the classical characters
  when `2 ≠ 0`.
* `DirichletCharacter.changeLevel_ringHomComp_intCast_apply`: the value of a lifted integer
  character at an integer coprime to the level, which with Mathlib's tables
  `ZMod.χ₄_int_eq_if_mod_four`, `ZMod.χ₈_int_eq_if_mod_eight` and `ZMod.χ₈'_int_eq_if_mod_eight`
  gives the values of the lifted characters at odd residues.

## References

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
Cambridge University Press, 2007, §9.3, p. 296.
-/

public section

open ZMod

namespace DirichletCharacter

/-! ### Characters at levels four and eight are determined by few values -/

section Ext

variable {R : Type*} [CommMonoidWithZero R]

/-- Two characters of level four agreeing at `3` are equal. -/
theorem ext_of_level_four {χ ψ : DirichletCharacter R 4} (h3 : χ 3 = ψ 3) : χ = ψ := by
  refine MulChar.ext fun u ↦ ?_
  rcases (by decide : ∀ u : (ZMod 4)ˣ, (u : ZMod 4) = 1 ∨ (u : ZMod 4) = 3) u with h | h <;>
    rw [h]
  · simp
  · exact h3

/-- Two characters of level eight agreeing at `3` and at `5` are equal. -/
theorem ext_of_level_eight {χ ψ : DirichletCharacter R 8} (h3 : χ 3 = ψ 3) (h5 : χ 5 = ψ 5) :
    χ = ψ := by
  refine MulChar.ext fun u ↦ ?_
  rcases (by decide : ∀ u : (ZMod 8)ˣ, (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 3 ∨
    (u : ZMod 8) = 5 ∨ (u : ZMod 8) = 3 * 5) u with h | h | h | h <;> rw [h]
  · simp
  · exact h3
  · exact h5
  · rw [map_mul, map_mul, h3, h5]

end Ext

/-! ### Reduction from level `2 ^ k` to level eight -/

/-- A character of order dividing two at level `2 ^ k`, `k ≥ 3`, factors through `8`: every
unit congruent to `1` modulo `8` is a square. -/
theorem factorsThrough_eight_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {k : ℕ}
    (hk : 3 ≤ k) (χ : DirichletCharacter R (2 ^ k)) (hχ : χ ^ 2 = 1) : χ.FactorsThrough 8 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h8 : 8 ∣ 2 ^ (k + 1) := pow_dvd_pow 2 hk
  refine (factorsThrough_iff_ker_unitsMap h8).mpr fun u hu ↦ ?_
  have hcast : ((u : ZMod (2 ^ (k + 1))).cast : ZMod 8) = 1 := by
    simpa only [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one] using hu
  -- The representative of `u` is `1 + 8 a`, the square of a unit.
  set x := (u : ZMod (2 ^ (k + 1))).val with hx
  have hmod : x % 8 = 1 := by
    have h : (x : ZMod 8) = ((1 : ℕ) : ZMod 8) := by
      rw [hx, ← ZMod.cast_eq_val, hcast, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' x 1 8).mp h
  obtain ⟨q, hq⟩ : ∃ q, x = 8 * q + 1 := ⟨x / 8, by omega⟩
  obtain ⟨y, hy⟩ := exists_unit_sq_eq_one_add_eight_mul (q : ZMod (2 ^ (k + 1)))
  have hu' : (u : ZMod (2 ^ (k + 1))) = (y : ZMod (2 ^ (k + 1))) ^ 2 := by
    rw [hy, ← ZMod.natCast_zmod_val (u : ZMod (2 ^ (k + 1))), ← hx, hq]
    push_cast
    ring
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one, hu', map_pow]
  simpa only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply y.isUnit] using
    congrArg (fun ψ : DirichletCharacter R (2 ^ (k + 1)) ↦ ψ y) hχ

/-! ### The quadratic characters at levels four and eight -/

section Classification

variable {R : Type*} [CommRing R]

/-- A quadratic character takes the value `1` or `-1` at a unit. -/
private theorem apply_eq_one_or_eq_neg_one {n : ℕ} {χ : DirichletCharacter R n}
    (hχ : χ.IsQuadratic) {a : ZMod n} (ha : IsUnit a) : χ a = 1 ∨ χ a = -1 := by
  rcases hχ a with h | h | h
  · have h01 : (0 : R) = 1 := isUnit_zero_iff.mp (h ▸ ha.map χ)
    exact Or.inl (h.trans h01)
  · exact Or.inl h
  · exact Or.inr h

/-- The value of a lifted integer-valued character at an integer coprime to the level. -/
theorem changeLevel_ringHomComp_intCast_apply {d N : ℕ} (h : d ∣ N) (ψ : DirichletCharacter ℤ d)
    {n : ℤ} (hn : IsCoprime n N) :
    changeLevel h (ψ.ringHomComp (Int.castRingHom R)) n = ψ n := by
  rw [changeLevel_eq_cast_of_dvd' _ h hn, MulChar.ringHomComp_apply, eq_intCast]

private theorem χ₄_ringHomComp_three : χ₄.ringHomComp (Int.castRingHom R) 3 = -1 := by
  rw [MulChar.ringHomComp_apply, show χ₄ 3 = -1 by decide]
  simp

private theorem changeLevel_χ₄_ringHomComp_eight_three :
    changeLevel (by norm_num : 4 ∣ 8) (χ₄.ringHomComp (Int.castRingHom R)) 3 = -1 := by
  have := changeLevel_ringHomComp_intCast_apply (R := R) (by norm_num : 4 ∣ 8) χ₄
    (n := 3) (Int.isCoprime_iff_gcd_eq_one.mpr rfl)
  rw [Int.cast_ofNat, Int.cast_ofNat, show χ₄ 3 = -1 by decide] at this
  simpa using this

private theorem changeLevel_χ₄_ringHomComp_eight_five :
    changeLevel (by norm_num : 4 ∣ 8) (χ₄.ringHomComp (Int.castRingHom R)) 5 = 1 := by
  have := changeLevel_ringHomComp_intCast_apply (R := R) (by norm_num : 4 ∣ 8) χ₄
    (n := 5) (Int.isCoprime_iff_gcd_eq_one.mpr rfl)
  rw [Int.cast_ofNat, Int.cast_ofNat, show χ₄ 5 = 1 by decide] at this
  simpa using this

/-- The quadratic characters of level four: the principal character and `χ₄`. -/
theorem eq_one_or_eq_χ₄_of_isQuadratic {χ : DirichletCharacter R 4} (hχ : χ.IsQuadratic) :
    χ = 1 ∨ χ = χ₄.ringHomComp (Int.castRingHom R) := by
  rcases apply_eq_one_or_eq_neg_one hχ (a := 3) (by decide) with h3 | h3
  · exact Or.inl (ext_of_level_four (by rw [h3, MulChar.one_apply (by decide)]))
  · exact Or.inr (ext_of_level_four (by rw [h3, χ₄_ringHomComp_three]))

/-- The quadratic characters of level eight: the principal character, the lift of `χ₄`, `χ₈`
and `χ₈'`. -/
theorem eq_one_or_eq_χ₄_or_eq_χ₈_or_eq_χ₈'_of_isQuadratic {χ : DirichletCharacter R 8}
    (hχ : χ.IsQuadratic) :
    χ = 1 ∨ χ = changeLevel (by norm_num) (χ₄.ringHomComp (Int.castRingHom R)) ∨
      χ = χ₈.ringHomComp (Int.castRingHom R) ∨ χ = χ₈'.ringHomComp (Int.castRingHom R) := by
  have h1 (a : ZMod 8) (ha : IsUnit a) : (1 : DirichletCharacter R 8) a = 1 :=
    MulChar.one_apply ha
  have hv (ψ : DirichletCharacter ℤ 8) (a : ZMod 8) (b : ℤ) (h : ψ a = b) :
      ψ.ringHomComp (Int.castRingHom R) a = b := by
    rw [MulChar.ringHomComp_apply, h, eq_intCast]
  rcases apply_eq_one_or_eq_neg_one hχ (a := 3) (by decide) with h3 | h3 <;>
  rcases apply_eq_one_or_eq_neg_one hχ (a := 5) (by decide) with h5 | h5
  · exact Or.inl (ext_of_level_eight (by rw [h3, h1 _ (by decide)])
      (by rw [h5, h1 _ (by decide)]))
  · refine Or.inr (Or.inr (Or.inr (ext_of_level_eight ?_ ?_)))
    · rw [h3, hv χ₈' 3 1 (by decide), Int.cast_one]
    · rw [h5, hv χ₈' 5 (-1) (by decide), Int.cast_neg, Int.cast_one]
  · refine Or.inr (Or.inl (ext_of_level_eight ?_ ?_))
    · rw [h3, changeLevel_χ₄_ringHomComp_eight_three]
    · rw [h5, changeLevel_χ₄_ringHomComp_eight_five]
  · refine Or.inr (Or.inr (Or.inl (ext_of_level_eight ?_ ?_)))
    · rw [h3, hv χ₈ 3 (-1) (by decide), Int.cast_neg, Int.cast_one]
    · rw [h5, hv χ₈ 5 (-1) (by decide), Int.cast_neg, Int.cast_one]

/-! ### The quadratic characters at level `2 ^ k` -/

/-- **The quadratic characters at a power-of-two level.** A Dirichlet character of level `2 ^ k`
is quadratic exactly when it is principal, or the lift of `χ₄` (possible for `k ≥ 2`), or the
lift of `χ₈` or of `χ₈'` (possible for `k ≥ 3`). -/
theorem isQuadratic_iff_of_level_two_pow {k : ℕ} (χ : DirichletCharacter R (2 ^ k)) :
    χ.IsQuadratic ↔ χ = 1 ∨
      (∃ h : 4 ∣ 2 ^ k, χ = changeLevel h (χ₄.ringHomComp (Int.castRingHom R))) ∨
      (∃ h : 8 ∣ 2 ^ k, χ = changeLevel h (χ₈.ringHomComp (Int.castRingHom R))) ∨
      (∃ h : 8 ∣ 2 ^ k, χ = changeLevel h (χ₈'.ringHomComp (Int.castRingHom R))) := by
  refine ⟨fun hχ ↦ ?_, ?_⟩
  · obtain hk | hk := le_or_gt 3 k
    · obtain ⟨h8, ψ, rfl⟩ := factorsThrough_eight_of_sq_eq_one hk χ hχ.sq_eq_one
      rcases eq_one_or_eq_χ₄_or_eq_χ₈_or_eq_χ₈'_of_isQuadratic
          ((isQuadratic_changeLevel_iff h8).mp hχ) with rfl | rfl | rfl | rfl
      · exact Or.inl (changeLevel_one h8)
      · exact Or.inr (Or.inl ⟨_, (changeLevel_trans _ _ h8).symm⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h8, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h8, rfl⟩))
    · interval_cases k
      · exact Or.inl (level_one χ)
      · refine Or.inl (MulChar.ext fun u ↦ ?_)
        rw [(by decide : ∀ u : (ZMod 2)ˣ, u = 1) u]
        simp
      · rcases eq_one_or_eq_χ₄_of_isQuadratic (χ := χ) hχ with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨dvd_refl 4, h.trans (changeLevel_self _).symm⟩)
  · rintro (rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
    · intro a
      by_cases ha : IsUnit a
      · exact Or.inr (Or.inl (MulChar.one_apply ha))
      · exact Or.inl (MulChar.map_nonunit _ ha)
    · exact (isQuadratic_χ₄.comp _).changeLevel h
    · exact (isQuadratic_χ₈.comp _).changeLevel h
    · exact (isQuadratic_χ₈'.comp _).changeLevel h

/-- A quadratic character of level `2 ^ k` has conductor `1`, `4` or `8`. -/
theorem conductor_eq_one_or_four_or_eight_of_isQuadratic {k : ℕ}
    {χ : DirichletCharacter R (2 ^ k)} (hχ : χ.IsQuadratic) :
    χ.conductor = 1 ∨ χ.conductor = 4 ∨ χ.conductor = 8 := by
  have hquad : χ.primitiveCharacter.IsQuadratic := by
    rw [← isQuadratic_changeLevel_iff χ.conductor_dvd_level, changeLevel_primitiveCharacter]
    exact hχ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp χ.conductor_dvd_level
  have hfac := χ.primitiveCharacter_isPrimitive.factorization_two_eq_zero_or_two_or_three hquad
  rw [hj, Nat.factorization_pow_self Nat.prime_two] at hfac
  rcases hfac with rfl | rfl | rfl <;> simp [hj]

/-! ### Conductors of the classical dyadic characters -/

section Conductor

variable [NeZero (2 : R)]

private theorem one_ne_neg_one : (1 : R) ≠ -1 := fun h ↦
  two_ne_zero (α := R) (by rw [← one_add_one_eq_two, ← add_neg_cancel (1 : R), ← h])

/-- When `2 ≠ 0` in the coefficient ring, `χ₄` is primitive of conductor `4`. -/
theorem conductor_χ₄_ringHomComp : conductor (χ₄.ringHomComp (Int.castRingHom R)) = 4 := by
  refine conductor_eq_four_of_apply_one_ne_apply_three _ ?_
  rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, show χ₄ ((1 : ℤ) : ZMod 4) = 1 by
    decide, show χ₄ ((3 : ℤ) : ZMod 4) = -1 by decide]
  simpa using one_ne_neg_one

/-- When `2 ≠ 0` in the coefficient ring, `χ₈` is primitive of conductor `8`. -/
theorem conductor_χ₈_ringHomComp : conductor (χ₈.ringHomComp (Int.castRingHom R)) = 8 := by
  refine conductor_eq_eight_of_apply_one_ne_apply_five _ ?_
  rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, show χ₈ ((1 : ℤ) : ZMod 8) = 1 by
    decide, show χ₈ ((5 : ℤ) : ZMod 8) = -1 by decide]
  simpa using one_ne_neg_one

/-- When `2 ≠ 0` in the coefficient ring, `χ₈'` is primitive of conductor `8`. -/
theorem conductor_χ₈'_ringHomComp : conductor (χ₈'.ringHomComp (Int.castRingHom R)) = 8 := by
  refine conductor_eq_eight_of_apply_one_ne_apply_five _ ?_
  rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, show χ₈' ((1 : ℤ) : ZMod 8) = 1 by
    decide, show χ₈' ((5 : ℤ) : ZMod 8) = -1 by decide]
  simpa using one_ne_neg_one

end Conductor

end Classification

end DirichletCharacter
