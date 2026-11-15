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

/-!
# Quadratic Dirichlet characters at a power-of-two level

A quadratic Dirichlet character of level `2 ^ k` is principal, or the lift of `ZMod.χ₄`
(possible for `k ≥ 2`), or the lift of `ZMod.χ₈` or of `ZMod.χ₈'` (possible for `k ≥ 3`).
The classification holds for characters with values in any commutative ring, with the classical
characters mapped by `Int.castRingHom`. When `2 ≠ 0` in the coefficient ring the four listed
characters have conductors `1`, `4`, `8` and `8` and are distinct, so there is one quadratic
character at levels `1` and `2`, two at level `4` and four at every level `2 ^ k` with `k ≥ 3`.
When `2 = 0` the four listed characters coincide, and the principal character is the only
quadratic character at every level `2 ^ k`.

The reduction to level eight, `DirichletCharacter.factorsThrough_eight_of_sq_eq_one`, and the
conductor bound hold more generally for characters of order dividing two with values in any
commutative monoid with zero.

## Main results

* `DirichletCharacter.eq_one_or_eq_χ₄_of_isQuadratic`,
  `DirichletCharacter.eq_one_or_eq_χ₄_or_eq_χ₈_or_eq_χ₈'_of_isQuadratic`: the quadratic
  characters at levels `4` and `8`.
* `DirichletCharacter.isQuadratic_iff_of_level_two_pow`: the quadratic characters at level
  `2 ^ k`.
* `DirichletCharacter.conductor_eq_one_or_four_or_eight_of_sq_eq_one`,
  `DirichletCharacter.conductor_eq_one_or_four_or_eight_of_isQuadratic`: a character of order
  dividing two, in particular a quadratic character, of level `2 ^ k` has conductor `1`, `4`
  or `8`.
* `DirichletCharacter.conductor_χ₄_ringHomComp`, `DirichletCharacter.conductor_χ₈_ringHomComp`,
  `DirichletCharacter.conductor_χ₈'_ringHomComp`: the conductors of the classical characters
  when `2 ≠ 0`.

The values of the lifted characters at odd residues follow from
`DirichletCharacter.changeLevel_ringHomComp_intCast_apply` and Mathlib's tables
`ZMod.χ₄_int_eq_if_mod_four`, `ZMod.χ₈_int_eq_if_mod_eight` and `ZMod.χ₈'_int_eq_if_mod_eight`.

## References

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
Cambridge University Press, 2007, §9.3, p. 296.
-/

public section

open ZMod

namespace DirichletCharacter

/-- A character of order dividing two at level `2 ^ k` has conductor `1`, `4` or `8`. -/
theorem conductor_eq_one_or_four_or_eight_of_sq_eq_one {R : Type*} [CommMonoidWithZero R]
    {k : ℕ} {χ : DirichletCharacter R (2 ^ k)} (hχ : χ ^ 2 = 1) :
    χ.conductor = 1 ∨ χ.conductor = 4 ∨ χ.conductor = 8 := by
  have hsq : χ.primitiveCharacter ^ 2 = 1 := by
    apply changeLevel_injective χ.conductor_dvd_level
    rw [map_pow, changeLevel_primitiveCharacter, map_one, hχ]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp χ.conductor_dvd_level
  have hfac :=
    χ.primitiveCharacter_isPrimitive.factorization_two_eq_zero_or_two_or_three_of_sq_eq_one hsq
  rw [hj, Nat.factorization_pow_self Nat.prime_two] at hfac
  rcases hfac with rfl | rfl | rfl <;> simp [hj]

/-! ### The quadratic characters at levels four and eight -/

section Classification

variable {R : Type*} [CommRing R]

/-- The quadratic characters of level four: the principal character and `χ₄`. -/
theorem eq_one_or_eq_χ₄_of_isQuadratic {χ : DirichletCharacter R 4} (hχ : χ.IsQuadratic) :
    χ = 1 ∨ χ = χ₄.ringHomComp (Int.castRingHom R) := by
  rcases hχ.apply_eq_one_or_eq_neg_one (a := 3) (by decide) with h3 | h3
  · exact Or.inl (ext_of_level_four (by rw [h3, MulChar.one_apply (by decide)]))
  · refine Or.inr (ext_of_level_four ?_)
    rw [h3, MulChar.ringHomComp_intCast_apply_of_apply_eq χ₄ (a := 3) (b := -1) (by decide),
      Int.cast_neg, Int.cast_one]

/-- The quadratic characters of level eight: the principal character, the lift of `χ₄`, `χ₈`
and `χ₈'`. -/
theorem eq_one_or_eq_χ₄_or_eq_χ₈_or_eq_χ₈'_of_isQuadratic {χ : DirichletCharacter R 8}
    (hχ : χ.IsQuadratic) :
    χ = 1 ∨ χ = changeLevel (by norm_num) (χ₄.ringHomComp (Int.castRingHom R)) ∨
      χ = χ₈.ringHomComp (Int.castRingHom R) ∨ χ = χ₈'.ringHomComp (Int.castRingHom R) := by
  have h1 (a : ZMod 8) (ha : IsUnit a) : (1 : DirichletCharacter R 8) a = 1 :=
    MulChar.one_apply ha
  rcases hχ.apply_eq_one_or_eq_neg_one (a := 3) (by decide) with h3 | h3 <;>
  rcases hχ.apply_eq_one_or_eq_neg_one (a := 5) (by decide) with h5 | h5
  · exact Or.inl (ext_of_level_eight (by rw [h3, h1 _ (by decide)])
      (by rw [h5, h1 _ (by decide)]))
  · refine Or.inr (Or.inr (Or.inr (ext_of_level_eight ?_ ?_)))
    · rw [h3, MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈' (a := 3) (b := 1) (by decide),
        Int.cast_one]
    · rw [h5, MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈' (a := 5) (b := -1) (by decide),
        Int.cast_neg, Int.cast_one]
  · refine Or.inr (Or.inl (ext_of_level_eight ?_ ?_))
    · rw [h3, show (3 : ZMod 8) = ((3 : ℤ) : ZMod 8) by decide,
        changeLevel_ringHomComp_intCast_apply _ _ (Int.isCoprime_iff_gcd_eq_one.mpr rfl),
        show χ₄ ((3 : ℤ) : ZMod 4) = -1 by decide, Int.cast_neg, Int.cast_one]
    · rw [h5, show (5 : ZMod 8) = ((5 : ℤ) : ZMod 8) by decide,
        changeLevel_ringHomComp_intCast_apply _ _ (Int.isCoprime_iff_gcd_eq_one.mpr rfl),
        show χ₄ ((5 : ℤ) : ZMod 4) = 1 by decide, Int.cast_one]
  · refine Or.inr (Or.inr (Or.inl (ext_of_level_eight ?_ ?_)))
    · rw [h3, MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈ (a := 3) (b := -1) (by decide),
        Int.cast_neg, Int.cast_one]
    · rw [h5, MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈ (a := 5) (b := -1) (by decide),
        Int.cast_neg, Int.cast_one]

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
    · exact MulChar.isQuadratic_one
    · exact (isQuadratic_χ₄.comp _).changeLevel h
    · exact (isQuadratic_χ₈.comp _).changeLevel h
    · exact (isQuadratic_χ₈'.comp _).changeLevel h

/-- A quadratic character of level `2 ^ k` has conductor `1`, `4` or `8`. -/
theorem conductor_eq_one_or_four_or_eight_of_isQuadratic {k : ℕ}
    {χ : DirichletCharacter R (2 ^ k)} (hχ : χ.IsQuadratic) :
    χ.conductor = 1 ∨ χ.conductor = 4 ∨ χ.conductor = 8 :=
  conductor_eq_one_or_four_or_eight_of_sq_eq_one hχ.sq_eq_one

/-! ### Conductors of the classical dyadic characters -/

section Conductor

variable [NeZero (2 : R)]

/-- When `2 ≠ 0` in the coefficient ring, `χ₄` is primitive of conductor `4`. -/
theorem conductor_χ₄_ringHomComp : conductor (χ₄.ringHomComp (Int.castRingHom R)) = 4 := by
  refine conductor_eq_four_of_apply_one_ne_apply_three _ ?_
  rw [MulChar.ringHomComp_intCast_apply_of_apply_eq χ₄ (b := 1) (by decide),
    MulChar.ringHomComp_intCast_apply_of_apply_eq χ₄ (b := -1) (by decide)]
  simpa [eq_neg_iff_add_eq_zero, one_add_one_eq_two] using two_ne_zero (α := R)

/-- When `2 ≠ 0` in the coefficient ring, `χ₈` is primitive of conductor `8`. -/
theorem conductor_χ₈_ringHomComp : conductor (χ₈.ringHomComp (Int.castRingHom R)) = 8 := by
  refine conductor_eq_eight_of_apply_one_ne_apply_five _ ?_
  rw [MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈ (b := 1) (by decide),
    MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈ (b := -1) (by decide)]
  simpa [eq_neg_iff_add_eq_zero, one_add_one_eq_two] using two_ne_zero (α := R)

/-- When `2 ≠ 0` in the coefficient ring, `χ₈'` is primitive of conductor `8`. -/
theorem conductor_χ₈'_ringHomComp : conductor (χ₈'.ringHomComp (Int.castRingHom R)) = 8 := by
  refine conductor_eq_eight_of_apply_one_ne_apply_five _ ?_
  rw [MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈' (b := 1) (by decide),
    MulChar.ringHomComp_intCast_apply_of_apply_eq χ₈' (b := -1) (by decide)]
  simpa [eq_neg_iff_add_eq_zero, one_add_one_eq_two] using two_ne_zero (α := R)

end Conductor

end Classification

end DirichletCharacter
