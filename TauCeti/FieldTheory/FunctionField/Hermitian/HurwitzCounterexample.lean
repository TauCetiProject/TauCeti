/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hermitian.Genus
public import TauCeti.FieldTheory.FunctionField.Hermitian.Translation
public import TauCeti.FieldTheory.FunctionField.Hermitian.Existence
public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.FieldTheory.FunctionField.Automorphism.HurwitzBound

/-!
# Hermitian counterexamples to the Hurwitz automorphism bound

Over the field with `q²` elements, the Hermitian function field has genus `q(q - 1)/2`
and its translation subgroup has order `q³`. For `q ≥ 41`, this finite subgroup exceeds
`84(g - 1)`. Thus the tame hypothesis in the Hurwitz automorphism bound is essential
in positive characteristic.

The concrete counterexample uses `q = 64` over `GaloisField 2 12`: there is a function field
of genus `2016` with a translation subgroup of order `262144`, exceeding `169260 = 84(g - 1)`.
The field and its coordinates are supplied by the existence theorem, and its genus and
subgroup order are computed from those coordinates.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 6.4 and Exercises 3.18 and 6.10.
-/

public section

namespace TauCeti

namespace IsHermitianCoordinates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {p n : ℕ} [ExpChar K p] {x y : F}

/-- For `q = pⁿ ≥ 41` over a field with `q²` elements, the translation subgroup of the
Hermitian function field exceeds the Hurwitz bound `84(g - 1)`. -/
theorem eighty_four_mul_genus_sub_one_lt_natCard_hermitianTranslations
    (h : IsHermitianCoordinates K (p ^ n) x y)
    (hK : Nat.card K = (p ^ n) ^ 2) (hq : 41 ≤ p ^ n) :
    84 * (genus K F - 1) < Nat.card (hermitianTranslations K p n x y) := by
  have hq' : 1 < p ^ n := by omega
  have hn : n ≠ 0 := by rintro rfl; simp at hq
  have hchar : ((p ^ n : ℕ) : K) = 0 := by
    rcases ‹ExpChar K p› with _ | hp
    · simp at hq
    · rw [Nat.cast_pow, CharP.cast_eq_zero K p, zero_pow hn]
  let : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (by omega))
  rw [h.natCard_hermitianTranslations hK]
  have hg := h.two_mul_genus_eq hq' hchar
  have hlt : 42 * (p ^ n - 1) < (p ^ n) ^ 2 := by
    have hsub : p ^ n - 1 + 1 = p ^ n := Nat.sub_add_cancel (by omega)
    nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < p ^ n)
  have hbound : 84 * genus K F < (p ^ n) ^ 3 := by nlinarith
  exact (Nat.mul_le_mul_left 84 (Nat.sub_le _ 1)).trans_lt hbound

/-- The extension over the field fixed by the Hermitian translations has a place that is
not tame whenever `q ≥ 41`.

The finite-group instance makes the fixed-field extension algebraic, so that its places and
tameness predicate can be formed. Its existence follows from the translation-group count. -/
theorem exists_not_isTame_hermitianTranslations
    (h : IsHermitianCoordinates K (p ^ n) x y)
    [Finite (hermitianTranslations K p n x y)]
    (hK : Nat.card K = (p ^ n) ^ 2) (hq : 41 ≤ p ^ n) :
    ∃ P : Place K F,
      ¬ Place.IsTame K (IntermediateField.fixedField (hermitianTranslations K p n x y)) P := by
  classical
  have hn : n ≠ 0 := by rintro rfl; simp at hq
  have hchar : ((p ^ n : ℕ) : K) = 0 := by
    rcases ‹ExpChar K p› with _ | hp
    · simp at hq
    · rw [Nat.cast_pow, CharP.cast_eq_zero K p, zero_pow hn]
  by_contra htame
  have hle := natCard_le_eighty_four_mul_genus_sub_one
    (h.isFunctionField (by omega)) (h.isIntegrallyClosedIn (by omega) hchar)
    (hermitianTranslations K p n x y) (h.two_le_genus (by omega) hchar)
    (not_exists_not.mp htame)
  exact (h.eighty_four_mul_genus_sub_one_lt_natCard_hermitianTranslations hK hq).not_ge hle

end IsHermitianCoordinates

/-- A characteristic-two Hermitian function field of genus `2016` has a finite translation
subgroup of order `262144`, strictly greater than `84(g - 1)`. In particular, its genus is
at least two, as required in the Hurwitz bound. -/
theorem exists_hermitianTranslations_hurwitz_counterexample :
    ∃ (F : Type) (_ : Field F) (_ : Algebra (GaloisField 2 12) F), ∃ x y : F,
      IsHermitianCoordinates (GaloisField 2 12) 64 x y ∧
      genus (GaloisField 2 12) F = 2016 ∧
      Finite (hermitianTranslations (GaloisField 2 12) 2 6 x y) ∧
      Nat.card (hermitianTranslations (GaloisField 2 12) 2 6 x y) = 262144 ∧
      84 * (genus (GaloisField 2 12) F - 1) <
        Nat.card (hermitianTranslations (GaloisField 2 12) 2 6 x y) := by
  obtain ⟨F, _, _, x, y, h⟩ :=
    exists_isHermitianCoordinates (GaloisField 2 12) (q := 64) (by decide)
  have h' : IsHermitianCoordinates (GaloisField 2 12) (2 ^ 6) x y := h
  have hK : Nat.card (GaloisField 2 12) = (2 ^ 6) ^ 2 := by
    rw [GaloisField.card 2 12 (by decide)]
    norm_num
  have hg : genus (GaloisField 2 12) F = 2016 := by
    have hchar : (64 : GaloisField 2 12) = 0 := by
      exact (CharP.cast_eq_zero_iff (GaloisField 2 12) 2 64).mpr (by decide)
    have hgenus := h.two_mul_genus_eq (by decide) hchar
    omega
  have hcard : Nat.card (hermitianTranslations (GaloisField 2 12) 2 6 x y) = 262144 := by
    simpa using h'.natCard_hermitianTranslations hK
  refine ⟨F, inferInstance, inferInstance, x, y, h, hg,
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide), hcard, ?_⟩
  exact h'.eighty_four_mul_genus_sub_one_lt_natCard_hermitianTranslations hK (by decide)

end TauCeti
