/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Suyama.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Examples of Suyama's parametrization and ellipticity criteria

Rational parameters separate the elliptic regime from each mode of degeneration:
* `σ = 6` over `ℚ` has `u = 31`, `v = 24`, scaled doubling relation `4N = (A + 2)D`, every
  exceptional factor nonzero, an elliptic model, and a native point `suyamaPoint` represented by
  `(31³, 24³)`.
* `σ = 5` over `ℚ` has `u = v = 20` and nonzero denominator `4 u³ v = 640000`, yet `x = 1`,
  `A = -2`, and `B = 0`, detected by the factor `σ² - 25 = 0`.
* `σ = 3` over `ℚ` has `A = 2` and `B ≠ 0`: the model is singular, yet `suyamaPoint` still exists
  as a nonsingular native point with projective `x`-coordinate `(4³ : 12³)`.
* `σ = 0` over `ℚ` has `A = -2` and `B = 0` while all five polynomial factors of
  `isElliptic_model_suyama_iff` are nonzero, witnessing necessity of the hypothesis `σ ≠ 0`.

Over prime fields:
* Modulo `7`, `σ = 2` has `u = 6`, `v = 1`, a unit denominator, `B = 0`, and `A² = 4` because
  `σ² - 25 = 0`; moreover, every `σ : ZMod 7` gives a singular model since `{1, 9, 25}` exhausts
  the nonzero squares modulo `7`.
* Modulo `11`, `σ = 2` has `σ² ≠ 25` and `B = 9 ≠ 0`, yet `9σ² - 25 = 0` forces `A² = 4` and
  refutes any criterion omitting `9σ² - 25`; meanwhile `σ = 4` satisfies `σ² = 5` (`u = 0`) with
  all five factors of `isElliptic_model_suyama_iff` nonzero, witnessing necessity of `σ² ≠ 5`.
* Every parameter in `ZMod 2`, `ZMod 3`, `ZMod 5`, `ZMod 7`, and `ZMod 11` is exceptional, whereas
  `σ = 2` over `ZMod 13` yields an elliptic Suyama curve, making `13` the smallest prime whose
  prime field admits one.

In characteristic three, `9σ² - 25 = -1` and `σ² - 9 = σ²`, reducing ellipticity to
`σ ≠ 0 ∧ σ⁴ ≠ 1` (and to `suyamaB σ ≠ 0`). Although every `σ : ZMod 3` is exceptional, both the
rational function field `RatFunc (ZMod 3)` at `RatFunc.X` and the nine-element finite field
`GaloisField 3 2` admit elliptic Suyama models.

## References

* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1, p. 3.
-/

namespace TauCeti.Montgomery

/-! ### Rational parameters: elliptic, singular and degenerate cases -/

-- σ = 6 over ℚ: auxiliary values u = 31, v = 24, nonvanishing of all five criterion factors,
-- and ellipticity of the resulting Montgomery model.
example : suyamaU (6 : ℚ) = 31 ∧ suyamaV (6 : ℚ) = 24 ∧
    ((6 : ℚ) ^ 2 - 1) ≠ 0 ∧ ((6 : ℚ) ^ 2 - 9) ≠ 0 ∧ ((6 : ℚ) ^ 2 - 25) ≠ 0 ∧
    (9 * (6 : ℚ) ^ 2 - 25) ≠ 0 ∧ ((6 : ℚ) ^ 2 + 5) ≠ 0 ∧
    (model (suyamaA (6 : ℚ)) (suyamaB (6 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- σ = 6 over ℚ: the scaled doubling constants N = (v - u)³ (3u + v) and D = 16 u³ v
-- satisfy 4N = (A + 2)D.
example : 4 * ((24 - 31 : ℚ) ^ 3 * (3 * 31 + 24)) =
    (suyamaA (6 : ℚ) + 2) * (16 * 31 ^ 3 * 24) := by
  have h := suyama_doubling_relation (σ := (6 : ℚ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [suyamaU_def, suyamaV_def] at h ⊢
  exact h

-- σ = 6 over ℚ: the polynomial seed (31³, 24³) represents the supplied native point.
example : ∃ hB : suyamaB (6 : ℚ) ≠ 0,
    (⟨31 ^ 3, 24 ^ 3⟩ : Pair ℚ).cross
      (coordinates (suyamaA 6) (suyamaB 6) (suyamaPoint (by norm_num) hB)) = 0 := by
  have hB : suyamaB (6 : ℚ) ≠ 0 := by
    rw [suyamaB_eq (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hB, ?_⟩
  convert cross_coordinates_suyamaPoint (by norm_num) hB using 1
  norm_num [suyamaU_def, suyamaV_def]

-- σ = 5 over ℚ: u = v = 20 and 4 u³ v = 640000 ≠ 0, yet x = 1, A = -2, and B = 0;
-- the factor σ² - 25 vanishes and the model is singular.
example : suyamaU (5 : ℚ) = 20 ∧ suyamaV (5 : ℚ) = 20 ∧
    4 * suyamaU (5 : ℚ) ^ 3 * suyamaV (5 : ℚ) = 640000 ∧
    suyamaX (5 : ℚ) = 1 ∧ suyamaA (5 : ℚ) = -2 ∧ suyamaB (5 : ℚ) = 0 ∧
    (5 : ℚ) ^ 2 - 25 = 0 ∧
    ¬ (model (suyamaA (5 : ℚ)) (suyamaB (5 : ℚ))).IsElliptic := by
  have hA : suyamaA (5 : ℚ) = -2 := by
    have h := suyamaA_add_two (5 : ℚ)
    norm_num at h
    linarith
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num [suyamaX_def, suyamaB_def, hA]

-- σ = 3 over ℚ: A = 2 and B ≠ 0, so the model is singular, yet its supplied native point
-- still exists and has projective x-coordinate (4³ : 12³).
example : suyamaA (3 : ℚ) = 2 ∧ ¬ (model (suyamaA (3 : ℚ)) (suyamaB (3 : ℚ))).IsElliptic := by
  have hA : suyamaA (3 : ℚ) = 2 := by
    have h := suyamaA_add_two (3 : ℚ)
    norm_num at h
    linarith
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num [hA]

example : ∃ hB : suyamaB (3 : ℚ) ≠ 0,
    projectiveX (suyamaA 3) hB (suyamaPoint (by norm_num) hB) =
      (⟨4 ^ 3, 12 ^ 3⟩ : Pair ℚ).toProj (by simp [Pair.eq_zero_iff]) := by
  have hB : suyamaB (3 : ℚ) ≠ 0 := by
    rw [suyamaB_eq (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hB, ?_⟩
  convert projectiveX_suyamaPoint (by norm_num) hB using 1
  norm_num [suyamaU_def, suyamaV_def]

-- σ = 0 over ℚ: all five factors of isElliptic_model_suyama_iff are nonzero (28125 ≠ 0),
-- yet A = -2 and B = 0 make the model singular, witnessing necessity of σ ≠ 0.
example : ((0 : ℚ) ^ 2 - 1) * ((0 : ℚ) ^ 2 - 9) * ((0 : ℚ) ^ 2 - 25) *
      (9 * (0 : ℚ) ^ 2 - 25) * ((0 : ℚ) ^ 2 + 5) = 28125 ∧
    suyamaA (0 : ℚ) = -2 ∧ suyamaB (0 : ℚ) = 0 ∧
    ¬ (model (suyamaA (0 : ℚ)) (suyamaB (0 : ℚ))).IsElliptic := by
  have hA : suyamaA (0 : ℚ) = -2 := by
    have h := suyamaA_add_two (0 : ℚ)
    norm_num at h
    linarith
  have hB : suyamaB (0 : ℚ) = 0 := by
    simp [suyamaB_def, suyamaX_def]
  rw [isElliptic_model_iff_ne_zero, hA, hB]
  norm_num

/-! ### Prime fields: exceptionality up to `11`, and ellipticity modulo `13` -/

section Seven

variable [Fact (Nat.Prime 7)]

-- σ = 2 over 𝔽₇: u = 6, v = 1, the denominator is a unit, yet σ² - 25 = 0 forces
-- B = 0 and A² = 4.
example : suyamaU (2 : ZMod 7) = 6 ∧ suyamaV (2 : ZMod 7) = 1 ∧
    IsUnit (4 * suyamaU (2 : ZMod 7) ^ 3 * suyamaV (2 : ZMod 7)) ∧
    (2 : ZMod 7) ^ 2 - 25 = 0 ∧
    suyamaB (2 : ZMod 7) = 0 ∧ suyamaA (2 : ZMod 7) ^ 2 = 4 ∧
    ¬ (model (suyamaA (2 : ZMod 7)) (suyamaB (2 : ZMod 7))).IsElliptic := by
  refine ⟨by simp only [suyamaU_def]; decide +revert, by simp only [suyamaV_def]; decide +revert,
    ?_, by decide +revert, ?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, suyamaU_def, suyamaV_def]
    decide +revert
  · rw [suyamaB_eq (by decide +revert) (by decide +revert) (by decide +revert),
      suyamaU_def, suyamaV_def, div_eq_zero_iff]
    left
    decide +revert
  · apply sub_eq_zero.mp
    rw [suyamaA_sq_sub_four (by decide +revert) (by decide +revert) (by decide +revert),
      suyamaU_def, suyamaV_def, div_eq_zero_iff]
    left
    decide +revert
  · rw [isElliptic_model_suyama_iff (by decide +revert) (by decide +revert) (by decide +revert)]
    decide +revert

-- Over 𝔽₇ every parameter σ is exceptional: σ = 0 gives B = 0, while {1, 9, 25} ≡ {1, 2, 4}
-- exhausts the nonzero squares modulo 7.
example : ∀ σ : ZMod 7, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  intro σ
  by_cases hσ : σ = 0
  · subst hσ
    rw [isElliptic_model_iff_ne_zero]
    simp [suyamaB_def, suyamaX_def]
  · have hu : σ ^ 2 ≠ 5 := by decide +revert
    rw [isElliptic_model_suyama_iff (by decide +revert) hσ hu]
    decide +revert

end Seven

section Eleven

variable [Fact (Nat.Prime 11)]

-- σ = 2 over 𝔽₁₁: σ² ≠ 25 and B = 9 ≠ 0, yet 9σ² - 25 = 0 forces A² = 4; a four-factor
-- criterion omitting 9σ² - 25 is nonzero here and is therefore refuted.
example : (2 : ZMod 11) ^ 2 ≠ 25 ∧
    9 * (2 : ZMod 11) ^ 2 - 25 = 0 ∧
    suyamaB (2 : ZMod 11) = 9 ∧
    suyamaA (2 : ZMod 11) ^ 2 = 4 ∧
    ((2 : ZMod 11) ^ 2 - 1) * ((2 : ZMod 11) ^ 2 - 9) *
      ((2 : ZMod 11) ^ 2 - 25) * ((2 : ZMod 11) ^ 2 + 5) ≠ 0 ∧
    ¬ (model (suyamaA (2 : ZMod 11)) (suyamaB (2 : ZMod 11))).IsElliptic := by
  refine ⟨by decide +revert, by decide +revert, ?_, ?_, by decide +revert, ?_⟩
  · rw [suyamaB_eq (by decide +revert) (by decide +revert) (by decide +revert),
      suyamaU_def, suyamaV_def]
    exact (div_eq_iff (by decide +revert)).mpr (by decide +revert)
  · apply sub_eq_zero.mp
    rw [suyamaA_sq_sub_four (by decide +revert) (by decide +revert) (by decide +revert),
      suyamaU_def, suyamaV_def, div_eq_zero_iff]
    left
    decide +revert
  · rw [isElliptic_model_suyama_iff (by decide +revert) (by decide +revert) (by decide +revert)]
    decide +revert

-- σ = 4 over 𝔽₁₁: 4² = 5 so u = 0 and B = 0, while all five factors of
-- isElliptic_model_suyama_iff are nonzero, witnessing necessity of the hypothesis σ² ≠ 5.
example : (4 : ZMod 11) ^ 2 = 5 ∧ suyamaB (4 : ZMod 11) = 0 ∧
    ((4 : ZMod 11) ^ 2 - 1) * ((4 : ZMod 11) ^ 2 - 9) * ((4 : ZMod 11) ^ 2 - 25) *
      (9 * (4 : ZMod 11) ^ 2 - 25) * ((4 : ZMod 11) ^ 2 + 5) ≠ 0 ∧
    ¬ (model (suyamaA (4 : ZMod 11)) (suyamaB (4 : ZMod 11))).IsElliptic := by
  have h₅ : (4 : ZMod 11) ^ 2 = 5 := by decide +revert
  refine ⟨h₅, ?_, by decide +revert, ?_⟩
  · simp [suyamaB_def, suyamaX_def, sub_eq_zero.mpr h₅]
  · rw [isElliptic_model_iff_ne_zero]
    simp [suyamaB_def, suyamaX_def, sub_eq_zero.mpr h₅]

-- Every parameter over 𝔽₁₁ is in fact exceptional: its five nonzero quadratic residues
-- {1, 3, 4, 5, 9} hit σ² = 1, σ² = 25, 9σ² = 25, σ² = 5, and σ² = 9 respectively.
example : ∀ σ : ZMod 11, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  intro σ
  by_cases hσ : σ = 0
  · subst hσ
    rw [isElliptic_model_iff_ne_zero]
    simp [suyamaB_def, suyamaX_def]
  by_cases hu : σ ^ 2 = 5
  · rw [isElliptic_model_iff_ne_zero]
    simp [suyamaB_def, suyamaX_def, sub_eq_zero.mpr hu]
  · rw [isElliptic_model_suyama_iff (by decide +revert) hσ hu]
    decide +revert

end Eleven

-- Over 𝔽₂ and 𝔽₅ every parameter is exceptional as well.
example [Fact (Nat.Prime 5)] :
    (∀ σ : ZMod 2, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic) ∧
    (∀ σ : ZMod 5, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic) := by
  refine ⟨fun σ h ↦ (isElliptic_model_iff_ne_zero.mp h).1 (by decide), fun σ ↦ ?_⟩
  by_cases hσ : σ = 0
  · subst hσ
    rw [isElliptic_model_iff_ne_zero]
    simp [suyamaB_def, suyamaX_def]
  · have hu : σ ^ 2 ≠ 5 := by decide +revert
    rw [isElliptic_model_suyama_iff (by decide +revert) hσ hu]
    decide +revert

-- Over 𝔽₁₃, σ = 2 gives an elliptic Suyama curve; combined with the global checks for
-- p ∈ {2, 3, 5, 7, 11}, p = 13 is the smallest prime whose prime field admits one.
example [Fact (Nat.Prime 13)] :
    (model (suyamaA (2 : ZMod 13)) (suyamaB (2 : ZMod 13))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by decide +revert) (by decide +revert) (by decide +revert)]
  decide +revert

/-! ### Characteristic three -/

section CharThree

-- Over any commutative ring of characteristic three, u = σ² + 1, v = σ, 9σ² - 25 = -1,
-- and σ² - 9 = σ²; over a field, under σ² ≠ 5 the five-factor criterion reduces to
-- σ (σ² - 1)(σ² - 25)(σ² + 5) ≠ 0, and unconditionally to σ ≠ 0 ∧ σ⁴ ≠ 1.
example {R : Type*} [CommRing R] [CharP R 3] (σ : R) :
    suyamaU σ = σ ^ 2 + 1 ∧ suyamaV σ = σ ∧
      9 * σ ^ 2 - 25 = -1 ∧ σ ^ 2 - 9 = σ ^ 2 := by
  have h₃ : (3 : R) = 0 := CharP.ofNat_eq_zero R 3
  exact ⟨suyamaU_of_char_three σ, suyamaV_of_char_three σ,
    by linear_combination (3 * σ ^ 2 - 8) * h₃, by linear_combination -3 * h₃⟩

example {K : Type*} [Field K] [CharP K 3] {σ : K} (hu : σ ^ 2 ≠ 5) :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔
      σ * (σ ^ 2 - 1) * (σ ^ 2 - 25) * (σ ^ 2 + 5) ≠ 0 := by
  have h₃ : (3 : K) = 0 := CharP.ofNat_eq_zero K 3
  have h₂₅ : σ ^ 2 - 25 = σ ^ 2 - 1 := by linear_combination -8 * h₃
  have h₅ : σ ^ 2 + 5 = σ ^ 2 - 1 := by linear_combination 2 * h₃
  have hu' : σ ^ 2 + 1 ≠ 0 := by
    rw [← suyamaU_of_char_three, suyamaU_def]
    exact sub_ne_zero.mpr hu
  have h₁ : σ ^ 4 - 1 = (σ ^ 2 - 1) * (σ ^ 2 + 1) := by ring
  rw [isElliptic_model_suyama_iff_of_char_three, h₂₅, h₅, ← sub_ne_zero (a := σ ^ 4), h₁]
  simp only [ne_eq, mul_eq_zero, hu', or_false]
  tauto

-- Over 𝔽₃ every element satisfies σ = 0 or σ⁴ = 1, so no parameter over 𝔽₃ is elliptic.
example : ∀ σ : ZMod 3, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  simp only [isElliptic_model_suyama_iff_of_char_three]
  decide

-- Over the characteristic-three function field 𝔽₃(X), the indeterminate X gives an explicit
-- elliptic Suyama curve with nonzero `suyamaB`.
example : (model (suyamaA (RatFunc.X : RatFunc (ZMod 3)))
      (suyamaB (RatFunc.X : RatFunc (ZMod 3)))).IsElliptic ∧
    suyamaB (RatFunc.X : RatFunc (ZMod 3)) ≠ 0 := by
  have hE : (model (suyamaA (RatFunc.X : RatFunc (ZMod 3)))
      (suyamaB (RatFunc.X : RatFunc (ZMod 3)))).IsElliptic := by
    rw [isElliptic_model_suyama_iff_of_char_three]
    refine ⟨RatFunc.X_ne_zero, fun h₄ ↦ ?_⟩
    rw [← RatFunc.algebraMap_X, ← map_pow,
      ← map_one (algebraMap (Polynomial (ZMod 3)) _)] at h₄
    have hp := RatFunc.algebraMap_injective (ZMod 3) h₄
    have hev : (0 : ZMod 3) = 1 := by
      simpa using congrArg (Polynomial.eval 0) hp
    exact zero_ne_one hev
  exact ⟨hE, isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three.mp hE⟩

-- Over the nine-element finite field 𝔽₉ = GaloisField 3 2, the unit group has order 8,
-- which does not divide 4, so characteristic three also admits finite-field elliptic Suyama curves.
example : ∃ σ : GaloisField 3 2, (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have h : ¬ ∀ x : (GaloisField 3 2)ˣ, x ^ 4 = 1 := by
    rw [FiniteField.forall_pow_eq_one_iff, ← Nat.card_eq_fintype_card,
      GaloisField.card 3 2 (by decide)]
    decide
  obtain ⟨x, hx⟩ := not_forall.mp h
  exact ⟨x, isElliptic_model_suyama_iff_of_char_three.mpr
    ⟨x.ne_zero, fun h₄ ↦ hx (Units.ext h₄)⟩⟩

end CharThree

end TauCeti.Montgomery
