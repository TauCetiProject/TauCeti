/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Suyama.Point
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Examples of Suyama's parametrization and ellipticity criteria

Rational parameters separate the elliptic regime from each mode of degeneration:
* `σ = 6` over `ℚ` has `u = 31`, `v = 24`, scaled doubling relation `4N = (A + 2)D`, every
  exceptional factor nonzero, an elliptic model, and a native point `suyamaPoint` represented by
  `(31³, 24³)` that is neither infinity, `twoTorsionPoint`, nor of order two.
* `σ = 5` over `ℚ` has `u = v = 20` and nonzero denominator `4 u³ v = 640000`, yet `x = 1`,
  `A = -2`, and `B = x(x - 1)² = 0`, detected by the factor `σ² - 25 = 0`.
* `σ = 3` over `ℚ` has `A = 2` and `B ≠ 0`: the model is singular, yet `suyamaPoint` still exists
  as a nonsingular native point with projective coordinate `(4³ : 12³)` and commutes with field
  embeddings.
* `σ = 0` over `ℚ` has `A = -2` and `B = 0` while all five polynomial factors of
  `isElliptic_model_suyama_iff` are nonzero, showing why `σ ≠ 0` is required there and how
  `isElliptic_model_suyama_iff_ne_zero` handles `σ = 0` unconditionally.

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

public section

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
  have h := suyama_doubling_relation (σ := (6 : ℚ)) (by norm_num) (by norm_num)
  norm_num [suyamaU_def, suyamaV_def] at h ⊢
  exact h

-- σ = 6 over ℚ: the polynomial seed (31³, 24³) represents suyamaPoint, which is nonzero,
-- distinct from the distinguished two-torsion point, and not killed by 2.
example : ∃ hB : suyamaB (6 : ℚ) ≠ 0,
    (⟨31 ^ 3, 24 ^ 3⟩ : Pair ℚ).cross
      (coordinates (suyamaA 6) (suyamaB 6) (suyamaPoint hB)) = 0 ∧
    suyamaPoint hB ≠ 0 ∧
    suyamaPoint hB ≠ twoTorsionPoint (suyamaA 6) hB ∧
    suyamaPoint hB + suyamaPoint hB ≠ 0 := by
  have hB : suyamaB (6 : ℚ) ≠ 0 := by
    rw [suyamaB_ne_zero_iff]
    norm_num
  refine ⟨hB, ?_, suyamaPoint_ne_zero hB, suyamaPoint_ne_twoTorsionPoint hB,
    suyamaPoint_add_self_ne_zero hB⟩
  convert cross_coordinates_suyamaPoint hB using 1
  norm_num [suyamaU_def, suyamaV_def]

-- σ = 5 over ℚ: u = v = 20 and 4 u³ v = 640000 ≠ 0, yet x = 1, A = -2, and
-- B = x(x - 1)² = 0; the factor σ² - 25 vanishes and the model is singular.
example : suyamaU (5 : ℚ) = 20 ∧ suyamaV (5 : ℚ) = 20 ∧
    4 * suyamaU (5 : ℚ) ^ 3 * suyamaV (5 : ℚ) = 640000 ∧
    suyamaX (5 : ℚ) = 1 ∧ suyamaA (5 : ℚ) = -2 ∧ suyamaB (5 : ℚ) = 0 ∧
    (5 : ℚ) ^ 2 - 25 = 0 ∧
    ¬ (model (suyamaA (5 : ℚ)) (suyamaB (5 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num [suyamaX_def, suyamaA_def, suyamaB_def]

-- σ = 3 over ℚ: A = 2 and B ≠ 0, so the model is singular, yet its supplied native point
-- still exists, has projective coordinate (4³ : 12³), and commutes with field embeddings.
example : suyamaA (3 : ℚ) = 2 ∧ ¬ (model (suyamaA (3 : ℚ)) (suyamaB (3 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num [suyamaA_def]

example : ∃ hB : suyamaB (3 : ℚ) ≠ 0,
    projectiveX (suyamaA 3) hB (suyamaPoint hB) =
      (⟨4 ^ 3, 12 ^ 3⟩ : Pair ℚ).toProj (by simp [Pair.eq_zero_iff]) := by
  have hB : suyamaB (3 : ℚ) ≠ 0 := by
    rw [suyamaB_ne_zero_iff]
    norm_num
  refine ⟨hB, ?_⟩
  convert projectiveX_suyamaPoint hB using 1
  norm_num [suyamaU_def, suyamaV_def]

example {L : Type*} [Field L] [CharZero L] :
    ∃ (hB : suyamaB (3 : ℚ) ≠ 0) (hBL : suyamaB (3 : L) ≠ 0),
      (Rat.castHom L).mapProjective (projectiveX (suyamaA 3) hB (suyamaPoint hB)) =
        projectiveX (suyamaA (3 : L)) hBL (suyamaPoint hBL) := by
  have hB : suyamaB (3 : ℚ) ≠ 0 := by
    rw [suyamaB_ne_zero_iff]
    norm_num
  rw [← map_ofNat (Rat.castHom L) 3]
  exact ⟨hB, by rwa [← map_suyamaB, map_ne_zero],
    mapProjective_projectiveX_suyamaPoint (Rat.castHom L) hB _⟩

-- σ = 0 over ℚ: all five factors of isElliptic_model_suyama_iff are nonzero (28125 ≠ 0),
-- yet B = 0 and the model is singular, showing that σ ≠ 0 cannot be dropped there.
example : ((0 : ℚ) ^ 2 - 1) * ((0 : ℚ) ^ 2 - 9) * ((0 : ℚ) ^ 2 - 25) *
      (9 * (0 : ℚ) ^ 2 - 25) * ((0 : ℚ) ^ 2 + 5) = 28125 ∧
    suyamaA (0 : ℚ) = -2 ∧ suyamaB (0 : ℚ) = 0 ∧
    ¬ (model (suyamaA (0 : ℚ)) (suyamaB (0 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff_ne_zero, suyamaA_zero, suyamaB_zero]
  norm_num

/-! ### Prime fields: exceptionality up to `11`, and ellipticity modulo `13` -/

section Seven

local instance suyamaPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

-- σ = 2 over 𝔽₇: u = 6, v = 1, the denominator is a unit, yet σ² - 25 = 0 forces
-- B = 0 and A² = 4.
example : suyamaU (2 : ZMod 7) = 6 ∧ suyamaV (2 : ZMod 7) = 1 ∧
    IsUnit (4 * suyamaU (2 : ZMod 7) ^ 3 * suyamaV (2 : ZMod 7)) ∧
    (2 : ZMod 7) ^ 2 - 25 = 0 ∧
    suyamaB (2 : ZMod 7) = 0 ∧ suyamaA (2 : ZMod 7) ^ 2 = 4 ∧
    ¬ (model (suyamaA (2 : ZMod 7)) (suyamaB (2 : ZMod 7))).IsElliptic := by
  have hB : suyamaB (2 : ZMod 7) = 0 := by
    rw [suyamaB_eq, suyamaU_def, suyamaV_def, div_eq_zero_iff]
    left
    decide
  have hA : suyamaA (2 : ZMod 7) ^ 2 = 4 :=
    not_ne_iff.mp (suyamaA_sq_ne_four_iff.not.mpr (by decide))
  have hE : ¬ (model (suyamaA (2 : ZMod 7)) (suyamaB (2 : ZMod 7))).IsElliptic := by
    rw [isElliptic_model_suyama_iff_ne_zero]
    decide
  refine ⟨by simp only [suyamaU_def]; decide, by simp only [suyamaV_def]; decide,
    ?_, by decide, hB, hA, hE⟩
  rw [isUnit_iff_ne_zero, suyamaU_def, suyamaV_def]
  decide

-- Over 𝔽₇ every parameter σ is exceptional: σ = 0 gives B = 0, while {1, 9, 25} ≡ {1, 2, 4}
-- exhausts the nonzero squares modulo 7.
example : ∀ σ : ZMod 7, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  simp only [isElliptic_model_suyama_iff_ne_zero]
  decide

end Seven

section Eleven

local instance suyamaPrimeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

-- σ = 2 over 𝔽₁₁: σ² ≠ 25 and B = 9 ≠ 0, yet 9σ² - 25 = 0 forces A² = 4; a four-factor
-- criterion omitting 9σ² - 25 is nonzero here and is therefore refuted.
example : (2 : ZMod 11) ^ 2 ≠ 25 ∧
    9 * (2 : ZMod 11) ^ 2 - 25 = 0 ∧
    suyamaB (2 : ZMod 11) = 9 ∧
    suyamaA (2 : ZMod 11) ^ 2 = 4 ∧
    ((2 : ZMod 11) ^ 2 - 1) * ((2 : ZMod 11) ^ 2 - 9) *
      ((2 : ZMod 11) ^ 2 - 25) * ((2 : ZMod 11) ^ 2 + 5) ≠ 0 ∧
    ¬ (model (suyamaA (2 : ZMod 11)) (suyamaB (2 : ZMod 11))).IsElliptic := by
  have hB : suyamaB (2 : ZMod 11) = 9 := by
    rw [suyamaB_eq, suyamaU_def, suyamaV_def]
    apply (div_eq_iff (by decide)).mpr
    decide
  have hA : suyamaA (2 : ZMod 11) ^ 2 = 4 :=
    not_ne_iff.mp (suyamaA_sq_ne_four_iff.not.mpr (by decide))
  have hE : ¬ (model (suyamaA (2 : ZMod 11)) (suyamaB (2 : ZMod 11))).IsElliptic := by
    rw [isElliptic_model_suyama_iff_ne_zero]
    decide
  exact ⟨by decide, by decide, hB, hA, by decide, hE⟩

-- σ = 4 over 𝔽₁₁: 4² = 5 so u = 0 and B = 0, while all five factors of
-- isElliptic_model_suyama_iff are nonzero, witnessing necessity of the hypothesis σ² ≠ 5.
example : (4 : ZMod 11) ^ 2 = 5 ∧ suyamaB (4 : ZMod 11) = 0 ∧
    ((4 : ZMod 11) ^ 2 - 1) * ((4 : ZMod 11) ^ 2 - 9) * ((4 : ZMod 11) ^ 2 - 25) *
      (9 * (4 : ZMod 11) ^ 2 - 25) * ((4 : ZMod 11) ^ 2 + 5) ≠ 0 ∧
    ¬ (model (suyamaA (4 : ZMod 11)) (suyamaB (4 : ZMod 11))).IsElliptic := by
  have hB : suyamaB (4 : ZMod 11) = 0 :=
    not_ne_iff.mp (suyamaB_ne_zero_iff.not.mpr (by decide))
  have hE : ¬ (model (suyamaA (4 : ZMod 11)) (suyamaB (4 : ZMod 11))).IsElliptic := by
    rw [isElliptic_model_suyama_iff_ne_zero]
    decide
  exact ⟨by decide, hB, by decide, hE⟩

-- Every parameter over 𝔽₁₁ is in fact exceptional: its five nonzero quadratic residues
-- {1, 3, 4, 5, 9} hit σ² = 1, σ² = 25, 9σ² = 25, σ² = 5, and σ² = 9 respectively.
example : ∀ σ : ZMod 11, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  simp only [isElliptic_model_suyama_iff_ne_zero]
  decide

end Eleven

section SmallPrimesAndThirteen

local instance suyamaPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance suyamaPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance suyamaPrimeThirteen : Fact (Nat.Prime 13) := ⟨by decide⟩

-- Over 𝔽₂ and 𝔽₅ every parameter is exceptional as well.
example : (∀ σ : ZMod 2, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic) ∧
    (∀ σ : ZMod 5, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic) := by
  simp only [isElliptic_model_suyama_iff_ne_zero]
  decide

-- Over 𝔽₁₃, σ = 2 gives an elliptic Suyama curve; combined with the global checks for
-- p ∈ {2, 3, 5, 7, 11}, p = 13 is the smallest prime whose prime field admits one.
example : (model (suyamaA (2 : ZMod 13)) (suyamaB (2 : ZMod 13))).IsElliptic := by
  rw [isElliptic_model_suyama_iff_ne_zero]
  decide

end SmallPrimesAndThirteen

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
  have h₂ : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; decide)
  have hf : σ ^ 4 - 25 = (σ ^ 2 - 5) * (σ ^ 2 + 5) := by ring
  rw [isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three, suyamaB_ne_zero_iff, hf]
  simp only [ne_eq, mul_eq_zero, sub_eq_zero, h₂, hu, not_false_eq_true, false_or, true_and]
  tauto

local instance suyamaPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

-- Over 𝔽₃ every element satisfies σ = 0 or σ⁴ = 1, so no parameter over 𝔽₃ is elliptic.
example : ∀ σ : ZMod 3, ¬ (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  simp only [isElliptic_model_suyama_iff_of_char_three]
  decide

-- Over the characteristic-three function field 𝔽₃(X), the indeterminate X gives an explicit
-- elliptic Suyama curve together with its nonsingular native point.
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

-- Over the nine-element finite field 𝔽₉ = GaloisField 3 2, X⁵ - X has at most five roots,
-- so characteristic three also admits finite-field elliptic Suyama curves.
example : ∃ σ : GaloisField 3 2, (model (suyamaA σ) (suyamaB σ)).IsElliptic := by
  classical
  cases nonempty_fintype (GaloisField 3 2)
  by_contra! h
  let p : Polynomial (GaloisField 3 2) := Polynomial.X ^ 5 - Polynomial.X
  have hp : p ≠ 0 := by
    intro hp₀
    have h₅ : p.coeff 5 = 0 := by simp [hp₀]
    simp [p, Polynomial.coeff_X] at h₅
  have hdeg : p.natDegree ≤ 5 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hsub : (Finset.univ : Finset (GaloisField 3 2)) ⊆ p.roots.toFinset := by
    intro σ _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    have hσ := isElliptic_model_suyama_iff_of_char_three.not.mp (h σ)
    rcases not_and_or.mp hσ with h₀ | h₄
    · simp [p, not_not.mp h₀]
    · simp [p, pow_succ σ 4, not_not.mp h₄]
  have hcard : Fintype.card (GaloisField 3 2) ≤ 5 :=
    (Finset.card_le_card hsub).trans <|
      (Multiset.toFinset_card_le _).trans <| (Polynomial.card_roots' p).trans hdeg
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by decide)] at hcard
  norm_num at hcard

end CharThree

end TauCeti.Montgomery
