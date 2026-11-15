/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Basic

/-!
# Suyama's family of Montgomery curves

Suyama's parametrization supplies a Montgomery curve together with a rational point. Put
`u = σ² - 5` and `v = 4σ`. The parameter `suyamaA σ` is chosen so that its scaled doubling
constants have polynomial expressions; `suyamaB σ` makes `(u³/v³, 1)` a point on the curve.

Through field division by zero, the rational factorizations `suyamaB_eq` and `suyamaA_sq_sub_four`
hold for every parameter `σ` in every field, with no denominator restriction. They yield
exact nonvanishing criteria `suyamaB_ne_zero_iff` and `suyamaA_sq_ne_four_iff`, as well as the
unconditional ellipticity equivalence `isElliptic_model_suyama_iff_ne_zero`. Under the standing
restrictions `(2 : K) ≠ 0`, `σ ≠ 0` and `σ² ≠ 5` — which by `suyamaX_ne_zero_iff` hold precisely
when the supplied `x`-coordinate `suyamaX σ` is nonzero — `isElliptic_model_suyama_iff` recovers
the five-factor criterion.

In characteristic three, `9σ² - 25 = -1` and `σ² - 9 = σ²` introduce no additional obstructions
beyond those of `suyamaB`: `isElliptic_model_suyama_iff_of_char_three` reduces ellipticity to
`σ ≠ 0 ∧ σ⁴ ≠ 1`, and `isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three` identifies
elliptic Suyama models in characteristic three with those having `suyamaB σ ≠ 0`.

## Main definitions

* `TauCeti.Montgomery.suyamaU`, `TauCeti.Montgomery.suyamaV`: the auxiliary polynomials
  `u = σ² - 5` and `v = 4σ`.
* `TauCeti.Montgomery.suyamaA`, `TauCeti.Montgomery.suyamaX`, `TauCeti.Montgomery.suyamaB`:
  Suyama's Montgomery curve parameters and supplied affine `x`-coordinate `u³/v³`.

## Main results

* `TauCeti.Montgomery.map_suyamaA`, `TauCeti.Montgomery.map_suyamaX`,
  `TauCeti.Montgomery.map_suyamaB`: Suyama's parameters commute with field homomorphisms.
* `TauCeti.Montgomery.suyamaX_ne_zero_iff`, `TauCeti.Montgomery.suyamaB_ne_zero_iff`,
  `TauCeti.Montgomery.suyamaA_sq_ne_four_iff`: unconditional nonvanishing criteria for `suyamaX`,
  `suyamaB` and `suyamaA² - 4`.
* `TauCeti.Montgomery.suyamaB_eq`, `TauCeti.Montgomery.suyamaA_sq_sub_four`: unconditional
  factorizations of `suyamaB` and `suyamaA² - 4`.
* `TauCeti.Montgomery.isElliptic_model_suyama_iff_ne_zero` and
  `TauCeti.Montgomery.isElliptic_model_suyama_iff`: unconditional and denominator-restricted
  exact ellipticity criteria.
* `TauCeti.Montgomery.isElliptic_model_suyama_iff_of_char_three` and
  `TauCeti.Montgomery.isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three`: reduced
  ellipticity criteria in characteristic three.

## References

* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1, p. 3,
  for Suyama's parametrization.
-/

public section

namespace TauCeti.Montgomery

section CommRing

variable {R : Type*} [CommRing R]

/-- The auxiliary polynomial `u = σ² - 5` in Suyama's parametrization. -/
def suyamaU (σ : R) : R := σ ^ 2 - 5

/-- The auxiliary polynomial `v = 4σ` in Suyama's parametrization. -/
def suyamaV (σ : R) : R := 4 * σ

@[simp] theorem suyamaU_def (σ : R) : suyamaU σ = σ ^ 2 - 5 := (rfl)
@[simp] theorem suyamaV_def (σ : R) : suyamaV σ = 4 * σ := (rfl)

/-- The first linear factorization used in the numerator of `A + 2`. -/
theorem suyamaV_sub_suyamaU (σ : R) :
    suyamaV σ - suyamaU σ = -(σ - 5) * (σ + 1) := by
  unfold suyamaU suyamaV
  ring

/-- The first linear factorization used in the numerator of `A - 2`. -/
theorem suyamaV_add_suyamaU (σ : R) :
    suyamaV σ + suyamaU σ = (σ + 5) * (σ - 1) := by
  unfold suyamaU suyamaV
  ring

/-- The second linear factorization used in the numerator of `A + 2`. -/
theorem three_mul_suyamaU_add_suyamaV (σ : R) :
    3 * suyamaU σ + suyamaV σ = (3 * σ - 5) * (σ + 3) := by
  unfold suyamaU suyamaV
  ring

/-- The second linear factorization used in the numerator of `A - 2`. -/
theorem suyamaV_sub_three_mul_suyamaU (σ : R) :
    suyamaV σ - 3 * suyamaU σ = -(3 * σ + 5) * (σ - 3) := by
  unfold suyamaU suyamaV
  ring

/-- In characteristic three, the auxiliary polynomial `u = σ² - 5` simplifies to `σ² + 1`. -/
theorem suyamaU_of_char_three [CharP R 3] (σ : R) : suyamaU σ = σ ^ 2 + 1 := by
  unfold suyamaU
  linear_combination -2 * CharP.ofNat_eq_zero R 3

/-- In characteristic three, the auxiliary polynomial `v = 4σ` simplifies to `σ`. -/
theorem suyamaV_of_char_three [CharP R 3] (σ : R) : suyamaV σ = σ := by
  unfold suyamaV
  linear_combination σ * CharP.ofNat_eq_zero R 3

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Suyama's Montgomery parameter `A`, in the `(A + 2)/4` doubling convention. -/
def suyamaA (σ : K) : K :=
  (suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ) /
    (4 * suyamaU σ ^ 3 * suyamaV σ) - 2

/-- Suyama's Montgomery parameter `A` in terms of the auxiliary polynomials `u` and `v`. -/
theorem suyamaA_def (σ : K) :
    suyamaA σ = (suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ) /
      (4 * suyamaU σ ^ 3 * suyamaV σ) - 2 := (rfl)

/-- The Montgomery `x`-coordinate `u³/v³` of Suyama's supplied point. -/
def suyamaX (σ : K) : K := suyamaU σ ^ 3 / suyamaV σ ^ 3

/-- The supplied affine coordinate in terms of the auxiliary polynomials. -/
theorem suyamaX_def (σ : K) : suyamaX σ = suyamaU σ ^ 3 / suyamaV σ ^ 3 := (rfl)

/-- Suyama's parameter `B`, chosen so that `(suyamaX σ, 1)` lies on the Montgomery curve. -/
def suyamaB (σ : K) : K := suyamaX σ ^ 3 + suyamaA σ * suyamaX σ ^ 2 + suyamaX σ

/-- The supplied Montgomery point satisfies the curve equation, even at exceptional parameters. -/
theorem suyamaB_def (σ : K) :
    suyamaB σ = suyamaX σ ^ 3 + suyamaA σ * suyamaX σ ^ 2 + suyamaX σ := (rfl)

/-- At `σ = 0` the denominator of `suyamaA` vanishes, leaving `-2`. -/
@[simp]
theorem suyamaA_zero : suyamaA (0 : K) = -2 := by
  simp [suyamaA_def]

/-- At `σ = 0` the supplied `x`-coordinate vanishes by division by zero. -/
@[simp]
theorem suyamaX_zero : suyamaX (0 : K) = 0 := by
  simp [suyamaX_def]

/-- At `σ = 0` Suyama's parameter `B` vanishes. -/
@[simp]
theorem suyamaB_zero : suyamaB (0 : K) = 0 := by
  simp [suyamaB_def]

/-- Suyama's parameter `A` commutes with field homomorphisms. -/
@[simp]
theorem map_suyamaA {L : Type*} [Field L] (f : K →+* L) (σ : K) :
    f (suyamaA σ) = suyamaA (f σ) := by
  simp [suyamaA_def, map_ofNat]

/-- Suyama's supplied `x`-coordinate commutes with field homomorphisms. -/
@[simp]
theorem map_suyamaX {L : Type*} [Field L] (f : K →+* L) (σ : K) :
    f (suyamaX σ) = suyamaX (f σ) := by
  simp [suyamaX_def, map_ofNat]

/-- Suyama's parameter `B` commutes with field homomorphisms. -/
@[simp]
theorem map_suyamaB {L : Type*} [Field L] (f : K →+* L) (σ : K) :
    f (suyamaB σ) = suyamaB (f σ) := by
  simp [suyamaB_def]

/-- Nonzero `B` forces the supplied `x`-coordinate `u³/v³` to be nonzero. -/
theorem suyamaX_ne_zero {σ : K} (hB : suyamaB σ ≠ 0) : suyamaX σ ≠ 0 := by
  intro hx
  apply hB
  simp [suyamaB_def, hx]

/-- Nonzero `B` forces the denominator auxiliary polynomial `v` to be nonzero. -/
theorem suyamaV_ne_zero {σ : K} (hB : suyamaB σ ≠ 0) : suyamaV σ ≠ 0 := by
  intro hv
  apply suyamaX_ne_zero hB
  rw [suyamaX_def, hv]
  simp

/-- Suyama's supplied `x`-coordinate is nonzero precisely under the standing denominator
restrictions `(2 : K) ≠ 0`, `σ ≠ 0` and `σ² ≠ 5`. -/
theorem suyamaX_ne_zero_iff {σ : K} :
    suyamaX σ ≠ 0 ↔ (2 : K) ≠ 0 ∧ σ ≠ 0 ∧ σ ^ 2 ≠ 5 := by
  have h₄ : (4 : K) = 2 * 2 := by norm_num
  simp [suyamaX_def, h₄, sub_eq_zero, and_rotate]

/-- The denominator in Suyama's formula is nonzero under the standing parameter restrictions. -/
theorem suyama_denominator_ne_zero {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0)
    (hu : σ ^ 2 ≠ 5) : 4 * suyamaU σ ^ 3 * suyamaV σ ≠ 0 := by
  have h₄ : (4 : K) ≠ 0 := by
    have h := mul_ne_zero h₂ h₂
    norm_num1 at h
    exact h
  exact mul_ne_zero (mul_ne_zero h₄ (pow_ne_zero 3 (sub_ne_zero.mpr hu)))
    (mul_ne_zero h₄ hσ)

/-- The factored formula for `A + 2`. -/
theorem suyamaA_add_two (σ : K) :
    suyamaA σ + 2 = (suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ) /
      (4 * suyamaU σ ^ 3 * suyamaV σ) := by
  simp [suyamaA_def]

/-- The factored formula for `A - 2`. In characteristic two both sides vanish without
requiring `(2 : K) ≠ 0`. -/
theorem suyamaA_sub_two {σ : K} (hσ : σ ≠ 0) (hu : σ ^ 2 ≠ 5) :
    suyamaA σ - 2 = (suyamaV σ + suyamaU σ) ^ 3 * (suyamaV σ - 3 * suyamaU σ) /
      (4 * suyamaU σ ^ 3 * suyamaV σ) := by
  by_cases h₂ : (2 : K) = 0
  · have h₄ : (4 : K) = 0 := by linear_combination 2 * h₂
    simp [suyamaA_def, h₂, h₄]
  · have hd := suyama_denominator_ne_zero h₂ hσ hu
    apply (eq_div_iff hd).mpr
    simp only [suyamaA_def, sub_mul, div_mul_cancel₀ _ hd]
    ring

/-- The polynomial numerator and denominator give valid scaled doubling constants. In
characteristic two both sides vanish without requiring `(2 : K) ≠ 0`. -/
theorem suyama_doubling_relation {σ : K} (hσ : σ ≠ 0) (hu : σ ^ 2 ≠ 5) :
    4 * ((suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ)) =
      (suyamaA σ + 2) * (16 * suyamaU σ ^ 3 * suyamaV σ) := by
  by_cases h₂ : (2 : K) = 0
  · have h₄ : (4 : K) = 0 := by linear_combination 2 * h₂
    have h₁₆ : (16 : K) = 0 := by linear_combination 8 * h₂
    simp [h₄, h₁₆]
  · have hd := suyama_denominator_ne_zero h₂ hσ hu
    have hD : 16 * suyamaU σ ^ 3 * suyamaV σ = (4 * suyamaU σ ^ 3 * suyamaV σ) * 4 := by ring
    rw [suyamaA_add_two, hD]
    simp only [← mul_assoc, div_mul_cancel₀ _ hd]
    ring

/-- **Unconditional factorization of `suyamaB`.** At the degenerate parameters where `2 = 0`,
`σ = 0` or `σ² = 5`, both sides vanish through division by zero. -/
theorem suyamaB_eq (σ : K) :
    suyamaB σ = suyamaU σ * (σ ^ 2 - 1) ^ 2 * (σ ^ 2 - 25) ^ 2 * (σ ^ 4 - 25) ^ 2 /
      suyamaV σ ^ 9 := by
  by_cases h₂ : (2 : K) = 0
  · have h₄ : (4 : K) = 0 := by linear_combination 2 * h₂
    simp [suyamaB_def, suyamaX_def, h₄]
  by_cases hσ : σ = 0
  · simp [hσ]
  by_cases hu : σ ^ 2 = 5
  · simp [suyamaB_def, suyamaX_def, sub_eq_zero.mpr hu]
  have hd := suyama_denominator_ne_zero h₂ hσ hu
  have hv : suyamaV σ ≠ 0 := (mul_ne_zero_iff.mp hd).2
  have hu' : suyamaU σ ≠ 0 := sub_ne_zero.mpr hu
  have h₄ : (4 : K) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).1
  unfold suyamaB suyamaX suyamaA
  field_simp
  unfold suyamaU suyamaV
  ring

/-- **Exact nonvanishing criterion for `suyamaB`.** The factor `σ⁴ - 25 = (σ² - 5)(σ² + 5)`
absorbs the numerator condition `u ≠ 0`. -/
theorem suyamaB_ne_zero_iff {σ : K} :
    suyamaB σ ≠ 0 ↔
      (2 : K) ≠ 0 ∧ σ ≠ 0 ∧ (σ ^ 2 - 1) * (σ ^ 2 - 25) * (σ ^ 4 - 25) ≠ 0 := by
  have h₄ : (4 : K) = 2 * 2 := by norm_num
  have hf : σ ^ 4 - 25 = suyamaU σ * (σ ^ 2 + 5) := by unfold suyamaU; ring
  rw [suyamaB_eq, div_ne_zero_iff, suyamaV_def, h₄, hf]
  simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    pow_eq_zero_iff (by decide : 9 ≠ 0)]
  tauto

/-- **Unconditional factorization of `suyamaA² - 4`**, without excluding characteristic two,
characteristic three, `σ = 0` or `σ² = 5`. -/
theorem suyamaA_sq_sub_four (σ : K) :
    suyamaA σ ^ 2 - 4 =
      (σ ^ 2 - 1) ^ 3 * (σ ^ 2 - 25) ^ 3 * (9 * σ ^ 2 - 25) * (σ ^ 2 - 9) /
        (16 * suyamaU σ ^ 6 * suyamaV σ ^ 2) := by
  by_cases hd : 4 * suyamaU σ ^ 3 * suyamaV σ = 0
  · have hd₂ : 16 * suyamaU σ ^ 6 * suyamaV σ ^ 2 = (4 * suyamaU σ ^ 3 * suyamaV σ) ^ 2 := by
      ring
    rw [suyamaA_def, hd₂, hd]
    norm_num
  · have hσ : σ ≠ 0 := fun h₀ ↦ hd (by simp [h₀])
    have hu : σ ^ 2 ≠ 5 := fun h₅ ↦ hd (by simp [sub_eq_zero.mpr h₅])
    have hf : suyamaA σ ^ 2 - 4 = (suyamaA σ + 2) * (suyamaA σ - 2) := by ring
    rw [hf, suyamaA_add_two, suyamaA_sub_two hσ hu, div_mul_div_comm]
    congr 1 <;> unfold suyamaU suyamaV <;> ring

/-- **Exact nonvanishing criterion for `suyamaA² - 4`.** -/
theorem suyamaA_sq_ne_four_iff {σ : K} :
    suyamaA σ ^ 2 ≠ 4 ↔
      (2 : K) ≠ 0 ∧ σ ≠ 0 ∧ σ ^ 2 ≠ 5 ∧
        (σ ^ 2 - 1) * (σ ^ 2 - 9) * (σ ^ 2 - 25) * (9 * σ ^ 2 - 25) ≠ 0 := by
  have h₁₆ : (16 : K) = (2 * 2) * (2 * 2) := by norm_num
  have h₄ : (4 : K) = 2 * 2 := by norm_num
  rw [← sub_ne_zero, suyamaA_sq_sub_four, div_ne_zero_iff, suyamaU_def, suyamaV_def, h₁₆, h₄]
  simp only [ne_eq, mul_eq_zero, sub_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    pow_eq_zero_iff (by decide : 3 ≠ 0), pow_eq_zero_iff (by decide : 6 ≠ 0)]
  tauto

/-- **Suyama's unconditional ellipticity criterion.** Over any field and for any parameter `σ`,
the monic Montgomery model `model (suyamaA σ) (suyamaB σ)` is elliptic precisely when `2 ≠ 0`,
`σ ≠ 0` and all five polynomial factors (with `σ⁴ - 25 = (σ² - 5)(σ² + 5)`) are nonzero. -/
theorem isElliptic_model_suyama_iff_ne_zero {σ : K} :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔
      (2 : K) ≠ 0 ∧ σ ≠ 0 ∧
        (σ ^ 2 - 1) * (σ ^ 2 - 9) * (σ ^ 2 - 25) * (9 * σ ^ 2 - 25) * (σ ^ 4 - 25) ≠ 0 := by
  have hf : σ ^ 4 - 25 = (σ ^ 2 - 5) * (σ ^ 2 + 5) := by ring
  rw [isElliptic_model_iff_ne_zero, suyamaB_ne_zero_iff, suyamaA_sq_ne_four_iff, hf]
  simp only [ne_eq, mul_eq_zero, sub_eq_zero]
  tauto

/-- **Suyama's exact ellipticity criterion.** Under the denominator restrictions, precisely
these five factors detect singular models. No odd characteristic is excluded. -/
theorem isElliptic_model_suyama_iff {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0)
    (hu : σ ^ 2 ≠ 5) :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔
      (σ ^ 2 - 1) * (σ ^ 2 - 9) * (σ ^ 2 - 25) * (9 * σ ^ 2 - 25) * (σ ^ 2 + 5) ≠ 0 := by
  have hf : σ ^ 4 - 25 = (σ ^ 2 - 5) * (σ ^ 2 + 5) := by ring
  have hu' : σ ^ 2 - 5 ≠ 0 := sub_ne_zero.mpr hu
  rw [isElliptic_model_suyama_iff_ne_zero, hf]
  simp only [ne_eq, mul_eq_zero, h₂, hσ, hu', not_false_eq_true, false_or, true_and]

/-- In characteristic three, `suyamaB σ` is nonzero precisely when `σ ≠ 0` and `σ⁴ ≠ 1`. -/
theorem suyamaB_ne_zero_iff_of_char_three [CharP K 3] {σ : K} :
    suyamaB σ ≠ 0 ↔ σ ≠ 0 ∧ σ ^ 4 ≠ 1 := by
  have h₃ : (3 : K) = 0 := CharP.ofNat_eq_zero K 3
  have h₂ : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; decide)
  have h₂₅ : σ ^ 2 - 25 = σ ^ 2 - 1 := by linear_combination -8 * h₃
  have h₄ : σ ^ 4 - 25 = σ ^ 4 - 1 := by linear_combination -8 * h₃
  have h₁ : σ ^ 4 - 1 = (σ ^ 2 - 1) * (σ ^ 2 + 1) := by ring
  rw [suyamaB_ne_zero_iff, h₂₅, h₄, ← sub_ne_zero (a := σ ^ 4), h₁]
  simp only [ne_eq, mul_eq_zero, h₂, not_false_eq_true, true_and]
  tauto

/-- In characteristic three, every Suyama model with nonzero `B` is already elliptic: the
factors `σ² - 9` and `9σ² - 25` of `suyamaA² - 4` introduce no extra singular parameters. -/
theorem isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three [CharP K 3] {σ : K} :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔ suyamaB σ ≠ 0 := by
  have h₃ : (3 : K) = 0 := CharP.ofNat_eq_zero K 3
  have h₉ : σ ^ 2 - 9 = σ ^ 2 := by linear_combination -3 * h₃
  have h₉₂₅ : 9 * σ ^ 2 - 25 = -1 := by linear_combination (3 * σ ^ 2 - 8) * h₃
  rw [isElliptic_model_suyama_iff_ne_zero, suyamaB_ne_zero_iff, h₉, h₉₂₅]
  simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), neg_eq_zero, one_ne_zero,
    or_false]
  tauto

/-- **Suyama's ellipticity criterion in characteristic three.** Because `9σ² - 25 = -1` and
`σ² - 9 = σ²`, the five factors collapse to `σ ≠ 0` and `σ⁴ ≠ 1`, with no side condition on `σ`. -/
theorem isElliptic_model_suyama_iff_of_char_three [CharP K 3] {σ : K} :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔ σ ≠ 0 ∧ σ ^ 4 ≠ 1 :=
  isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three.trans suyamaB_ne_zero_iff_of_char_three

/-- When `B` is nonzero, Suyama's supplied point becomes a nonsingular point of the monic
model under `x' = Bx`, `y' = B²`. Nonvanishing of `2` follows automatically from `hB`, and
ellipticity of the model is not required. -/
theorem nonsingular_suyama {σ : K} (hB : suyamaB σ ≠ 0) :
    (model (suyamaA σ) (suyamaB σ)).toAffine.Nonsingular
      (suyamaB σ * suyamaX σ) (suyamaB σ ^ 2) := by
  have h₂ : (2 : K) ≠ 0 := (suyamaB_ne_zero_iff.mp hB).1
  rw [← mul_one (suyamaB σ ^ 2), nonsingular_model_iff hB]
  exact ⟨by simpa using suyamaB_def σ, Or.inr (by simpa using mul_ne_zero h₂ hB)⟩

end Field

end TauCeti.Montgomery
