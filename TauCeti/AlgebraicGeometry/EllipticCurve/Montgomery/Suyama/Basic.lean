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

The main result `isElliptic_model_suyama_iff` describes the exact exceptional set, over any
field of characteristic different from two, including characteristic three. The only standing
restrictions on the parameter are `σ ≠ 0` and `σ² ≠ 5`, which keep the denominators nonzero.
The factorization of `suyamaB` and of `suyamaA² - 4` explains all five exceptional factors.

In characteristic three, `9σ² - 25 = -1` and `σ² - 9 = σ²` introduce no additional obstructions
beyond those of `suyamaB`: `isElliptic_model_suyama_iff_of_char_three` reduces ellipticity to
`σ ≠ 0 ∧ σ⁴ ≠ 1`, and `isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three` identifies
elliptic Suyama models in characteristic three with those having `suyamaB σ ≠ 0`.

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

/-- The Montgomery `x`-coordinate `u³/v³` of Suyama's supplied point. -/
def suyamaX (σ : K) : K := suyamaU σ ^ 3 / suyamaV σ ^ 3

/-- The supplied affine coordinate in terms of the auxiliary polynomials. -/
theorem suyamaX_def (σ : K) : suyamaX σ = suyamaU σ ^ 3 / suyamaV σ ^ 3 := (rfl)

/-- Suyama's parameter `B`, chosen so that `(suyamaX σ, 1)` lies on the Montgomery curve. -/
def suyamaB (σ : K) : K := suyamaX σ ^ 3 + suyamaA σ * suyamaX σ ^ 2 + suyamaX σ

/-- The supplied Montgomery point satisfies the curve equation, even at exceptional parameters. -/
theorem suyamaB_def (σ : K) :
    suyamaB σ = suyamaX σ ^ 3 + suyamaA σ * suyamaX σ ^ 2 + suyamaX σ := (rfl)

/-- Nonzero `B` forces the denominator auxiliary polynomial `v` to be nonzero. -/
theorem suyamaV_ne_zero {σ : K} (hB : suyamaB σ ≠ 0) : suyamaV σ ≠ 0 := by
  intro hv
  apply hB
  simp only [suyamaB_def, suyamaX_def, hv]
  simp

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
  simp [suyamaA]

/-- The factored formula for `A - 2`. -/
theorem suyamaA_sub_two {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0) (hu : σ ^ 2 ≠ 5) :
    suyamaA σ - 2 = (suyamaV σ + suyamaU σ) ^ 3 * (suyamaV σ - 3 * suyamaU σ) /
      (4 * suyamaU σ ^ 3 * suyamaV σ) := by
  have hd := suyama_denominator_ne_zero h₂ hσ hu
  apply (eq_div_iff hd).mpr
  simp only [suyamaA, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- The polynomial numerator and denominator give valid scaled doubling constants. -/
theorem suyama_doubling_relation {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0)
    (hu : σ ^ 2 ≠ 5) :
    4 * ((suyamaV σ - suyamaU σ) ^ 3 * (3 * suyamaU σ + suyamaV σ)) =
      (suyamaA σ + 2) * (16 * suyamaU σ ^ 3 * suyamaV σ) := by
  have hd := suyama_denominator_ne_zero h₂ hσ hu
  have hD : 16 * suyamaU σ ^ 3 * suyamaV σ = (4 * suyamaU σ ^ 3 * suyamaV σ) * 4 := by ring
  rw [suyamaA_add_two, hD]
  simp only [← mul_assoc, div_mul_cancel₀ _ hd]
  ring

/-- The factorization of `B` isolates the parameters where the supplied model degenerates. -/
theorem suyamaB_eq {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0) (hu : σ ^ 2 ≠ 5) :
    suyamaB σ = suyamaU σ * (σ ^ 2 - 1) ^ 2 * (σ ^ 2 - 25) ^ 2 * (σ ^ 4 - 25) ^ 2 /
      suyamaV σ ^ 9 := by
  have hd := suyama_denominator_ne_zero h₂ hσ hu
  have hv : suyamaV σ ≠ 0 := (mul_ne_zero_iff.mp hd).2
  have hu' : suyamaU σ ≠ 0 := sub_ne_zero.mpr hu
  have h₄ : (4 : K) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).1
  unfold suyamaB suyamaX suyamaA
  field_simp
  unfold suyamaU suyamaV
  ring

/-- The factorization of `A² - 4`, without excluding characteristic three. -/
theorem suyamaA_sq_sub_four {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0) (hu : σ ^ 2 ≠ 5) :
    suyamaA σ ^ 2 - 4 =
      (σ ^ 2 - 1) ^ 3 * (σ ^ 2 - 25) ^ 3 * (9 * σ ^ 2 - 25) * (σ ^ 2 - 9) /
        (16 * suyamaU σ ^ 6 * suyamaV σ ^ 2) := by
  have hf : suyamaA σ ^ 2 - 4 = (suyamaA σ + 2) * (suyamaA σ - 2) := by ring
  rw [hf, suyamaA_add_two, suyamaA_sub_two h₂ hσ hu, div_mul_div_comm]
  congr 1 <;> unfold suyamaU suyamaV <;> ring

/-- **Suyama's exact ellipticity criterion.** Under the denominator restrictions, precisely
these five factors detect singular models. No odd characteristic is excluded. -/
theorem isElliptic_model_suyama_iff {σ : K} (h₂ : (2 : K) ≠ 0) (hσ : σ ≠ 0)
    (hu : σ ^ 2 ≠ 5) :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔
      (σ ^ 2 - 1) * (σ ^ 2 - 9) * (σ ^ 2 - 25) * (9 * σ ^ 2 - 25) * (σ ^ 2 + 5) ≠ 0 := by
  have hd := suyama_denominator_ne_zero h₂ hσ hu
  have hv : suyamaV σ ≠ 0 := (mul_ne_zero_iff.mp hd).2
  have hu' : suyamaU σ ≠ 0 := sub_ne_zero.mpr hu
  have h₄ : (4 : K) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).1
  have h₁₆ : (16 : K) ≠ 0 := by
    have h := mul_ne_zero h₄ h₄
    norm_num1 at h
    exact h
  rw [isElliptic_model_iff_ne_zero, suyamaB_eq h₂ hσ hu]
  have hsq : suyamaA σ ^ 2 ≠ 4 ↔ suyamaA σ ^ 2 - 4 ≠ 0 := sub_ne_zero.symm
  rw [hsq, suyamaA_sq_sub_four h₂ hσ hu]
  have hf : σ ^ 4 - 25 = suyamaU σ * (σ ^ 2 + 5) := by unfold suyamaU; ring
  simp only [hf, ne_eq, div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    pow_eq_zero_iff (by decide : 3 ≠ 0), pow_eq_zero_iff (by decide : 6 ≠ 0),
    pow_eq_zero_iff (by decide : 9 ≠ 0)]
  tauto

/-- In characteristic three, `suyamaB σ` is nonzero precisely when `σ ≠ 0` and `σ⁴ ≠ 1`. -/
theorem suyamaB_ne_zero_iff_of_char_three [CharP K 3] {σ : K} :
    suyamaB σ ≠ 0 ↔ σ ≠ 0 ∧ σ ^ 4 ≠ 1 := by
  have h₃ : (3 : K) = 0 := CharP.ofNat_eq_zero K 3
  have h₂ : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; decide)
  by_cases hσ : σ = 0
  · simp [hσ, suyamaB_def, suyamaX_def]
  by_cases hu : σ ^ 2 = 5
  · have h₄ : σ ^ 4 = 1 := by linear_combination (σ ^ 2 + 5) * hu + 8 * h₃
    simp [suyamaB_def, suyamaX_def, sub_eq_zero.mpr hu, h₄]
  · have h₂₅ : σ ^ 2 - 25 = σ ^ 2 - 1 := by linear_combination -8 * h₃
    have h₄ : σ ^ 4 - 25 = σ ^ 4 - 1 := by linear_combination -8 * h₃
    have h₁ : σ ^ 4 - 1 = (σ ^ 2 - 1) * (σ ^ 2 + 1) := by ring
    rw [suyamaB_eq h₂ hσ hu, suyamaU_of_char_three, suyamaV_of_char_three, div_ne_zero_iff,
      h₂₅, h₄, ← sub_ne_zero (a := σ ^ 4), h₁]
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
      pow_eq_zero_iff (by decide : 9 ≠ 0), hσ, not_false_eq_true, and_true, true_and]
    tauto

/-- In characteristic three, every Suyama model with nonzero `B` is already elliptic: the
factors `σ² - 9` and `9σ² - 25` of `suyamaA² - 4` introduce no extra singular parameters. -/
theorem isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three [CharP K 3] {σ : K} :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔ suyamaB σ ≠ 0 := by
  refine ⟨fun h ↦ (isElliptic_model_iff_ne_zero.mp h).2.1, fun hB ↦ ?_⟩
  have h₃ : (3 : K) = 0 := CharP.ofNat_eq_zero K 3
  have h₂ : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; decide)
  obtain ⟨hσ, h₄⟩ := suyamaB_ne_zero_iff_of_char_three.mp hB
  have hu : σ ^ 2 ≠ 5 := fun h₅ ↦ h₄ (by linear_combination (σ ^ 2 + 5) * h₅ + 8 * h₃)
  have hsq : σ ^ 2 - 1 ≠ 0 := fun h₁ ↦ h₄ (by linear_combination (σ ^ 2 + 1) * h₁)
  have h₉ : σ ^ 2 - 9 = σ ^ 2 := by linear_combination -3 * h₃
  have h₉₂₅ : 9 * σ ^ 2 - 25 = -1 := by linear_combination (3 * σ ^ 2 - 8) * h₃
  have h₂₅ : σ ^ 2 - 25 = σ ^ 2 - 1 := by linear_combination -8 * h₃
  have h₅ : σ ^ 2 + 5 = σ ^ 2 - 1 := by linear_combination 2 * h₃
  rw [isElliptic_model_suyama_iff h₂ hσ hu, h₉, h₉₂₅, h₂₅, h₅]
  simp [hσ, hsq]

/-- **Suyama's ellipticity criterion in characteristic three.** Because `9σ² - 25 = -1` and
`σ² - 9 = σ²`, the five factors collapse to `σ ≠ 0` and `σ⁴ ≠ 1`, with no side condition on `σ`. -/
theorem isElliptic_model_suyama_iff_of_char_three [CharP K 3] {σ : K} :
    (model (suyamaA σ) (suyamaB σ)).IsElliptic ↔ σ ≠ 0 ∧ σ ^ 4 ≠ 1 :=
  isElliptic_model_suyama_iff_suyamaB_ne_zero_of_char_three.trans suyamaB_ne_zero_iff_of_char_three

/-- When `B` is nonzero, Suyama's supplied point becomes a nonsingular point of the monic
model under `x' = Bx`, `y' = B²`. This does not require ellipticity of the model. -/
theorem nonsingular_suyama {σ : K} (h₂ : (2 : K) ≠ 0) (hB : suyamaB σ ≠ 0) :
    (model (suyamaA σ) (suyamaB σ)).toAffine.Nonsingular
      (suyamaB σ * suyamaX σ) (suyamaB σ ^ 2) := by
  rw [← mul_one (suyamaB σ ^ 2), nonsingular_model_iff hB]
  exact ⟨by simpa using suyamaB_def σ, Or.inr (by simpa using mul_ne_zero h₂ hB)⟩

end Field

end TauCeti.Montgomery
