/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Data.ZMod.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.NumberTheory.NumberField.RingOfIntegers.QuadraticAlgebra

/-!
# Period-algebra presentations of quadratic rings of integers

For any quadratic number field `K` of discriminant `D = NumberField.discr K`, the shifted period
generator `τ_D = √D / 2` (when `D ≡ 0 (mod 4)`) or `τ_D = (3 + √D) / 2` (when `D ≡ 1 (mod 4)`)
satisfies the monic quadratic `X² + periodCoeffB D * X + periodCoeffC D = 0`, where:

* `periodCoeffB D = 0`, `periodCoeffC D = -D / 4` for `D ≡ 0 (mod 4)`;
* `periodCoeffB D = -3`, `periodCoeffC D = (9 - D) / 4` for `D ≡ 1 (mod 4)`.

This yields a `ℤ`-algebra isomorphism
`𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-periodCoeffC D) (-periodCoeffB D)`
(`TauCeti.NumberField.exists_ringOfIntegers_periodAlgEquiv`), together with the exceptional
Gaussian (`D = -4`) and Eisenstein (`D = -3`) parameter values and the `ZMod 3` reductions needed
at ramified level `3`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open Module NumberField Polynomial

namespace TauCeti.NumberField

/-- Linear coefficient `B` of the monic quadratic `X² + B X + C` satisfied by the period
generator `τ_D = √D / 2` (`D ≡ 0 (mod 4)`) or `τ_D = (3 + √D) / 2` (`D ≡ 1 (mod 4)`). -/
def periodCoeffB (D : ℤ) : ℤ := if D % 4 = 0 then 0 else -3

/-- Constant coefficient `C` of the monic quadratic `X² + B X + C` satisfied by `τ_D`. -/
def periodCoeffC (D : ℤ) : ℤ := if D % 4 = 0 then -D / 4 else (9 - D) / 4

/-- Unfolding lemma for `periodCoeffB`. -/
theorem periodCoeffB_def (D : ℤ) : periodCoeffB D = if D % 4 = 0 then 0 else -3 := (rfl)

/-- Unfolding lemma for `periodCoeffC`. -/
theorem periodCoeffC_def (D : ℤ) : periodCoeffC D = if D % 4 = 0 then -D / 4 else (9 - D) / 4 :=
  (rfl)

/-- For `D ≡ 0, 1 (mod 4)`, the quadratic algebra `QuadraticAlgebra ℤ (-periodCoeffC D)
(-periodCoeffB D)` has discriminant `D`. -/
theorem discr_neg_periodCoeff (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    QuadraticAlgebra.discr (-periodCoeffC D) (-periodCoeffB D) = D := by
  rw [QuadraticAlgebra.discr_def, periodCoeffB_def, periodCoeffC_def]
  rcases hD with h0 | h1 <;> split_ifs <;> norm_num <;> omega

/-- Value of `-periodCoeffC (-4)` (the Gaussian discriminant). -/
@[simp]
theorem neg_periodCoeffC_neg_four : -periodCoeffC (-4) = -1 := by decide

/-- Value of `-periodCoeffB (-4)` (the Gaussian discriminant). -/
@[simp]
theorem neg_periodCoeffB_neg_four : -periodCoeffB (-4) = 0 := by decide

/-- Value of `-periodCoeffC (-3)` (the Eisenstein discriminant). -/
@[simp]
theorem neg_periodCoeffC_neg_three : -periodCoeffC (-3) = -3 := by decide

/-- Value of `-periodCoeffB (-3)` (the Eisenstein discriminant). -/
@[simp]
theorem neg_periodCoeffB_neg_three : -periodCoeffB (-3) = 3 := by decide

/-- For every integer `D`, `-periodCoeffB D` vanishes in `ZMod 3` (since
`periodCoeffB D ∈ {0, -3}`). -/
theorem intCast_neg_periodCoeffB_zmod_three_eq_zero (D : ℤ) :
    ((-periodCoeffB D : ℤ) : ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, periodCoeffB_def]
  split_ifs <;> decide

/-- For `D ≡ 0, 1 (mod 4)` divisible by `3`, `-periodCoeffC D` vanishes in `ZMod 3`. -/
theorem intCast_neg_periodCoeffC_zmod_three_eq_zero_of_three_dvd {D : ℤ}
    (hD : D % 4 = 0 ∨ D % 4 = 1) (h3 : (3 : ℤ) ∣ D) :
    ((-periodCoeffC D : ℤ) : ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, periodCoeffC_def]
  rcases hD with h0 | h1 <;> split_ifs <;> omega

/-- **Period-algebra presentation of `𝓞 K`**: for any quadratic number field `K` of discriminant
`D = discr K`, `𝓞 K` admits a `ℤ`-algebra isomorphism onto the period algebra
`QuadraticAlgebra ℤ (-periodCoeffC D) (-periodCoeffB D)`. -/
theorem exists_ringOfIntegers_periodAlgEquiv {K : Type*} [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) :
    Nonempty (𝓞 K ≃ₐ[ℤ]
      QuadraticAlgebra ℤ (-periodCoeffC (discr K)) (-periodCoeffB (discr K))) := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  by_cases hd4 : d % 4 = 1
  · set ω₀ := halfGen hmin hd4
    have hdisc : discr K = d := discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4
    have hD4 : discr K % 4 = 0 ∨ discr K % 4 = 1 := Or.inr (hdisc.symm ▸ hd4)
    have hω_sq : ω₀ * ω₀ = ((d - 1) / 4) • (1 : 𝓞 K) + (1 : ℤ) • ω₀ := by
      have haeval := minpoly.aeval ℤ ω₀
      rw [minpoly_halfGen hmin hd4, show (1 - d) / 4 = -((d - 1) / 4) by omega] at haeval
      simp only [map_add, map_sub, map_pow, map_neg, map_intCast, aeval_X, zsmul_eq_mul,
        eq_intCast, Int.cast_one, one_mul] at haeval ⊢
      linear_combination haeval
    have hω_notMem : (ω₀ : K) ∉ (algebraMap ℚ K).range := fun ⟨q, hq⟩ ↦
      gen_notMem_range hmin ⟨2 * q - 1, by
        rw [coe_halfGen] at hq; rw [map_sub, map_mul, map_one, map_ofNat, hq]; ring⟩
    let e₁ := ringOfIntegersAlgEquivOfAdjoin hω_sq
      (adjoin_halfGen_eq_top_of_mod_four_eq_one hmin hgen hsf hd4) hω_notMem
    obtain ⟨e₂⟩ := (QuadraticAlgebra.nonempty_algEquiv_int_iff (a := (d - 1) / 4) (b := 1)
      (a' := -periodCoeffC (discr K)) (b' := -periodCoeffB (discr K))).mpr <| by
        rw [discr_neg_periodCoeff (discr K) hD4, hdisc, QuadraticAlgebra.discr_def]; omega
    exact ⟨e₁.trans e₂⟩
  · have hdisc : discr K = 4 * d := discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4
    have hD4 : discr K % 4 = 0 ∨ discr K % 4 = 1 := Or.inl (by rw [hdisc]; omega)
    have hθ_sq : θ * θ = d • (1 : 𝓞 K) + (0 : ℤ) • θ := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      simpa [sq, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap] using coe_gen_sq hmin
    let e₁ := ringOfIntegersAlgEquivOfAdjoin hθ_sq
      (adjoin_gen_eq_top_of_mod_four_ne_one hmin hgen hsf hd4) (gen_notMem_range hmin)
    obtain ⟨e₂⟩ := (QuadraticAlgebra.nonempty_algEquiv_int_iff (a := d) (b := 0)
      (a' := -periodCoeffC (discr K)) (b' := -periodCoeffB (discr K))).mpr <| by
        rw [discr_neg_periodCoeff (discr K) hD4, hdisc, QuadraticAlgebra.discr_def]; ring
    exact ⟨e₁.trans e₂⟩

end TauCeti.NumberField
