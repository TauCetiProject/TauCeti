/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.ModularForms.DedekindEta.ScaledKronecker
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Product

/-!
# The theta multiplier on `Γ₀(4)`

For `θ(z) = jacobiTheta (2 * z)` on the upper half-plane `ℍ` and `γ = (a b; c d) ∈ Γ₀(4)`,
this file defines Shimura's phase `thetaEpsilon d` (`ε_d = 1` for `d ≡ 1 (mod 4)`, `i`
for `d ≡ 3 (mod 4)`, and `0` for even `d`), defines the theta automorphy factor
`thetaAutomorphy γ z = θ(γ • z) / θ(z)`, and proves its explicit formula and square law:
* `thetaAutomorphy γ z = (thetaEpsilon d)⁻¹ * (c / d) * √(c z + d)` for every
  `γ ∈ Γ₀(4)` (with the principal square root and `TauCeti.kroneckerSym`);
* `thetaAutomorphy γ z ^ 2 = χ₄(d) * (c z + d)` for every `γ ∈ Γ₀(4)`.

The proof writes `θ(z) = η(2z)⁵ / (η(z)² η(4z)²)`
(`TauCeti.jacobiTheta_two_mul_eq_eta_div`) as a level-four eta quotient
(`TauCeti.ModularForm.etaQuotient`), applies its transformation law
`TauCeti.ModularForm.etaQuotient_smul`, and evaluates the three conjugate eta multipliers via the
Kronecker-symbol form `TauCeti.ModularForm.etaMultiplier_conjScaleGamma0_of_c_nonneg_of_odd_d`.
Passing from `γ` to `-γ` extends the formula from `c ≥ 0` to negative `c`.

## Main definitions

* `TauCeti.thetaEpsilon`: the phase `ε_d` (`1` for `d ≡ 1 (mod 4)`, `i` for
  `d ≡ 3 (mod 4)`, and `0` for even `d`).
* `TauCeti.thetaAutomorphy`: the ratio `jacobiTheta (2 * (γ • z)) / jacobiTheta (2 * z)`.
* `TauCeti.thetaEtaExp`: the level-4 eta-quotient exponent vector for `jacobiTheta (2 * z)`.

## Main results

* `TauCeti.thetaEpsilon_sq`, `TauCeti.inv_thetaEpsilon_sq`:
  `ε_d² = ε_d⁻² = χ₄(d)`.
* `TauCeti.thetaAutomorphy_ne_zero`:
  `thetaAutomorphy γ z ≠ 0` for all `γ : SL(2, ℤ)` and `z : ℍ`.
* `TauCeti.sum_thetaEtaExp`, `TauCeti.jacobiTheta_two_mul_eq_etaQuotient`:
  identification of `jacobiTheta (2 * τ)` with `ModularForm.etaQuotient 4 thetaEtaExp τ` of
  exponent sum `1` over the divisors of `4` (weight `1 / 2`).
* `TauCeti.thetaAutomorphy_eq_of_mem_Gamma0`: Shimura's formula for `j(γ, z)` on `Γ₀(4)`.
* `TauCeti.thetaAutomorphy_sq_of_mem_Gamma0`: the square law `j(γ, z)² = χ₄(d) (c z + d)`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. **97** (1973),
  (1.9)–(1.11).
* H. Iwaniec, *Fourier coefficients of modular forms of half-integral weight*, Invent. Math. **87**
  (1987), §2, pp. 387–389.
-/

public section

open Complex CongruenceSubgroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace TauCeti

/-! ### Shimura's phase `ε_d` -/

/-- **Shimura's theta multiplier phase** `ε_d`: `1` when `d ≡ 1 (mod 4)`, `i` when
`d ≡ 3 (mod 4)`, and `0` when `d` is even. -/
noncomputable def thetaEpsilon (d : ℤ) : ℂ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0

/-- The defining formula of `TauCeti.thetaEpsilon`. -/
theorem thetaEpsilon_def (d : ℤ) :
    thetaEpsilon d = if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0 :=
  (rfl)

/-- `ε_d = 1` when `d ≡ 1 (mod 4)`. -/
theorem thetaEpsilon_of_emod_eq_one {d : ℤ} (hd : d % 4 = 1) :
    thetaEpsilon d = 1 := by
  simp [thetaEpsilon_def, hd]

/-- `ε_d = i` when `d ≡ 3 (mod 4)`. -/
theorem thetaEpsilon_of_emod_eq_three {d : ℤ} (hd : d % 4 = 3) :
    thetaEpsilon d = I := by
  simp [thetaEpsilon_def, hd]

/-- `ε_d = 0` when `d` is even. -/
theorem thetaEpsilon_eq_zero_of_even {d : ℤ} (hd : Even d) :
    thetaEpsilon d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [thetaEpsilon_def]
  have h1 : (k + k) % 4 ≠ 1 := by omega
  have h3 : (k + k) % 4 ≠ 3 := by omega
  simp [h1, h3]

/-- `ε_0 = 0`. -/
@[simp]
theorem thetaEpsilon_zero : thetaEpsilon 0 = 0 :=
  thetaEpsilon_eq_zero_of_even Even.zero

/-- `ε_1 = 1`. -/
@[simp]
theorem thetaEpsilon_one : thetaEpsilon 1 = 1 :=
  thetaEpsilon_of_emod_eq_one (by norm_num)

/-- `ε_{-1} = i`. -/
@[simp]
theorem thetaEpsilon_neg_one : thetaEpsilon (-1) = I :=
  thetaEpsilon_of_emod_eq_three (by norm_num)

/-- `thetaEpsilon` depends only on `d` modulo `4`. -/
theorem thetaEpsilon_congr {d d' : ℤ} (h : d ≡ d' [ZMOD 4]) :
    thetaEpsilon d = thetaEpsilon d' := by
  simp only [thetaEpsilon_def, h.eq]

/-- `ε_d` vanishes exactly when `d` is even. -/
@[simp]
theorem thetaEpsilon_eq_zero_iff {d : ℤ} :
    thetaEpsilon d = 0 ↔ Even d := by
  refine ⟨fun h ↦ ?_, thetaEpsilon_eq_zero_of_even⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  have hmod := Int.odd_iff.mp hodd
  rw [thetaEpsilon_def] at h
  split_ifs at h with h₁ h₃
  · exact one_ne_zero h
  · exact I_ne_zero h
  · omega

/-- `ε_d ≠ 0` exactly when `d` is odd. -/
theorem thetaEpsilon_ne_zero_iff {d : ℤ} :
    thetaEpsilon d ≠ 0 ↔ Odd d := by
  simp [ne_eq, ← Int.not_even_iff_odd]

/-- For odd `d`, `ε_d ≠ 0`. -/
theorem thetaEpsilon_ne_zero {d : ℤ} (hd : Odd d) :
    thetaEpsilon d ≠ 0 :=
  thetaEpsilon_ne_zero_iff.mpr hd

/-- For every integer `d`, `ε_d² = χ₄(d)`. -/
theorem thetaEpsilon_sq (d : ℤ) :
    thetaEpsilon d ^ 2 = (ZMod.χ₄ (d : ZMod 4) : ℂ) := by
  rw [thetaEpsilon_def, ZMod.χ₄_int_eq_if_mod_four]
  have hd : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
  rcases hd with h | h | h | h
  · have h2 : d % 2 = 0 := by omega
    have h1 : d % 4 ≠ 1 := by omega
    have h3 : d % 4 ≠ 3 := by omega
    simp [h2, h1, h3]
  · have h2 : d % 2 ≠ 0 := by omega
    simp [h2, h]
  · have h2 : d % 2 = 0 := by omega
    have h1 : d % 4 ≠ 1 := by omega
    have h3 : d % 4 ≠ 3 := by omega
    simp [h2, h1, h3]
  · have h2 : d % 2 ≠ 0 := by omega
    simp [h2, h]

/-- For odd `d`, `‖ε_d‖ = 1`. -/
@[simp]
theorem norm_thetaEpsilon {d : ℤ} (hd : Odd d) : ‖thetaEpsilon d‖ = 1 := by
  have hmod := Int.odd_iff.mp hd
  rw [thetaEpsilon_def]
  split_ifs with h₁ h₃
  · simp
  · simp
  · omega

/-- For odd `d`, `ε_d⁻¹` is `1` when `d ≡ 1 (mod 4)` and `-i` when `d ≡ 3 (mod 4)`. -/
theorem inv_thetaEpsilon {d : ℤ} (hd : Odd d) :
    (thetaEpsilon d)⁻¹ = if d % 4 = 1 then 1 else -I := by
  have hmod := Int.odd_iff.mp hd
  rw [thetaEpsilon_def]
  split_ifs with h₁ h₃ <;> simp [inv_I]
  omega

/-- For every integer `d`, `(ε_d⁻¹)² = χ₄(d)`. -/
theorem inv_thetaEpsilon_sq (d : ℤ) :
    (thetaEpsilon d)⁻¹ ^ 2 = (ZMod.χ₄ (d : ZMod 4) : ℂ) := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaEpsilon_eq_zero_of_even hd, inv_zero, zero_pow two_ne_zero,
      ZMod.χ₄_int_eq_if_mod_four]
    simp [Int.dvd_iff_emod_eq_zero.mp (even_iff_two_dvd.mp hd)]
  · rw [inv_pow, thetaEpsilon_sq]
    have hsq : (ZMod.χ₄ (d : ZMod 4) : ℂ) ^ 2 = 1 := by
      rw [← kroneckerSym_neg_one_left_of_odd hd, sq_intCast_kroneckerSym_eq_one (by simp)]
    exact inv_eq_of_mul_eq_one_right (by simpa [sq] using hsq)

/-- For every integer `d`, `ε_{-d} = i ε_d⁻¹`. -/
theorem thetaEpsilon_neg (d : ℤ) :
    thetaEpsilon (-d) = I * (thetaEpsilon d)⁻¹ := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaEpsilon_eq_zero_of_even hd.neg, thetaEpsilon_eq_zero_of_even hd,
      inv_zero, mul_zero]
  · have hmod := Int.odd_iff.mp hd
    rw [inv_thetaEpsilon hd, thetaEpsilon_def]
    split_ifs with h₁ h₃ h₄ <;> simp <;> omega

/-- For odd `d`, `ε_d ε_{-d} = i`. -/
theorem thetaEpsilon_mul_neg {d : ℤ} (hd : Odd d) :
    thetaEpsilon d * thetaEpsilon (-d) = I := by
  rw [thetaEpsilon_neg, ← mul_assoc, mul_comm (thetaEpsilon d) I, mul_assoc,
    mul_inv_cancel₀ (thetaEpsilon_ne_zero hd), mul_one]

/-- For every integer `d`, `(ε_{-d})⁻¹ = -i (-1 / d) ε_d⁻¹`. -/
theorem inv_thetaEpsilon_neg (d : ℤ) :
    (thetaEpsilon (-d))⁻¹ =
      -I * (kroneckerSym (-1) d : ℂ) * (thetaEpsilon d)⁻¹ := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaEpsilon_eq_zero_of_even hd.neg, thetaEpsilon_eq_zero_of_even hd,
      inv_zero, mul_zero]
  · rw [thetaEpsilon_neg, mul_inv, inv_I, inv_inv, kroneckerSym_neg_one_left_of_odd hd,
      mul_assoc]
    congr 1
    exact (eq_mul_inv_iff_mul_eq₀ (thetaEpsilon_ne_zero hd)).mpr
      (by rw [← sq, thetaEpsilon_sq])

/-! ### The theta automorphy factor on `Γ₀(4)` -/

/-- **The theta automorphy factor** `j(γ, z) = θ(γ • z) / θ(z)` on `ℍ`, where
`θ(z) = jacobiTheta (2 * z)`. -/
noncomputable def thetaAutomorphy (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ))

/-- The defining ratio of `TauCeti.thetaAutomorphy`. -/
theorem thetaAutomorphy_def (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphy γ z =
      jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ)) :=
  (rfl)

/-- `thetaAutomorphy γ z ≠ 0` for every `γ ∈ SL(2, ℤ)` and `z ∈ ℍ`. -/
@[simp]
theorem thetaAutomorphy_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : thetaAutomorphy γ z ≠ 0 := by
  rw [thetaAutomorphy_def]
  exact div_ne_zero (jacobiTheta_two_mul_ne_zero (γ • z)) (jacobiTheta_two_mul_ne_zero z)

/-- At the identity matrix, `j(1, z) = 1`. -/
@[simp]
theorem thetaAutomorphy_one (z : ℍ) : thetaAutomorphy 1 z = 1 := by
  rw [thetaAutomorphy_def, one_smul]
  exact div_self (jacobiTheta_two_mul_ne_zero z)

/-- Negating the matrix does not change the theta automorphy factor: `j(-γ, z) = j(γ, z)`. -/
@[simp]
theorem thetaAutomorphy_neg (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphy (-γ) z = thetaAutomorphy γ z := by
  rw [thetaAutomorphy_def, ModularGroup.SL_neg_smul, ← thetaAutomorphy_def]

/-- The cocycle law for the theta automorphy factor:
`j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)`. -/
theorem thetaAutomorphy_mul (γ₁ γ₂ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphy (γ₁ * γ₂) z =
      thetaAutomorphy γ₁ (γ₂ • z) * thetaAutomorphy γ₂ z := by
  simp only [thetaAutomorphy_def, mul_smul]
  rw [div_mul_div_cancel₀ (jacobiTheta_two_mul_ne_zero (γ₂ • z))]

/-- Inversion law for the theta automorphy factor:
`j(γ⁻¹, γ • z) = j(γ, z)⁻¹`. -/
theorem thetaAutomorphy_inv_smul (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphy γ⁻¹ (γ • z) = (thetaAutomorphy γ z)⁻¹ := by
  rw [thetaAutomorphy_def, thetaAutomorphy_def, inv_smul_smul, inv_div]

/-- The level-4 eta-quotient exponent vector for
`θ(z) = jacobiTheta (2 * z) = η(2z)⁵ / (η(z)² η(4z)²)`: it sends `2` to `5` and every other
natural number (in particular `1` and `4`) to `-2`. -/
def thetaEtaExp : ℕ → ℤ := fun δ ↦ if δ = 2 then 5 else -2

/-- Value of `TauCeti.thetaEtaExp` at every natural index `δ : ℕ`: `5` at `δ = 2` and `-2` at
every `δ ≠ 2`. -/
theorem thetaEtaExp_def (δ : ℕ) :
    thetaEtaExp δ = if δ = 2 then 5 else -2 :=
  (rfl)

/-- `thetaEtaExp 1 = -2`. -/
@[simp]
theorem thetaEtaExp_one : thetaEtaExp 1 = -2 := by
  decide

/-- `thetaEtaExp 2 = 5`. -/
@[simp]
theorem thetaEtaExp_two : thetaEtaExp 2 = 5 := by
  decide

/-- `thetaEtaExp 4 = -2`. -/
@[simp]
theorem thetaEtaExp_four : thetaEtaExp 4 = -2 := by
  decide

/-- The values of `thetaEtaExp` over the divisors of `4` sum to `1`, corresponding to weight
`1 / 2`. -/
theorem sum_thetaEtaExp : ∑ δ ∈ (4 : ℕ).divisors, thetaEtaExp δ = 1 := by
  decide

/-- Expanding a `thetaEtaExp`-weighted product over the divisors of `4`. -/
theorem prod_zpow_thetaEtaExp {G : Type*} [DivisionCommMonoid G] (f : ℕ → G) :
    ∏ δ ∈ (4 : ℕ).divisors, f δ ^ thetaEtaExp δ = f 2 ^ 5 / (f 1 ^ 2 * f 4 ^ 2) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, Nat.prod_divisors_prime_pow Nat.prime_two,
    Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
  simp only [pow_zero, pow_one, Nat.reducePow, thetaEtaExp_one, thetaEtaExp_two, thetaEtaExp_four,
    zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_inv]
  ac_rfl

/-- Expanding a `thetaEtaExp`-weighted sum over the divisors of `4`. -/
theorem sum_thetaEtaExp_mul (f : ℕ → ℤ) :
    ∑ δ ∈ (4 : ℕ).divisors, thetaEtaExp δ * f δ = 5 * f 2 - 2 * f 1 - 2 * f 4 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, Nat.sum_divisors_prime_pow Nat.prime_two,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, pow_one, Nat.reducePow, thetaEtaExp_one, thetaEtaExp_two, thetaEtaExp_four]
  ring

/-- For `τ` in the upper half-plane, `jacobiTheta (2 * τ)` equals the level-4 eta quotient
`ModularForm.etaQuotient 4 thetaEtaExp τ`. -/
theorem jacobiTheta_two_mul_eq_etaQuotient {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = ModularForm.etaQuotient 4 thetaEtaExp τ := by
  rw [jacobiTheta_two_mul_eq_eta_div hτ, ModularForm.etaQuotient_apply, prod_zpow_thetaEtaExp]
  simp

private theorem kroneckerSym_two_mul_e24 {d : ℤ} (hd : Odd d) :
    (kroneckerSym 2 d : ℂ) * ModularForm.e24 (3 * d - 3) = (thetaEpsilon d)⁻¹ := by
  rw [kroneckerSym_two_left d, ZMod.χ₈_int_eq_if_mod_eight, inv_thetaEpsilon hd]
  have h2 : d % 2 ≠ 0 := by
    obtain ⟨k, rfl⟩ := hd
    omega
  have hmod : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by
    obtain ⟨k, rfl⟩ := hd
    omega
  rcases hmod with h | h | h | h
  · have he : 3 * d - 3 ≡ 0 [ZMOD 24] := by rw [Int.ModEq]; omega
    have h4 : d % 4 = 1 := by omega
    rw [ModularForm.e24_congr he, ModularForm.e24_zero]
    simp [h2, h, h4]
  · have he : 3 * d - 3 ≡ 6 [ZMOD 24] := by rw [Int.ModEq]; omega
    have h8 : d % 8 ≠ 1 ∧ d % 8 ≠ 7 := by omega
    have h4 : d % 4 ≠ 1 := by omega
    rw [ModularForm.e24_congr he, ModularForm.e24_six]
    simp [h2, h8, h4]
  · have he : 3 * d - 3 ≡ 12 * (1 : ℕ) [ZMOD 24] := by rw [Int.ModEq]; omega
    have h8 : d % 8 ≠ 1 ∧ d % 8 ≠ 7 := by omega
    have h4 : d % 4 = 1 := by omega
    rw [ModularForm.e24_congr he, ModularForm.e24_twelve_mul]
    simp [h2, h8, h4]
  · have he : 3 * d - 3 ≡ 12 * (1 : ℕ) + 6 [ZMOD 24] := by rw [Int.ModEq]; omega
    have h4 : d % 4 ≠ 1 := by omega
    rw [ModularForm.e24_congr he, ModularForm.e24_add, ModularForm.e24_twelve_mul,
      ModularForm.e24_six]
    simp [h2, h, h4]

private theorem prod_kroneckerSym_thetaEtaExp {t d : ℤ} (hcop : IsCoprime (4 * t) d) :
    ∏ δ ∈ (4 : ℕ).divisors, (kroneckerSym ((4 / δ : ℕ) * t) d : ℂ) ^ thetaEtaExp δ =
      kroneckerSym 2 d * kroneckerSym (4 * t) d := by
  rw [prod_zpow_thetaEtaExp]
  simp only [Nat.reduceDiv, Nat.cast_one, Nat.cast_ofNat, one_mul]
  have hcop4 : (4 * t).gcd d = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hcopt : t.gcd d = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_left (dvd_mul_left t 4))
  have hcop2 : (2 * t).gcd d = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_left ⟨2, by ring⟩)
  have hcop2d : (2 : ℤ).gcd d = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_left ⟨2 * t, by ring⟩)
  have h4sq : (kroneckerSym (4 * t) d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one hcop4
  have htsq : (kroneckerSym t d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one hcopt
  have h2pow : (kroneckerSym (2 * t) d : ℂ) ^ 5 = (kroneckerSym (2 * t) d : ℂ) := by
    have hsq : (kroneckerSym (2 * t) d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one hcop2
    calc (kroneckerSym (2 * t) d : ℂ) ^ 5
        = ((kroneckerSym (2 * t) d : ℂ) ^ 2) ^ 2 * (kroneckerSym (2 * t) d : ℂ) := by ring
      _ = (kroneckerSym (2 * t) d : ℂ) := by rw [hsq, one_pow, one_mul]
  simp only [h4sq, htsq, h2pow, one_mul, div_one]
  rcases eq_or_ne d (-1) with rfl | hd1
  · have h4_neg : 4 * t < 0 ↔ 2 * t < 0 := by omega
    simp [kroneckerSym_neg_one_right, h4_neg]
  · have h2t : kroneckerSym (2 * t) d = kroneckerSym 2 d * kroneckerSym t d :=
      kroneckerSym_mul_left_of_ne_neg_one hd1 2 t
    have h4t : kroneckerSym (4 * t) d = kroneckerSym t d := by
      have hsq : 4 * t = t * 2 ^ 2 := by ring
      rw [hsq, kroneckerSym_mul_sq two_ne_zero hcop2d]
    rw [h2t, h4t, Int.cast_mul]

private theorem odd_apply_one_one_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) :
    Odd (γ 1 1) :=
  γ.odd_apply_one_of_even_apply_zero
    (even_iff_two_dvd.mpr (dvd_trans ⟨2, by norm_num⟩ (mem_Gamma0_iff_dvd.mp hγ)))

private theorem etaQuotientMultiplier_thetaEtaExp_of_nonneg {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 4) (hc : 0 ≤ γ 1 0) :
    ModularForm.etaQuotientMultiplier 4 thetaEtaExp ⟨γ, hγ⟩ =
      (thetaEpsilon (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
  have ht' : γ 1 0 = 4 * t := by simpa using ht
  have hdo : Odd (γ 1 1) := odd_apply_one_one_of_mem_Gamma0 hγ
  have hcop : IsCoprime (4 * t) (γ 1 1) := ht' ▸ γ.isCoprime_row 1
  have hE :
      ∑ δ ∈ (4 : ℕ).divisors,
        thetaEtaExp δ * ((γ 0 0 + γ 1 1) * ((4 / δ : ℕ) * t) -
          γ 0 1 * δ * γ 1 1 * (((4 / δ : ℕ) * t) ^ 2 - 1) + 3 * γ 1 1 - 3 -
          3 * ((4 / δ : ℕ) * t) * γ 1 1) =
        3 * γ 1 1 - 3 := by
    rw [sum_thetaEtaExp_mul]
    simp only [Nat.reduceDiv, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [ModularForm.etaQuotientMultiplier_eq_prod thetaEtaExp ⟨γ, hγ⟩ fun δ hδ ↦
      ModularForm.etaMultiplier_conjScaleGamma0_of_c_nonneg_of_odd_d
        (Nat.dvd_of_mem_divisors hδ) hγ ht' hc hdo,
    ModularForm.prod_mul_e24_zpow, hE, prod_kroneckerSym_thetaEtaExp hcop, ← ht',
    mul_right_comm, kroneckerSym_two_mul_e24 hdo]

private theorem thetaAutomorphy_eq_of_mem_Gamma0_of_nonneg {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4)
    (hc : 0 ≤ γ 1 0) (z : ℍ) :
    thetaAutomorphy γ z =
      (thetaEpsilon (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hsmul := ModularForm.etaQuotient_smul 4 thetaEtaExp ⟨γ, hγ⟩ z
  simp only [sum_thetaEtaExp, zpow_one,
    etaQuotientMultiplier_thetaEtaExp_of_nonneg hγ hc] at hsmul
  rw [thetaAutomorphy_def, jacobiTheta_two_mul_eq_etaQuotient (γ • z).im_pos,
    jacobiTheta_two_mul_eq_etaQuotient z.im_pos, hsmul, mul_div_assoc,
    div_self (ModularForm.etaQuotient_ne_zero 4 thetaEtaExp z.im_pos), mul_one]

/-- **Shimura's theta multiplier formula on `Γ₀(4)`** (Shimura (1973), (1.9)–(1.10); Iwaniec
(1987), (2.1)): for every `γ = (a b; c d) ∈ Γ₀(4)` and `z ∈ ℍ`,
`j(γ, z) = θ(γ • z) / θ(z) = ε_d⁻¹ (c / d) √(c z + d)`, with the principal square root
and the Kronecker symbol `TauCeti.kroneckerSym`. Holds for every sign of `c` and `d`. -/
theorem thetaAutomorphy_eq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphy γ z =
      (thetaEpsilon (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rcases le_or_gt 0 (γ 1 0) with hc | hc
  · exact thetaAutomorphy_eq_of_mem_Gamma0_of_nonneg hγ hc z
  · -- For `c < 0`, pass to `-γ ∈ Γ₀(4)`, which acts identically on `ℍ` and has `-c > 0`.
    have hγneg : -γ ∈ Gamma0 4 := mem_Gamma0_iff_dvd.mpr (by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      exact dvd_neg.mpr (mem_Gamma0_iff_dvd.mp hγ))
    have hcneg : 0 ≤ (-γ) 1 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      omega
    have hmain := thetaAutomorphy_eq_of_mem_Gamma0_of_nonneg hγneg hcneg z
    rw [thetaAutomorphy_neg] at hmain
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at hmain
    have hsqrt : Complex.sqrt (-(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ)) =
        I * Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
      have hneg : -(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ) = -((γ 1 0 : ℂ) * z + γ 1 1) := by ring
      rw [hneg]
      exact Complex.sqrt_neg_of_im_neg <| by
        simpa using mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hc) z.im_pos
    have hsym_sq : (kroneckerSym (-1) (γ 1 1) : ℂ) ^ 2 = 1 :=
      sq_intCast_kroneckerSym_eq_one (by simp)
    rw [hmain, inv_thetaEpsilon_neg, kroneckerSym_neg_neg_of_left_neg hc, Int.cast_mul, hsqrt]
    calc -I * (kroneckerSym (-1) (γ 1 1) : ℂ) * (thetaEpsilon (γ 1 1))⁻¹ *
          ((kroneckerSym (-1) (γ 1 1) : ℂ) * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ)) *
          (I * Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1))
        = -(I * I) * (kroneckerSym (-1) (γ 1 1) : ℂ) ^ 2 *
            ((thetaEpsilon (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
              Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1)) := by ring
      _ = (thetaEpsilon (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
            Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
          rw [I_mul_I, neg_neg, hsym_sq, one_mul, one_mul]

/-- Variant of `thetaAutomorphy_eq_of_mem_Gamma0` expressing the transformation directly in terms
of `jacobiTheta (2 * z)`. -/
theorem jacobiTheta_two_mul_smul_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      (thetaEpsilon (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) * jacobiTheta (2 * (z : ℂ)) := by
  have h := thetaAutomorphy_eq_of_mem_Gamma0 hγ z
  rw [thetaAutomorphy_def] at h
  exact (div_eq_iff (jacobiTheta_two_mul_ne_zero z)).mp h

/-- **The theta multiplier square law** on `Γ₀(4)` (Shimura (1973), (1.11)):
`j(γ, z)² = χ₄(d) (c z + d)` for every `γ = (a b; c d) ∈ Γ₀(4)` and `z ∈ ℍ`. -/
theorem thetaAutomorphy_sq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphy γ z ^ 2 =
      (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hsym : (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) ^ 2 = 1 :=
    sq_intCast_kroneckerSym_eq_one (Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_row 1))
  rw [thetaAutomorphy_eq_of_mem_Gamma0 hγ z, mul_pow, mul_pow,
    inv_thetaEpsilon_sq, hsym, mul_one, Complex.sq_sqrt]

/-- The theta multiplier square law written with the Kronecker symbol `(-1 / d)`. -/
theorem thetaAutomorphy_sq_eq_kroneckerSym_mul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphy γ z ^ 2 =
      (kroneckerSym (-1) (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [thetaAutomorphy_sq_of_mem_Gamma0 hγ z,
    ← kroneckerSym_neg_one_left_of_odd (odd_apply_one_one_of_mem_Gamma0 hγ)]

end TauCeti
