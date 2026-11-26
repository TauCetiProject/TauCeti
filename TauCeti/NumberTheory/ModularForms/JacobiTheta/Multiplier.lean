/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Algebra.Ring.Int.Parity
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Sqrt
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Product

/-!
# The theta multiplier on `Γ₀(4)`

For `θ(z) = jacobiTheta (2 * z)` on the upper half-plane `ℍ` and `γ = (a b; c d) ∈ Γ₀(4)`,
this file defines Shimura's phase `thetaMultiplierPhase d` (`ε_d = 1` for `d ≡ 1 (mod 4)`, `i`
for `d ≡ 3 (mod 4)`, and `0` for even `d`), defines the theta automorphy factor
`thetaAutomorphy γ z = θ(γ • z) / θ(z)`, and proves its explicit formula and square law:
* `thetaAutomorphy γ z = (thetaMultiplierPhase d)⁻¹ * (c / d) * √(c z + d)` for every
  `γ ∈ Γ₀(4)` (with the principal square root and `TauCeti.kroneckerSym`);
* `thetaAutomorphy γ z ^ 2 = χ₋₄(d) * (c z + d)` for every `γ ∈ Γ₀(4)`.

The proof writes `θ(2z) = η(2z)⁵ / (η(z)² η(4z)²)`
(`TauCeti.jacobiTheta_two_mul_eq_eta_div`) as a level-four eta quotient
(`TauCeti.ModularForm.etaQuotient`), applies its transformation law
`TauCeti.ModularForm.etaQuotient_smul`, and evaluates the three conjugate eta multipliers via the
Kronecker-symbol form `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d`.
Passing from `γ` to `-γ` extends the formula from `c ≥ 0` to negative `c`.

## Main definitions

* `TauCeti.thetaMultiplierPhase`: the phase `ε_d` (`1` for `d ≡ 1 (mod 4)`, `i` for
  `d ≡ 3 (mod 4)`, and `0` for even `d`).
* `TauCeti.thetaAutomorphy`: the ratio `jacobiTheta (2 * (γ • z)) / jacobiTheta (2 * z)`.

## Main results

* `TauCeti.thetaMultiplierPhase_sq`, `TauCeti.inv_thetaMultiplierPhase_sq`:
  `ε_d² = ε_d⁻² = χ₄(d)`.
* `TauCeti.thetaAutomorphy_ne_zero`:
  `thetaAutomorphy γ z ≠ 0` for all `γ : SL(2, ℤ)` and `z : ℍ`.
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
noncomputable def thetaMultiplierPhase (d : ℤ) : ℂ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0

/-- The defining formula of `TauCeti.thetaMultiplierPhase`. -/
theorem thetaMultiplierPhase_def (d : ℤ) :
    thetaMultiplierPhase d = if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0 :=
  (rfl)

/-- `ε_d = 1` when `d ≡ 1 (mod 4)`. -/
theorem thetaMultiplierPhase_of_emod_eq_one {d : ℤ} (hd : d % 4 = 1) :
    thetaMultiplierPhase d = 1 := by
  simp [thetaMultiplierPhase_def, hd]

/-- `ε_d = i` when `d ≡ 3 (mod 4)`. -/
theorem thetaMultiplierPhase_of_emod_eq_three {d : ℤ} (hd : d % 4 = 3) :
    thetaMultiplierPhase d = I := by
  simp [thetaMultiplierPhase_def, hd]

/-- `ε_d = 0` when `d` is even. -/
theorem thetaMultiplierPhase_eq_zero_of_even {d : ℤ} (hd : Even d) :
    thetaMultiplierPhase d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [thetaMultiplierPhase_def]
  simp [show (k + k) % 4 ≠ 1 by omega, show (k + k) % 4 ≠ 3 by omega]

/-- `ε_0 = 0`. -/
@[simp]
theorem thetaMultiplierPhase_zero : thetaMultiplierPhase 0 = 0 :=
  thetaMultiplierPhase_eq_zero_of_even Even.zero

/-- `ε_1 = 1`. -/
@[simp]
theorem thetaMultiplierPhase_one : thetaMultiplierPhase 1 = 1 :=
  thetaMultiplierPhase_of_emod_eq_one (by norm_num)

/-- `ε_{-1} = i`. -/
@[simp]
theorem thetaMultiplierPhase_neg_one : thetaMultiplierPhase (-1) = I :=
  thetaMultiplierPhase_of_emod_eq_three (by norm_num)

/-- `thetaMultiplierPhase` depends only on `d` modulo `4`. -/
theorem thetaMultiplierPhase_congr {d d' : ℤ} (h : d ≡ d' [ZMOD 4]) :
    thetaMultiplierPhase d = thetaMultiplierPhase d' := by
  simp only [thetaMultiplierPhase_def, h.eq]

/-- `ε_d` vanishes exactly when `d` is even. -/
@[simp]
theorem thetaMultiplierPhase_eq_zero_iff {d : ℤ} :
    thetaMultiplierPhase d = 0 ↔ Even d := by
  refine ⟨fun h ↦ ?_, thetaMultiplierPhase_eq_zero_of_even⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  have hmod := Int.odd_iff.mp hodd
  rw [thetaMultiplierPhase_def] at h
  split_ifs at h with h₁ h₃
  · exact one_ne_zero h
  · exact I_ne_zero h
  · omega

/-- `ε_d ≠ 0` exactly when `d` is odd. -/
theorem thetaMultiplierPhase_ne_zero_iff {d : ℤ} :
    thetaMultiplierPhase d ≠ 0 ↔ Odd d := by
  simp [ne_eq, ← Int.not_even_iff_odd]

/-- For odd `d`, `ε_d ≠ 0`. -/
theorem thetaMultiplierPhase_ne_zero {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase d ≠ 0 :=
  thetaMultiplierPhase_ne_zero_iff.mpr hd

/-- For every integer `d`, `ε_d² = χ₄(d)`. -/
theorem thetaMultiplierPhase_sq (d : ℤ) :
    thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ (d : ZMod 4) : ℂ) := by
  rw [thetaMultiplierPhase_def, ZMod.χ₄_int_eq_if_mod_four]
  have hd : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
  rcases hd with h | h | h | h
  · simp [show d % 2 = 0 by omega, show d % 4 ≠ 1 by omega, show d % 4 ≠ 3 by omega]
  · simp [show d % 2 ≠ 0 by omega, h]
  · simp [show d % 2 = 0 by omega, show d % 4 ≠ 1 by omega, show d % 4 ≠ 3 by omega]
  · simp [show d % 2 ≠ 0 by omega, h]

/-- For odd `d`, `‖ε_d‖ = 1`. -/
@[simp]
theorem norm_thetaMultiplierPhase {d : ℤ} (hd : Odd d) : ‖thetaMultiplierPhase d‖ = 1 := by
  have hmod := Int.odd_iff.mp hd
  rw [thetaMultiplierPhase_def]
  split_ifs with h₁ h₃
  · simp
  · simp
  · omega

/-- For odd `d`, `ε_d⁻¹` is `1` when `d ≡ 1 (mod 4)` and `-i` when `d ≡ 3 (mod 4)`. -/
theorem inv_thetaMultiplierPhase {d : ℤ} (hd : Odd d) :
    (thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I := by
  have hmod := Int.odd_iff.mp hd
  rw [thetaMultiplierPhase_def]
  split_ifs with h₁ h₃ <;> simp [inv_I]
  omega

/-- For odd `d`, `(ε_d⁻¹)² = χ₄(d)`. -/
theorem inv_thetaMultiplierPhase_sq {d : ℤ} (hd : Odd d) :
    (thetaMultiplierPhase d)⁻¹ ^ 2 = (ZMod.χ₄ (d : ZMod 4) : ℂ) := by
  rw [inv_pow, thetaMultiplierPhase_sq]
  have hsq : (ZMod.χ₄ (d : ZMod 4) : ℂ) ^ 2 = 1 := by
    rw [← kroneckerSym_neg_one_left_of_odd hd, sq_intCast_kroneckerSym_eq_one (by simp)]
  exact inv_eq_of_mul_eq_one_right (by simpa [sq] using hsq)

/-- For odd `d`, `ε_{-d} = i ε_d⁻¹`. -/
theorem thetaMultiplierPhase_neg {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase (-d) = I * (thetaMultiplierPhase d)⁻¹ := by
  have hmod := Int.odd_iff.mp hd
  rw [inv_thetaMultiplierPhase hd, thetaMultiplierPhase_def]
  split_ifs with h₁ h₃ h₄ <;> simp <;> omega

/-- For odd `d`, `ε_d ε_{-d} = i`. -/
theorem thetaMultiplierPhase_mul_neg {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I := by
  rw [thetaMultiplierPhase_neg hd, ← mul_assoc, mul_comm (thetaMultiplierPhase d) I, mul_assoc,
    mul_inv_cancel₀ (thetaMultiplierPhase_ne_zero hd), mul_one]

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
  exact div_ne_zero (jacobiTheta_ne_zero (by simpa using mul_pos two_pos (γ • z).im_pos))
    (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))

/-- At the identity matrix, `j(1, z) = 1`. -/
@[simp]
theorem thetaAutomorphy_one (z : ℍ) : thetaAutomorphy 1 z = 1 := by
  rw [thetaAutomorphy_def, one_smul]
  exact div_self (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))

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
  have h0 : jacobiTheta (2 * ((γ₂ • z : ℍ) : ℂ)) ≠ 0 :=
    jacobiTheta_ne_zero (by simpa using mul_pos two_pos (γ₂ • z).im_pos)
  rw [div_mul_div_cancel₀ h0]

/-- Inversion law for the theta automorphy factor:
`j(γ⁻¹, γ • z) = j(γ, z)⁻¹`. -/
theorem thetaAutomorphy_inv_smul (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphy γ⁻¹ (γ • z) = (thetaAutomorphy γ z)⁻¹ := by
  rw [thetaAutomorphy_def, thetaAutomorphy_def, inv_smul_smul, inv_div]

/-- The eta-quotient exponent vector for `θ(2z) = η(2z)⁵ / (η(z)² η(4z)²)`. -/
private def thetaEtaExp : ℕ → ℤ := fun δ ↦ if δ = 2 then 5 else -2

private theorem jacobiTheta_two_mul_eq_etaQuotient (z : ℍ) :
    jacobiTheta (2 * (z : ℂ)) = ModularForm.etaQuotient 4 thetaEtaExp z := by
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [jacobiTheta_two_mul_eq_eta_div z.im_pos, ModularForm.etaQuotient_apply, hdiv,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [thetaEtaExp, Nat.cast_one, Nat.cast_ofNat, one_mul]
  norm_num
  ring

private theorem sum_thetaEtaExp : ∑ δ ∈ (4 : ℕ).divisors, thetaEtaExp δ = 1 := by
  decide

private theorem kroneckerSym_two_left_of_odd {d : ℤ} (hd : Odd d) :
    kroneckerSym 2 d = ZMod.χ₈ d := by
  rw [kroneckerSym_of_odd 2 hd, jacobiSym.at_two (Int.natAbs_odd.mpr hd)]
  simp only [show ¬((2 : ℤ) < 0 ∧ d < 0) by omega, ↓reduceIte, one_mul]
  rcases Int.natAbs_eq d with h | h
  · rw [h, Int.natAbs_natCast, Int.cast_natCast]
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast, ZMod.χ₈_neg]

private theorem kroneckerSym_two_mul_e24 {d : ℤ} (hd : Odd d) :
    (kroneckerSym 2 d : ℂ) * ModularForm.e24 (3 * d - 3) = (thetaMultiplierPhase d)⁻¹ := by
  rw [kroneckerSym_two_left_of_odd hd, ZMod.χ₈_int_eq_if_mod_eight, inv_thetaMultiplierPhase hd]
  have he24_6 : ModularForm.e24 6 = I := by
    rw [ModularForm.e24_def]
    convert Complex.exp_pi_div_two_mul_I using 2
    push_cast
    ring
  have hmod : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by
    obtain ⟨k, rfl⟩ := hd
    omega
  rcases hmod with h | h | h | h
  · have he : 3 * d - 3 ≡ 0 [ZMOD 24] := by rw [Int.ModEq]; omega
    rw [ModularForm.e24_congr he, ModularForm.e24_zero]
    simp [show d % 2 ≠ 0 by omega, h, show d % 4 = 1 by omega]
  · have he : 3 * d - 3 ≡ 6 [ZMOD 24] := by rw [Int.ModEq]; omega
    rw [ModularForm.e24_congr he, he24_6]
    simp [show d % 2 ≠ 0 by omega, show d % 8 ≠ 1 ∧ d % 8 ≠ 7 by omega,
      show d % 4 ≠ 1 by omega]
  · have he : 3 * d - 3 ≡ 12 * (1 : ℕ) [ZMOD 24] := by rw [Int.ModEq]; omega
    rw [ModularForm.e24_congr he, ModularForm.e24_twelve_mul]
    simp [show d % 2 ≠ 0 by omega, show d % 8 ≠ 1 ∧ d % 8 ≠ 7 by omega,
      show d % 4 = 1 by omega]
  · have he : 3 * d - 3 ≡ 12 * (1 : ℕ) + 6 [ZMOD 24] := by rw [Int.ModEq]; omega
    rw [ModularForm.e24_congr he, ModularForm.e24_add, ModularForm.e24_twelve_mul, he24_6]
    simp [show d % 2 ≠ 0 by omega, h, show d % 4 ≠ 1 by omega]

private theorem prod_kroneckerSym_thetaEtaExp {t d : ℤ} (ht : 0 ≤ t) (hd : Odd d)
    (hcop : IsCoprime (4 * t) d) :
    ∏ δ ∈ (4 : ℕ).divisors, (kroneckerSym ((4 / δ : ℕ) * t) d : ℂ) ^ thetaEtaExp δ =
      kroneckerSym 2 d * kroneckerSym (4 * t) d := by
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [hdiv, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [thetaEtaExp]
  norm_num
  have hcop4 : (4 * t).gcd d = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hcopt : t.gcd d = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_left (dvd_mul_left t 4))
  have hcop2 : (2 * t).gcd d = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_left ⟨2, by ring⟩)
  have h4sq : (kroneckerSym (4 * t) d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one hcop4
  have htsq : (kroneckerSym t d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one hcopt
  have h2pow : (kroneckerSym (2 * t) d : ℂ) ^ 5 = (kroneckerSym (2 * t) d : ℂ) := by
    have hsq : (kroneckerSym (2 * t) d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one hcop2
    rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
  rw [h4sq, inv_one, htsq, inv_one, h2pow, mul_one, one_mul]
  rcases eq_or_ne d (-1) with rfl | hd1
  · simp [kroneckerSym_neg_one_right, show ¬(4 * t < 0) by omega,
      show ¬(2 * t < 0) by omega]
  · have h2t : kroneckerSym (2 * t) d = kroneckerSym 2 d * kroneckerSym t d :=
      kroneckerSym_mul_left_of_ne_neg_one hd1 2 t
    have h4t : kroneckerSym (4 * t) d = kroneckerSym t d := by
      have h4_eq : 4 * t = t * 2 ^ 2 := by ring
      have hcop2d : (2 : ℤ).gcd d = 1 := Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hd)
      rw [h4_eq, kroneckerSym_mul_sq two_ne_zero hcop2d]
    rw [h2t, h4t, Int.cast_mul]

private theorem etaQuotientMultiplier_thetaEtaExp_of_nonneg {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 4) (hc : 0 ≤ γ 1 0) :
    ModularForm.etaQuotientMultiplier 4 thetaEtaExp ⟨γ, hγ⟩ =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
  norm_num at ht
  have ht0 : 0 ≤ t := by omega
  have hdo : Odd (γ 1 1) := γ.odd_apply_one_of_even_apply_zero ⟨2 * t, by omega⟩
  let E : ℕ → ℤ := fun δ ↦ (γ 0 0 + γ 1 1) * ((4 / δ : ℕ) * t) -
    γ 0 1 * δ * γ 1 1 * (((4 / δ : ℕ) * t) ^ 2 - 1) + 3 * γ 1 1 - 3 -
    3 * ((4 / δ : ℕ) * t) * γ 1 1
  have hε (δ : ℕ) (hδ : δ ∈ (4 : ℕ).divisors) :
      ModularForm.etaMultiplier
        (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) =
      (kroneckerSym ((4 / δ : ℕ) * t) (γ 1 1) : ℂ) * ModularForm.e24 (E δ) := by
    have hcδ : γ 1 0 = (δ : ℤ) * ((4 / δ : ℕ) * t) := by
      have hdvd : (δ : ℤ) * (4 / δ : ℕ) = 4 := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hδ)
      rw [ht, ← mul_assoc, hdvd]
    have hδ0 : (δ : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne'
    have h00 : conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 0 0 = γ 0 0 := by simp
    have h01 : conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 0 1 = γ 0 1 * δ := by
      simp [mul_comm]
    have h10 : conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 1 0 =
        (4 / δ : ℕ) * t := by
      simp [hcδ, Int.mul_ediv_cancel_left _ hδ0]
    have h11 : conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 1 1 = γ 1 1 := by simp
    rw [ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d _
      (by rw [h10]; exact mul_nonneg (Int.natCast_nonneg _) ht0) (by rw [h11]; exact hdo),
      h00, h01, h10, h11, ModularForm.e24_def]
  have hmult : ModularForm.etaQuotientMultiplier 4 thetaEtaExp ⟨γ, hγ⟩ =
      ∏ δ ∈ (4 : ℕ).divisors,
        ((kroneckerSym ((4 / δ : ℕ) * t) (γ 1 1) : ℂ) * ModularForm.e24 (E δ)) ^
          thetaEtaExp δ := by
    rw [ModularForm.etaQuotientMultiplier_def,
      ← Finset.prod_attach (4 : ℕ).divisors (fun δ ↦ _ ^ thetaEtaExp δ)]
    exact Finset.prod_congr rfl fun δ _ ↦ by rw [hε δ δ.property]
  have hE : ∑ δ ∈ (4 : ℕ).divisors, thetaEtaExp δ * E δ = 3 * γ 1 1 - 3 := by
    have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
    rw [hdiv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [thetaEtaExp, E]
    norm_num
    ring
  rw [hmult, ModularForm.prod_mul_e24_zpow, hE,
    prod_kroneckerSym_thetaEtaExp ht0 hdo (ht ▸ γ.isCoprime_row 1), ← ht,
    mul_comm (kroneckerSym 2 (γ 1 1) : ℂ), mul_assoc,
    mul_comm (kroneckerSym (γ 1 0) (γ 1 1) : ℂ), kroneckerSym_two_mul_e24 hdo]

private theorem thetaAutomorphy_eq_of_mem_Gamma0_of_nonneg {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4)
    (hc : 0 ≤ γ 1 0) (z : ℍ) :
    thetaAutomorphy γ z =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hsmul := ModularForm.etaQuotient_smul 4 thetaEtaExp ⟨γ, hγ⟩ z
  simp only [sum_thetaEtaExp, zpow_one,
    etaQuotientMultiplier_thetaEtaExp_of_nonneg hγ hc] at hsmul
  rw [thetaAutomorphy_def, jacobiTheta_two_mul_eq_etaQuotient (γ • z),
    jacobiTheta_two_mul_eq_etaQuotient z, hsmul, mul_div_assoc,
    div_self (ModularForm.etaQuotient_ne_zero 4 thetaEtaExp z.im_pos), mul_one]

/-- **Shimura's theta multiplier formula on `Γ₀(4)`** (Shimura (1973), (1.9)–(1.10); Iwaniec
(1987), (2.1)): for every `γ = (a b; c d) ∈ Γ₀(4)` and `z ∈ ℍ`,
`j(γ, z) = θ(γ • z) / θ(z) = ε_d⁻¹ (c / d) √(c z + d)`, with the principal square root
and the Kronecker symbol `TauCeti.kroneckerSym`. Holds for every sign of `c` and `d`. -/
theorem thetaAutomorphy_eq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphy γ z =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rcases le_or_gt 0 (γ 1 0) with hc | hc
  · exact thetaAutomorphy_eq_of_mem_Gamma0_of_nonneg hγ hc z
  · -- For `c < 0`, pass to `-γ ∈ Γ₀(4)`, which acts identically on `ℍ` and has `-c > 0`.
    have hγneg : -γ ∈ Gamma0 4 := mem_Gamma0_iff_dvd.mpr (by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      exact dvd_neg.mpr (mem_Gamma0_iff_dvd.mp hγ))
    have hsmul : (-γ) • z = γ • z := ModularGroup.SL_neg_smul γ z
    have hcneg : 0 ≤ (-γ) 1 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      omega
    have hmain := thetaAutomorphy_eq_of_mem_Gamma0_of_nonneg hγneg hcneg z
    rw [thetaAutomorphy_def, hsmul, ← thetaAutomorphy_def] at hmain
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at hmain
    obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
    have hdo : Odd (γ 1 1) := γ.odd_apply_one_of_even_apply_zero ⟨2 * t, by omega⟩
    -- 1. `(ε_{-d})⁻¹ = -i (-1 / d) ε_d⁻¹`
    have hε : (thetaMultiplierPhase (-γ 1 1))⁻¹ =
        -I * (kroneckerSym (-1) (γ 1 1) : ℂ) * (thetaMultiplierPhase (γ 1 1))⁻¹ := by
      rw [thetaMultiplierPhase_neg hdo, mul_inv, inv_I, inv_inv, mul_assoc]
      congr 1
      have hsq : (thetaMultiplierPhase (γ 1 1))⁻¹ ^ 2 = (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) :=
        inv_thetaMultiplierPhase_sq hdo
      rw [← kroneckerSym_neg_one_left_of_odd hdo] at hsq
      have hsym : (kroneckerSym (-1) (γ 1 1) : ℂ) ^ 2 = 1 :=
        sq_intCast_kroneckerSym_eq_one (by simp)
      calc
        thetaMultiplierPhase (γ 1 1)
          = thetaMultiplierPhase (γ 1 1) * (kroneckerSym (-1) (γ 1 1) : ℂ) ^ 2 := by
            rw [hsym, mul_one]
        _ = thetaMultiplierPhase (γ 1 1) * ((thetaMultiplierPhase (γ 1 1))⁻¹ ^ 2 *
              (kroneckerSym (-1) (γ 1 1) : ℂ)) := by
            rw [hsq, sq]
        _ = (thetaMultiplierPhase (γ 1 1) * (thetaMultiplierPhase (γ 1 1))⁻¹) *
              (thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (-1) (γ 1 1) : ℂ) := by
            rw [sq]
            ring
        _ = (kroneckerSym (-1) (γ 1 1) : ℂ) * (thetaMultiplierPhase (γ 1 1))⁻¹ := by
            rw [mul_inv_cancel₀ (thetaMultiplierPhase_ne_zero hdo), one_mul, mul_comm]
    -- 2. `(-c / -d) = (-1 / d) * (c / d)`
    have hsym : (kroneckerSym (-γ 1 0) (-γ 1 1) : ℂ) =
        (kroneckerSym (-1) (γ 1 1) : ℂ) * kroneckerSym (γ 1 0) (γ 1 1) := by
      have h1 : kroneckerSym (-γ 1 0) (-γ 1 1) =
          kroneckerSym (-1) (-γ 1 1) * kroneckerSym (γ 1 0) (-γ 1 1) := by
        rw [neg_eq_neg_one_mul (γ 1 0),
          kroneckerSym_mul_left (by norm_num) hc.ne (-γ 1 1)]
      have h2 : kroneckerSym (-1) (-γ 1 1) = -kroneckerSym (-1) (γ 1 1) := by
        rw [kroneckerSym_neg_one_left_of_odd hdo.neg, kroneckerSym_neg_one_left_of_odd hdo,
          Int.cast_neg, ZMod.χ₄_neg]
      have h3 : kroneckerSym (γ 1 0) (-γ 1 1) = -kroneckerSym (γ 1 0) (γ 1 1) := by
        have hd0 : γ 1 1 ≠ 0 := fun h ↦ by simp [h] at hdo
        rw [neg_eq_neg_one_mul (γ 1 1),
          kroneckerSym_mul_right (γ 1 0) (by norm_num) hd0,
          kroneckerSym_neg_one_right]
        simp [hc]
      rw [h1, h2, h3]
      push_cast
      ring
    -- 3. `√(-c z - d) = i √(c z + d)` since `im (c z + d) < 0`
    have hsqrt : Complex.sqrt (-(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ)) =
        I * Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
      set w : ℂ := (γ 1 0 : ℂ) * z + γ 1 1
      have hwim : w.im < 0 := by
        simpa [w] using mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hc) z.im_pos
      have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hwim
      have hneg : -(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ) = -w := by simp only [w]; ring
      have hlog : Complex.log (-w) = Complex.log w + π * I := by
        apply Complex.ext
        · simp [Complex.log_re]
        · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hwim]
      have hpi : (π : ℂ) * I / 2 = π / 2 * I := by ring
      rw [hneg, _root_.sqrt_eq_exp (neg_ne_zero.mpr hw0), _root_.sqrt_eq_exp hw0, hlog,
        add_div, Complex.exp_add, hpi, Complex.exp_pi_div_two_mul_I, mul_comm _ I]
    have hsym_sq : (kroneckerSym (-1) (γ 1 1) : ℂ) ^ 2 = 1 :=
      sq_intCast_kroneckerSym_eq_one (by simp)
    rw [hmain, hε, hsym, hsqrt]
    calc
      (-I * (kroneckerSym (-1) (γ 1 1) : ℂ) * (thetaMultiplierPhase (γ 1 1))⁻¹ *
          ((kroneckerSym (-1) (γ 1 1) : ℂ) * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ))) *
          (I * Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1))
        = -(I ^ 2) * (kroneckerSym (-1) (γ 1 1) : ℂ) ^ 2 *
            ((thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
              Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1)) := by ring
      _ = (thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
            Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
          rw [I_sq, hsym_sq]
          ring

/-- Variant of `thetaAutomorphy_eq_of_mem_Gamma0` expressing the transformation directly in terms
of `jacobiTheta (2 * z)`. -/
theorem jacobiTheta_two_mul_smul_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) * jacobiTheta (2 * (z : ℂ)) := by
  have h := thetaAutomorphy_eq_of_mem_Gamma0 hγ z
  rw [thetaAutomorphy_def] at h
  have hθ0 : jacobiTheta (2 * (z : ℂ)) ≠ 0 :=
    jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos)
  exact (div_eq_iff hθ0).mp h

/-- **The theta multiplier square law** on `Γ₀(4)` (Shimura (1973), (1.11)):
`j(γ, z)² = χ₄(d) (c z + d)` for every `γ = (a b; c d) ∈ Γ₀(4)` and `z ∈ ℍ`. -/
theorem thetaAutomorphy_sq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphy γ z ^ 2 =
      (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
  have hdo : Odd (γ 1 1) := γ.odd_apply_one_of_even_apply_zero ⟨2 * t, by omega⟩
  have hsym : (kroneckerSym (γ 1 0) (γ 1 1) : ℂ) ^ 2 = 1 :=
    sq_intCast_kroneckerSym_eq_one (Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_row 1))
  rw [thetaAutomorphy_eq_of_mem_Gamma0 hγ z, mul_pow, mul_pow,
    inv_thetaMultiplierPhase_sq hdo, hsym, mul_one, Complex.sq_sqrt]

/-- The theta multiplier square law written with the Kronecker symbol `(-1 / d)`. -/
theorem thetaAutomorphy_sq_eq_kroneckerSym_mul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphy γ z ^ 2 =
      (kroneckerSym (-1) (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
  have hdo : Odd (γ 1 1) := γ.odd_apply_one_of_even_apply_zero ⟨2 * t, by omega⟩
  rw [thetaAutomorphy_sq_of_mem_Gamma0 hγ z, ← kroneckerSym_neg_one_left_of_odd hdo]

end TauCeti
