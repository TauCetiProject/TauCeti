/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.JacobiTheta.AutomorphyFactor
public import TauCeti.NumberTheory.ModularForms.JacobiTheta.EtaQuotient
public import TauCeti.NumberTheory.ModularForms.JacobiTheta.Phase
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient.Kronecker
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Product

/-!
# Shimura's theta multiplier and automorphy factor on `Γ₀(4)`

Starting from the level-`4` eta-quotient identity `TauCeti.jacobiTheta_two_mul_eq_etaQuotient` in
`TauCeti.NumberTheory.ModularForms.JacobiTheta.EtaQuotient`, this file evaluates the scalar
multiplier `etaQuotientMultiplier 4 thetaExpVec` on `Γ₀(4)` via
`TauCeti.ModularForm.etaQuotient_smul` and
`TauCeti.ModularForm.etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d`, and specializes
the general `SL(2, ℤ)` automorphy factor `TauCeti.thetaAutomorphyFactor` (defined in
`TauCeti.NumberTheory.ModularForms.JacobiTheta.AutomorphyFactor`, with phase
`TauCeti.thetaMultiplierPhase` from `TauCeti.NumberTheory.ModularForms.JacobiTheta.Phase`) to
`Γ₀(4)` and `Γ₁(4)`.

## Main results

* `TauCeti.etaQuotientMultiplier_thetaExpVec`,
  `TauCeti.etaQuotientMultiplier_thetaExpVec_pow_four`: evaluation of
  `etaQuotientMultiplier 4 thetaExpVec γ` on `Γ₀(4)` and the fourth-power-one identity.
* `TauCeti.thetaAutomorphyFactor_of_mem_Gamma0`: Shimura's formula for `γ ∈ Γ₀(4)`,
  `thetaAutomorphyFactor γ z = (ε_d)⁻¹ * kroneckerSym c d * Complex.sqrt (c z + d)` with the
  Kronecker symbol `TauCeti.kroneckerSym` and principal square root `Complex.sqrt`.
* `TauCeti.thetaAutomorphyFactor_sq_of_mem_Gamma0`,
  `TauCeti.thetaAutomorphyFactor_sq_of_mem_Gamma1`,
  `TauCeti.norm_thetaAutomorphyFactor_of_mem_Gamma0`: the square and weight-`1/2` modulus laws
  on `Γ₀(4)` and `Γ₁(4)`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. (2) **97** (1973),
  440–481, (1.10)–(1.11).
* H. Iwaniec, *Fourier coefficients of modular forms of half-integral weight*, Invent. Math. **87**
  (1987), 385–401, §2.
-/

public section

open Complex CongruenceSubgroup ModularGroup TauCeti.ModularForm
open scoped ModularForm MatrixGroups Real UpperHalfPlane

namespace TauCeti

/-! ### Evaluation of the level-`4` theta eta-quotient multiplier on `Γ₀(4)` -/

private lemma kroneckerSym_two_mul_e24_three_mul_sub_three {d : ℤ} (hd : Odd d) :
    (kroneckerSym 2 d : ℂ) * e24 (3 * d - 3) = (thetaMultiplierPhase d)⁻¹ := by
  rw [kroneckerSym_two_left, thetaMultiplierPhase_inv hd, ZMod.χ₈_int_mod_eight]
  have hcongr : e24 (3 * d - 3) = e24 (3 * (d % 8) - 3) :=
    e24_congr (Int.modEq_iff_dvd.mpr ⟨-(d / 8), by omega⟩)
  have hmod4 : d % 4 = (d % 8) % 4 := by omega
  have hr : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by
    obtain ⟨t, rfl⟩ := hd
    omega
  have h12 : e24 12 = -1 := by simpa using e24_twelve_mul 1
  have hcongr7 : (18 : ℤ) ≡ -6 [ZMOD 24] := by decide
  rw [hcongr, hmod4]
  rcases hr with h | h | h | h <;> rw [h]
  · norm_num [ZMod.χ₈_int_eq_if_mod_eight, e24_zero]
  · norm_num [ZMod.χ₈_int_eq_if_mod_eight]
  · norm_num [ZMod.χ₈_int_eq_if_mod_eight, h12]
  · norm_num [ZMod.χ₈_int_eq_if_mod_eight]
    rw [e24_congr hcongr7]
    norm_num

private lemma prod_kroneckerSym_thetaExpVec {γ : SL(2, ℤ)} {t : ℤ} (ht : γ 1 0 = 4 * t) :
    ∏ δ ∈ (4 : ℕ).divisors, (kroneckerSym ((4 / δ : ℕ) * t) (γ 1 1) : ℂ) ^ thetaExpVec δ =
      kroneckerSym 2 (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
  have hcop_dvd {x : ℤ} (hx : x ∣ γ 1 0) : x.gcd (γ 1 1) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ((γ.isCoprime_row 1).of_isCoprime_of_dvd_left hx)
  have hpow_neg_two {x : ℤ} (hx : x ∣ γ 1 0) :
      ((kroneckerSym x (γ 1 1) : ℤ) : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [zpow_neg _ 2, zpow_ofNat, sq_intCast_kroneckerSym_eq_one (hcop_dvd hx), inv_one]
  have hk_2t : ((kroneckerSym (2 * t) (γ 1 1) : ℤ) : ℂ) ^ (5 : ℤ) =
      kroneckerSym (2 * t) (γ 1 1) := by
    have hpow5 (x : ℂ) : x ^ (5 : ℤ) = (x ^ 2) ^ 2 * x := by rw [zpow_ofNat]; ring
    rw [hpow5, sq_intCast_kroneckerSym_eq_one (hcop_dvd ⟨2, by omega⟩)]
    simp
  have hk_eq : kroneckerSym (2 * t) (γ 1 1) =
      kroneckerSym 2 (γ 1 1) * kroneckerSym (4 * t) (γ 1 1) := by
    rcases eq_or_ne t 0 with rfl | ht_ne
    · have hd1 : γ 1 1 = 1 ∨ γ 1 1 = -1 :=
        (Int.eq_one_or_neg_one_of_mul_eq_one'
          (γ.apply_zero_zero_mul_apply_one_one_of_apply_one_zero_eq_zero (by simp [ht]))).elim
          (fun h ↦ .inl h.2) (fun h ↦ .inr h.2)
      rcases hd1 with h | h <;> simp [h]
    · have h4t : (4 * t : ℤ) = t * 2 ^ 2 := by ring
      rw [kroneckerSym_mul_left two_ne_zero ht_ne, h4t,
        kroneckerSym_mul_sq two_ne_zero (hcop_dvd ⟨2 * t, by omega⟩)]
  have h4t_eq : (4 * t : ℤ) = γ 1 0 := by simpa using ht.symm
  rw [prod_divisors_four_thetaExpVec (fun δ ↦ (kroneckerSym ((4 / δ : ℕ) * t) (γ 1 1) : ℂ))]
  norm_num only [Nat.reduceDiv, Nat.cast_one, one_mul, Nat.cast_ofNat]
  rw [hpow_neg_two ⟨1, by omega⟩, hpow_neg_two ⟨4, by omega⟩, hk_2t, hk_eq, h4t_eq,
    one_mul, mul_one, Int.cast_mul]

/-- Evaluating the level-`4` theta eta-quotient multiplier on `Γ₀(4)`:
`etaQuotientMultiplier 4 thetaExpVec γ = (thetaMultiplierPhase d)⁻¹ * kroneckerSym c d`. -/
theorem etaQuotientMultiplier_thetaExpVec (γ : Gamma0 4) :
    etaQuotientMultiplier 4 thetaExpVec γ =
      (thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1))⁻¹ *
        kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp γ.property
  have hdo : Odd ((γ : SL(2, ℤ)) 1 1) :=
    odd_apply_one_one_of_mem_Gamma0 (by decide : Even 4) γ.property
  have h24 : (24 : ℤ) ∣ ∑ δ ∈ (4 : ℕ).divisors, (δ : ℤ) * thetaExpVec δ := by
    have h : ∑ δ ∈ (4 : ℕ).divisors, (δ : ℤ) * thetaExpVec δ = 0 := by
      simp only [thetaExpVec_def]; decide
    exact h ▸ dvd_zero 24
  have h24' : (24 : ℤ) ∣ ∑ δ ∈ (4 : ℕ).divisors, ((4 / δ : ℕ) : ℤ) * thetaExpVec δ := by
    have h : ∑ δ ∈ (4 : ℕ).divisors, ((4 / δ : ℕ) : ℤ) * thetaExpVec δ = 0 := by
      simp only [thetaExpVec_def]; decide
    exact h ▸ dvd_zero 24
  rw [etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d thetaExpVec γ.property ht hdo,
    e24_congr (etaQuotientMultiplierExp_modEq h24 h24' _ _ _ _), sum_divisors_four_thetaExpVec,
    one_mul, prod_kroneckerSym_thetaExpVec ht, mul_right_comm,
    kroneckerSym_two_mul_e24_three_mul_sub_three hdo]

/-- On `Γ₀(4)`, the scalar theta multiplier `etaQuotientMultiplier 4 thetaExpVec γ` has fourth
power `1`. -/
@[simp]
theorem etaQuotientMultiplier_thetaExpVec_pow_four (γ : Gamma0 4) :
    etaQuotientMultiplier 4 thetaExpVec γ ^ 4 = 1 := by
  have hdo : Odd ((γ : SL(2, ℤ)) 1 1) :=
    odd_apply_one_one_of_mem_Gamma0 (by decide : Even 4) γ.property
  have hcop : ((γ : SL(2, ℤ)) 1 0).gcd ((γ : SL(2, ℤ)) 1 1) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ((γ : SL(2, ℤ)).isCoprime_row 1)
  have hpow4 : (kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) : ℂ) ^ 4 = 1 := by
    calc (kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) : ℂ) ^ 4
        = ((kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) : ℂ) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [sq_intCast_kroneckerSym_eq_one hcop, one_pow]
  rw [etaQuotientMultiplier_thetaExpVec, mul_pow, inv_pow, thetaMultiplierPhase_pow_four hdo,
    inv_one, one_mul, hpow4]

/-! ### Specialization of `thetaAutomorphyFactor` to `Γ₀(4)` and `Γ₁(4)` -/

/-- **Shimura's theta transformation law** for `γ ∈ Γ₀(4)`:
`θ(2 · γ z) = ε_d⁻¹ · kroneckerSym c d · Complex.sqrt (c z + d) · θ(2 z)`, where
`(c / d) = kroneckerSym c d` is the Kronecker symbol `TauCeti.kroneckerSym` and `√` is the
principal square root `Complex.sqrt`. -/
theorem jacobiTheta_two_mul_smul_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * kroneckerSym (γ 1 0) (γ 1 1) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) * jacobiTheta (2 * (z : ℂ)) := by
  rw [jacobiTheta_two_mul_eq_etaQuotient (γ • z).im_pos,
    jacobiTheta_two_mul_eq_etaQuotient z.im_pos,
    etaQuotient_smul 4 thetaExpVec ⟨γ, hγ⟩ z,
    sum_divisors_four_thetaExpVec, zpow_one,
    etaQuotientMultiplier_thetaExpVec ⟨γ, hγ⟩]

/-- **Shimura's formula for the theta automorphy factor on `Γ₀(4)`**:
`thetaAutomorphyFactor γ z = ε_d⁻¹ · kroneckerSym c d · Complex.sqrt (c z + d)`, where
`(c / d) = kroneckerSym c d` is the Kronecker symbol `TauCeti.kroneckerSym` and `√` is the
principal square root `Complex.sqrt`. -/
theorem thetaAutomorphyFactor_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphyFactor γ z =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * kroneckerSym (γ 1 0) (γ 1 1) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [thetaAutomorphyFactor_def, jacobiTheta_two_mul_smul_of_mem_Gamma0 hγ z,
    mul_div_cancel_right₀ _ (by simpa using jacobiTheta_natCast_mul_ne_zero 2 z)]

/-- **Square of the theta automorphy factor on `Γ₀(4)`**:
`thetaAutomorphyFactor γ z ^ 2 = χ₄(d) · (c z + d)`. -/
theorem thetaAutomorphyFactor_sq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphyFactor γ z ^ 2 = (ZMod.χ₄ (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hdo : Odd (γ 1 1) := odd_apply_one_one_of_mem_Gamma0 (by decide : Even 4) hγ
  have hcop : (γ 1 0).gcd (γ 1 1) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_row 1)
  have hχ_inv : ((ZMod.χ₄ (γ 1 1) : ℤ) : ℂ)⁻¹ = ZMod.χ₄ (γ 1 1) :=
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact_mod_cast ZMod.χ₄_intCast_sq hdo)
  rw [thetaAutomorphyFactor_of_mem_Gamma0 hγ z, mul_pow, mul_pow, inv_pow,
    thetaMultiplierPhase_sq, hχ_inv, sq_intCast_kroneckerSym_eq_one hcop, mul_one,
    Complex.sq_sqrt]

/-- **Weight-`1/2` modulus law** for the theta automorphy factor on `Γ₀(4)`:
`‖thetaAutomorphyFactor γ z‖ = √‖c z + d‖`. -/
theorem norm_thetaAutomorphyFactor_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    ‖thetaAutomorphyFactor γ z‖ = √‖(γ 1 0 : ℂ) * z + γ 1 1‖ := by
  have hdo : Odd (γ 1 1) := odd_apply_one_one_of_mem_Gamma0 (by decide : Even 4) hγ
  have hχ_sq : ‖(ZMod.χ₄ (γ 1 1) : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, show (ZMod.χ₄ (γ 1 1) : ℂ) ^ 2 = 1 from by
      exact_mod_cast ZMod.χ₄_intCast_sq hdo, norm_one]
  have hχ : ‖(ZMod.χ₄ (γ 1 1) : ℂ)‖ = 1 :=
    (sq_eq_one_iff.mp hχ_sq).resolve_right (by linarith [norm_nonneg (ZMod.χ₄ (γ 1 1) : ℂ)])
  rw [← Real.sqrt_sq (norm_nonneg _), ← norm_pow, thetaAutomorphyFactor_sq_of_mem_Gamma0 hγ z,
    norm_mul, hχ, one_mul]

/-- On `Γ₁(4)`, the square of the theta automorphy factor simplifies to `c z + d`. -/
theorem thetaAutomorphyFactor_sq_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 4) (z : ℍ) :
    thetaAutomorphyFactor γ z ^ 2 = (γ 1 0 : ℂ) * z + γ 1 1 := by
  have h := thetaAutomorphyFactor_sq_of_mem_Gamma0 (Gamma1_le_Gamma0 4 hγ) z
  have hd : (4 : ℤ) ∣ γ 1 1 - 1 := (mem_Gamma1_iff_dvd_lowerRow.mp hγ).2
  have hχ : ZMod.χ₄ (γ 1 1) = 1 :=
    ZMod.χ₄_int_one_mod_four (by obtain ⟨k, hk⟩ := hd; omega)
  rwa [hχ, Int.cast_one, one_mul] at h

end TauCeti
