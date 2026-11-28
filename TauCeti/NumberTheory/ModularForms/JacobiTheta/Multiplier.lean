/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Product

/-!
# Shimura's theta multiplier and automorphy factor on `Γ₀(4)`

Using the eta-quotient identity `TauCeti.jacobiTheta_two_mul_eq_eta_pow_div` (derived from
`TauCeti.ModularForm.eta_two_mul` in `TauCeti.NumberTheory.ModularForms.JacobiTheta.Product`), this
file identifies `θ(2 τ)` with the level-`4` eta quotient `η(2 τ)⁵ / (η(τ)² η(4 τ)²)` and derives
Shimura's weight-`1/2` automorphy factor `j(γ, z) = θ(2 · γ z) / θ(2 z)` for `γ ∈ Γ₀(4)` via
`TauCeti.ModularForm.etaQuotient_smul`, reducing to
`TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d` in the `c ≥ 0` case
and passing to `-γ` via `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos` when `c < 0`.

## Main definitions

* `TauCeti.thetaMultiplierPhase`: Shimura's fourth-root-of-unity phase `ε_d` for odd `d`, equal to
  `1` for `d ≡ 1 (mod 4)` and `I` for `d ≡ 3 (mod 4)`, extended by `0` for even `d`.
* `TauCeti.thetaAutomorphyFactor`: the theta automorphy factor
  `j(γ, z) = jacobiTheta (2 * (γ • z)) / jacobiTheta (2 * z)` for `γ ∈ SL(2, ℤ)` and `z ∈ ℍ`.

## Main results

* `TauCeti.thetaMultiplierPhase_sq`:
  `thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ)` for every `d : ℤ`.
* `TauCeti.thetaAutomorphyFactor_mul`: the cocycle law
  `j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)` for all `γ₁, γ₂ ∈ SL(2, ℤ)`.
* `TauCeti.mdifferentiable_thetaAutomorphyFactor`: `thetaAutomorphyFactor γ` is holomorphic on `ℍ`
  for every `γ ∈ SL(2, ℤ)`.
* `TauCeti.thetaAutomorphyFactor_of_mem_Gamma0`: Shimura's formula for `γ ∈ Γ₀(4)`,
  `thetaAutomorphyFactor γ z = (ε_d)⁻¹ * kroneckerSym c d * Complex.sqrt (c * z + d)` with the
  Kronecker symbol `TauCeti.kroneckerSym` and principal square root `Complex.sqrt`.
* `TauCeti.thetaAutomorphyFactor_sq_of_mem_Gamma0`: for `γ ∈ Γ₀(4)`,
  `thetaAutomorphyFactor γ z ^ 2 = (ZMod.χ₄ (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1)`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. (2) **97** (1973),
  440–481, (1.10)–(1.11).
* H. Iwaniec, *Fourier coefficients of modular forms of half-integral weight*, Invent. Math. **87**
  (1987), 385–401, §2.
-/

public section

open Complex CongruenceSubgroup ModularGroup TauCeti.ModularForm
open scoped Manifold ModularForm MatrixGroups Real UpperHalfPlane

namespace TauCeti

/-! ### Shimura's phase factor `ε_d` -/

/-- Shimura's phase factor `ε_d`, a fourth root of unity for odd `d` (`1` for `d ≡ 1 (mod 4)`, `I`
for `d ≡ 3 (mod 4)`) extended by `0` for even `d`, appearing in the transformation law of `θ(2 τ)`
under `Γ₀(4)`. -/
noncomputable def thetaMultiplierPhase (d : ℤ) : ℂ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0

/-- Defining formula for `thetaMultiplierPhase`. -/
theorem thetaMultiplierPhase_def (d : ℤ) :
    thetaMultiplierPhase d = if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0 := (rfl)

/-- For `d ≡ 1 (mod 4)`, `thetaMultiplierPhase d = 1`. -/
theorem thetaMultiplierPhase_one_mod_four {d : ℤ} (hd : d % 4 = 1) :
    thetaMultiplierPhase d = 1 := by
  rw [thetaMultiplierPhase_def, ite_eq_left hd]

/-- For `d ≡ 3 (mod 4)`, `thetaMultiplierPhase d = I`. -/
theorem thetaMultiplierPhase_three_mod_four {d : ℤ} (hd : d % 4 = 3) :
    thetaMultiplierPhase d = I := by
  rw [thetaMultiplierPhase_def, ite_eq_right (by omega), ite_eq_left hd]

/-- For even `d`, `thetaMultiplierPhase d = 0`. -/
theorem thetaMultiplierPhase_of_even {d : ℤ} (hd : Even d) : thetaMultiplierPhase d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [thetaMultiplierPhase_def, ite_eq_right (by omega), ite_eq_right (by omega)]

private lemma odd_emod_four_eq {d : ℤ} (hd : Odd d) : d % 4 = 1 ∨ d % 4 = 3 := by
  obtain ⟨k, rfl⟩ := hd
  omega

/-- `thetaMultiplierPhase d = 0` if and only if `d` is even. -/
@[simp]
theorem thetaMultiplierPhase_eq_zero_iff (d : ℤ) : thetaMultiplierPhase d = 0 ↔ Even d := by
  refine ⟨fun h ↦ ?_, thetaMultiplierPhase_of_even⟩
  by_contra hodd
  rcases odd_emod_four_eq (Int.not_even_iff_odd.mp hodd) with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm] at h
    exact one_ne_zero h
  · rw [thetaMultiplierPhase_three_mod_four hm] at h
    exact I_ne_zero h

/-- For odd `d`, `thetaMultiplierPhase d ≠ 0`. -/
theorem thetaMultiplierPhase_ne_zero {d : ℤ} (hd : Odd d) : thetaMultiplierPhase d ≠ 0 := by
  rw [ne_eq, thetaMultiplierPhase_eq_zero_iff]
  exact Int.not_even_iff_odd.mpr hd

@[simp]
theorem thetaMultiplierPhase_zero : thetaMultiplierPhase 0 = 0 :=
  thetaMultiplierPhase_of_even ⟨0, rfl⟩

@[simp]
theorem thetaMultiplierPhase_one : thetaMultiplierPhase 1 = 1 :=
  thetaMultiplierPhase_one_mod_four (by norm_num)

@[simp]
theorem thetaMultiplierPhase_neg_one : thetaMultiplierPhase (-1) = I :=
  thetaMultiplierPhase_three_mod_four (by norm_num)

/-- `thetaMultiplierPhase` depends only on the residue class modulo `4`. -/
theorem thetaMultiplierPhase_congr {d d' : ℤ} (h : d ≡ d' [ZMOD 4]) :
    thetaMultiplierPhase d = thetaMultiplierPhase d' := by
  simp only [thetaMultiplierPhase_def, Int.ModEq] at h ⊢
  rw [h]

/-- `thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ)` for every integer `d`. -/
theorem thetaMultiplierPhase_sq (d : ℤ) : thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ) := by
  rw [ZMod.χ₄_int_eq_if_mod_four]
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_of_even hd, zero_pow two_ne_zero,
      ite_eq_left (by obtain ⟨k, rfl⟩ := hd; omega), Int.cast_zero]
  · have hne : d % 2 ≠ 0 := by
      obtain ⟨k, rfl⟩ := hd
      omega
    rw [ite_eq_right hne]
    rcases odd_emod_four_eq hd with hm | hm
    · rw [thetaMultiplierPhase_one_mod_four hm, ite_eq_left hm]
      norm_num
    · rw [thetaMultiplierPhase_three_mod_four hm, ite_eq_right (by omega)]
      norm_num

/-- For odd `d`, `‖thetaMultiplierPhase d‖ = 1`. -/
theorem norm_thetaMultiplierPhase {d : ℤ} (hd : Odd d) : ‖thetaMultiplierPhase d‖ = 1 := by
  rcases odd_emod_four_eq hd with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, norm_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, norm_I]

/-- For odd `d`, `(thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I`. -/
theorem thetaMultiplierPhase_inv {d : ℤ} (hd : Odd d) :
    (thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I := by
  rcases odd_emod_four_eq hd with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, ite_eq_left hm, inv_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, ite_eq_right (by omega), inv_I]

/-- Negating the integer parameter gives
`thetaMultiplierPhase (-d) = I * star (thetaMultiplierPhase d)` for every `d : ℤ` (both sides
vanish when `d` is even). -/
theorem thetaMultiplierPhase_neg (d : ℤ) :
    thetaMultiplierPhase (-d) = I * star (thetaMultiplierPhase d) := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_of_even hd.neg, thetaMultiplierPhase_of_even hd, star_zero, mul_zero]
  · rcases odd_emod_four_eq hd with hm | hm
    · rw [thetaMultiplierPhase_three_mod_four (by omega), thetaMultiplierPhase_one_mod_four hm,
        star_one, mul_one]
    · rw [thetaMultiplierPhase_one_mod_four (by omega), thetaMultiplierPhase_three_mod_four hm,
        Complex.star_def, conj_I, mul_neg, I_mul_I, neg_neg]

/-- For odd `d`, `thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I`. -/
theorem thetaMultiplierPhase_mul_neg {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I := by
  rcases odd_emod_four_eq hd with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, thetaMultiplierPhase_three_mod_four (by omega),
      one_mul]
  · rw [thetaMultiplierPhase_three_mod_four hm, thetaMultiplierPhase_one_mod_four (by omega),
      mul_one]

/-- Conjugation equals inversion on `thetaMultiplierPhase d` for every integer `d` (both sides
vanish when `d` is even, and `‖thetaMultiplierPhase d‖ = 1` when `d` is odd). -/
theorem star_thetaMultiplierPhase (d : ℤ) :
    star (thetaMultiplierPhase d) = (thetaMultiplierPhase d)⁻¹ := by
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_of_even hd, star_zero, inv_zero]
  · rw [Complex.star_def]
    exact (Complex.inv_eq_conj (norm_thetaMultiplierPhase hd)).symm

/-! ### Evaluation of the level-`4` theta eta-quotient multiplier on `Γ₀(4)` -/

/-- The exponent vector of the level-`4` eta quotient representing `τ ↦ θ(2 τ)`. -/
private def thetaExpVec : ℕ → ℤ :=
  fun δ ↦ if δ = 2 then 5 else if δ = 1 ∨ δ = 4 then -2 else 0

private lemma sum_divisors_four_thetaExpVec : ∑ δ ∈ (4 : ℕ).divisors, thetaExpVec δ = 1 := by
  decide

private lemma jacobiTheta_two_mul_eq_etaQuotient {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = etaQuotient 4 thetaExpVec τ := by
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [jacobiTheta_two_mul_eq_eta_pow_div hτ, etaQuotient_apply, hdiv]
  simp only [Finset.mem_insert, Finset.mem_singleton, OfNat.one_ne_ofNat, OfNat.ofNat_ne_one,
    or_self, not_false_eq_true, Finset.prod_insert, Nat.cast_one, one_mul,
    Nat.reduceEqDiff, Finset.prod_singleton, Nat.cast_ofNat, thetaExpVec]
  norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, zpow_neg, zpow_ofNat]

private lemma odd_apply_one_one_of_mem_Gamma0_four {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) :
    Odd (γ 1 1) :=
  γ.odd_apply_one_of_even_apply_zero
    (even_iff_two_dvd.mpr (dvd_trans (by decide) (mem_Gamma0_iff_dvd.mp hγ)))

private lemma chi4_sq_eq_one_of_odd {d : ℤ} (hd : Odd d) : ((ZMod.χ₄ d : ℤ) : ℂ) ^ 2 = 1 := by
  rw [← kroneckerSym_neg_one_left_of_odd hd]
  exact sq_intCast_kroneckerSym_eq_one (by simp)

private lemma kroneckerSym_two_mul_e24_three_mul_sub_three {d : ℤ} (hd : Odd d) :
    (kroneckerSym 2 d : ℂ) * e24 (3 * d - 3) = (thetaMultiplierPhase d)⁻¹ := by
  rw [kroneckerSym_two_left, thetaMultiplierPhase_inv hd]
  obtain ⟨m, r, hr0, hr8, rfl⟩ : ∃ m r : ℤ, 0 ≤ r ∧ r < 8 ∧ d = 8 * m + r :=
    ⟨d / 8, d % 8, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), by omega⟩
  have hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
    obtain ⟨t, ht⟩ := hd
    omega
  have h8 : ((8 : ℤ) : ZMod 8) = 0 := by decide
  have hχ₈ (a : ℤ) : ZMod.χ₈ ((8 * m + a : ℤ) : ZMod 8) = ZMod.χ₈ a := by
    rw [Int.cast_add, Int.cast_mul, h8, zero_mul, zero_add]
  have hcongr (a : ℤ) : e24 (3 * (8 * m + a) - 3) = e24 (3 * a - 3) :=
    e24_congr (Int.modEq_iff_dvd.mpr ⟨-m, by ring⟩)
  rw [hχ₈, hcongr]
  rcases hr with rfl | rfl | rfl | rfl
  · have harg : (3 * (1 : ℤ) - 3) = 0 := by norm_num
    rw [ite_eq_left (by omega), ZMod.χ₈_int_eq_if_mod_eight, harg, e24_zero]
    norm_num
  · have harg : (2 * π * I * 6 / 24 : ℂ) = π / 2 * I := by ring
    rw [ite_eq_right (by omega), ZMod.χ₈_int_eq_if_mod_eight, e24_def]
    norm_num
    rw [harg, Complex.exp_pi_div_two_mul_I]
  · have harg : (2 * π * I * 12 / 24 : ℂ) = π * I := by ring
    rw [ite_eq_left (by omega), ZMod.χ₈_int_eq_if_mod_eight, e24_def]
    norm_num
    rw [harg, Complex.exp_pi_mul_I]
    ring
  · have harg : (2 * π * I * 18 / 24 : ℂ) = π * I + π / 2 * I := by ring
    rw [ite_eq_right (by omega), ZMod.χ₈_int_eq_if_mod_eight, e24_def]
    norm_num
    rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    ring

private lemma prod_kroneckerSym_thetaExpVec {γ : SL(2, ℤ)} {t : ℤ} (ht : γ 1 0 = 4 * t) :
    ∏ δ ∈ (4 : ℕ).divisors, (kroneckerSym ((4 / δ : ℕ) * t) (γ 1 1) : ℂ) ^ thetaExpVec δ =
      kroneckerSym 2 (γ 1 1) * kroneckerSym (γ 1 0) (γ 1 1) := by
  have hcop : (γ 1 0).gcd (γ 1 1) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_row 1)
  have hcop_dvd {x : ℤ} (hx : x ∣ γ 1 0) : x.gcd (γ 1 1) = 1 := by
    have hdvd := Int.gcd_dvd_gcd_of_dvd_left (γ 1 1) hx
    rw [hcop] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hpow_neg_two {x : ℤ} (hx : x ∣ γ 1 0) :
      ((kroneckerSym x (γ 1 1) : ℤ) : ℂ) ^ (-2 : ℤ) = 1 := by
    have hneg2 : (-2 : ℤ) = -(2 : ℕ) := rfl
    rw [hneg2, zpow_neg, zpow_natCast, sq_intCast_kroneckerSym_eq_one (hcop_dvd hx), inv_one]
  have hk_2t : ((kroneckerSym (2 * t) (γ 1 1) : ℤ) : ℂ) ^ (5 : ℤ) =
      kroneckerSym (2 * t) (γ 1 1) := by
    have h5 : (5 : ℤ) = (2 * 2 + 1 : ℕ) := rfl
    rw [h5, zpow_natCast, pow_add, pow_mul,
      sq_intCast_kroneckerSym_eq_one (hcop_dvd ⟨2, by omega⟩)]
    simp
  have hk_eq : kroneckerSym (2 * t) (γ 1 1) =
      kroneckerSym 2 (γ 1 1) * kroneckerSym (4 * t) (γ 1 1) := by
    rcases eq_or_ne t 0 with rfl | ht_ne
    · have hd1 : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        have hdet := γ.fin_two_mul_sub_mul_eq_one
        rw [ht, mul_zero, mul_zero, sub_zero] at hdet
        exact Int.eq_one_or_neg_one_of_mul_eq_one' hdet |>.elim (fun h ↦ .inl h.2)
          (fun h ↦ .inr h.2)
      rcases hd1 with h | h <;> simp [h]
    · have h4t : (4 * t : ℤ) = t * 2 ^ 2 := by ring
      rw [kroneckerSym_mul_left two_ne_zero ht_ne, h4t,
        kroneckerSym_mul_sq two_ne_zero (hcop_dvd ⟨2 * t, by omega⟩)]
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  have hr1 : thetaExpVec 1 = -2 := by decide
  have hr2 : thetaExpVec 2 = 5 := by decide
  have hr4 : thetaExpVec 4 = -2 := by decide
  have h4t_eq : (4 * t : ℤ) = γ 1 0 := by simpa using ht.symm
  rw [hdiv, Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
    Finset.prod_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)), Finset.prod_singleton,
    hr1, hr2, hr4]
  norm_num only [Nat.reduceDiv, Nat.cast_one, one_mul, Nat.cast_ofNat]
  rw [hpow_neg_two ⟨1, by omega⟩, hpow_neg_two ⟨4, by omega⟩, hk_2t, hk_eq, h4t_eq,
    one_mul, mul_one, Int.cast_mul]

private lemma etaQuotientMultiplier_thetaExpVec_of_c_nonneg {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4)
    (hc : 0 ≤ γ 1 0) :
    etaQuotientMultiplier 4 thetaExpVec ⟨γ, hγ⟩ =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * kroneckerSym (γ 1 0) (γ 1 1) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
  have ht0 : 0 ≤ t := by omega
  have hdo : Odd (γ 1 1) := odd_apply_one_one_of_mem_Gamma0_four hγ
  let E : ℕ → ℤ := fun δ ↦ (γ 0 0 + γ 1 1) * ((4 / δ : ℕ) * t) -
    γ 0 1 * δ * γ 1 1 * (((4 / δ : ℕ) * t) ^ 2 - 1) +
    3 * γ 1 1 - 3 - 3 * ((4 / δ : ℕ) * t) * γ 1 1
  have hε (δ : ℕ) (hδ : δ ∈ (4 : ℕ).divisors) :
      etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) =
        (kroneckerSym ((4 / δ : ℕ) * t) (γ 1 1) : ℂ) * e24 (E δ) := by
    obtain ⟨h00, h01, h10, h11⟩ :=
      conjScaleGamma0_apply_of_eq (Nat.dvd_of_mem_divisors hδ) hγ ht
    rw [etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d _
      (by rw [h10]; exact mul_nonneg (Int.natCast_nonneg _) ht0) (by rw [h11]; exact hdo),
      h00, h01, h10, h11, e24_def]
  have hsum : ∑ δ ∈ (4 : ℕ).divisors, thetaExpVec δ * E δ = 3 * γ 1 1 - 3 := by
    have h1 : ∑ δ ∈ (4 : ℕ).divisors, ((4 / δ : ℕ) : ℤ) * thetaExpVec δ = 0 := by decide
    have h2 : ∑ δ ∈ (4 : ℕ).divisors, (δ : ℤ) * thetaExpVec δ = 0 := by decide
    rw [sum_mul_evenExp 4 thetaExpVec (γ 0 0) (γ 0 1) (γ 1 1) t, h1, h2,
      sum_divisors_four_thetaExpVec]
    ring
  rw [etaQuotientMultiplier_eq_prod thetaExpVec hγ hε, prod_mul_e24_zpow, hsum,
    prod_kroneckerSym_thetaExpVec ht, mul_right_comm,
    kroneckerSym_two_mul_e24_three_mul_sub_three hdo]

private lemma etaQuotientMultiplier_thetaExpVec (γ : Gamma0 4) :
    etaQuotientMultiplier 4 thetaExpVec γ =
      (thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1))⁻¹ *
        kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := by
  rcases le_or_gt 0 ((γ : SL(2, ℤ)) 1 0) with hc | hc
  · exact etaQuotientMultiplier_thetaExpVec_of_c_nonneg γ.property hc
  have hc_pos : 0 ≤ ((Gamma0.negOne 4 * γ : Gamma0 4) : SL(2, ℤ)) 1 0 := by
    simp only [Subgroup.coe_mul, Gamma0.coe_negOne, neg_one_mul,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    omega
  have hdo : Odd ((γ : SL(2, ℤ)) 1 1) := odd_apply_one_one_of_mem_Gamma0_four γ.property
  rw [etaQuotientMultiplier_of_c_neg 4 thetaExpVec γ hc, sum_divisors_four_thetaExpVec, zpow_one,
    etaQuotientMultiplier_thetaExpVec_of_c_nonneg (Gamma0.negOne 4 * γ).property hc_pos]
  simp only [Subgroup.coe_mul, Gamma0.coe_negOne, neg_one_mul,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [kroneckerSym_neg_neg_of_odd hc.ne hdo, ite_eq_left hc, one_mul, Int.cast_mul]
  have hphase : I * (thetaMultiplierPhase (-((γ : SL(2, ℤ)) 1 1)))⁻¹ *
      ((ZMod.χ₄ ((γ : SL(2, ℤ)) 1 1) : ℤ) : ℂ) =
      (thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1))⁻¹ := by
    have hmul := thetaMultiplierPhase_mul_neg hdo
    have hneg_ne : thetaMultiplierPhase (-((γ : SL(2, ℤ)) 1 1)) ≠ 0 :=
      thetaMultiplierPhase_ne_zero hdo.neg
    have hinv_neg : I * (thetaMultiplierPhase (-((γ : SL(2, ℤ)) 1 1)))⁻¹ =
        thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1) := by
      rw [← hmul, mul_assoc, mul_inv_cancel₀ hneg_ne, mul_one]
    rw [hinv_neg, ← thetaMultiplierPhase_sq]
    have hpow4 : thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1) ^ 4 = 1 := by
      calc thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1) ^ 4
          = (thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1) ^ 2) ^ 2 := by ring
        _ = 1 := by rw [thetaMultiplierPhase_sq, chi4_sq_eq_one_of_odd hdo]
    exact eq_inv_of_mul_eq_one_left (by rw [← hpow4]; ring)
  linear_combination (kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) : ℂ) * hphase

/-! ### The theta automorphy factor `j(γ, z)` on `SL(2, ℤ)` and `Γ₀(4)` -/

private lemma jacobiTheta_two_mul_ne_zero (z : ℍ) : jacobiTheta (2 * (z : ℂ)) ≠ 0 :=
  jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos)

/-- **The theta automorphy factor** `j(γ, z) = θ(2 · γ z) / θ(2 z)` for `γ ∈ SL(2, ℤ)` and
`z ∈ ℍ`. On `Γ₀(4)`, it equals Shimura's weight-`1/2` factor
`(thetaMultiplierPhase d)⁻¹ * kroneckerSym c d * Complex.sqrt (c z + d)`
(`thetaAutomorphyFactor_of_mem_Gamma0`), with the Kronecker symbol `TauCeti.kroneckerSym` and
principal square root `Complex.sqrt`. -/
noncomputable def thetaAutomorphyFactor (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ))

/-- Defining formula for `thetaAutomorphyFactor`. -/
theorem thetaAutomorphyFactor_def (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ z = jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ)) :=
  (rfl)

/-- For each `γ ∈ SL(2, ℤ)`, `z ↦ thetaAutomorphyFactor γ z` is holomorphic on `ℍ`. -/
theorem mdifferentiable_thetaAutomorphyFactor (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaAutomorphyFactor γ) := fun z ↦ by
  have hθ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ ↦ jacobiTheta (2 * (w : ℂ))) := fun w ↦ by
    have h2 : DifferentiableAt ℂ (fun y : ℂ ↦ jacobiTheta (2 * y)) (w : ℂ) :=
      (differentiableAt_jacobiTheta (by simpa using mul_pos two_pos w.im_pos)).comp (w : ℂ)
        ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)
    exact h2.mdifferentiableAt.comp w w.mdifferentiable_coe
  have hsmul : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ ↦ γ • w) := fun w ↦ by
    have h := UpperHalfPlane.mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ)
      (by simp) w
    simpa only [Matrix.SpecialLinearGroup.mapGL_smul] using h
  exact ((hθ.comp hsmul) z).div (hθ z) (jacobiTheta_two_mul_ne_zero z)

/-- The theta automorphy factor never vanishes on the upper half-plane. -/
@[simp]
theorem thetaAutomorphyFactor_ne_zero (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ z ≠ 0 :=
  div_ne_zero (jacobiTheta_two_mul_ne_zero (γ • z)) (jacobiTheta_two_mul_ne_zero z)

/-- Rewriting `θ(2 · γ z)` in terms of `thetaAutomorphyFactor γ z` and `θ(2 z)`. -/
theorem jacobiTheta_two_mul_smul_eq (γ : SL(2, ℤ)) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      thetaAutomorphyFactor γ z * jacobiTheta (2 * (z : ℂ)) :=
  (div_mul_cancel₀ _ (jacobiTheta_two_mul_ne_zero z)).symm

/-- **Cocycle law** for `thetaAutomorphyFactor` on all of `SL(2, ℤ)`:
`j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)`. -/
theorem thetaAutomorphyFactor_mul (γ₁ γ₂ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor (γ₁ * γ₂) z =
      thetaAutomorphyFactor γ₁ (γ₂ • z) * thetaAutomorphyFactor γ₂ z := by
  rw [thetaAutomorphyFactor_def, thetaAutomorphyFactor_def, thetaAutomorphyFactor_def,
    mul_smul, div_mul_div_cancel₀ (jacobiTheta_two_mul_ne_zero (γ₂ • z))]

@[simp]
theorem thetaAutomorphyFactor_one (z : ℍ) : thetaAutomorphyFactor 1 z = 1 := by
  rw [thetaAutomorphyFactor_def, one_smul, div_self (jacobiTheta_two_mul_ne_zero z)]

@[simp]
theorem thetaAutomorphyFactor_neg (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor (-γ) z = thetaAutomorphyFactor γ z := by
  have hsmul : (-γ) • z = γ • z :=
    ModularGroup.smul_eq_smul_of_eq_or_eq_neg (Or.inr rfl)
  rw [thetaAutomorphyFactor_def, hsmul, thetaAutomorphyFactor_def]

/-- Inversion formula for the theta automorphy factor:
`thetaAutomorphyFactor γ⁻¹ (γ • z) = (thetaAutomorphyFactor γ z)⁻¹`. -/
theorem thetaAutomorphyFactor_inv (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ⁻¹ (γ • z) = (thetaAutomorphyFactor γ z)⁻¹ := by
  have h := thetaAutomorphyFactor_mul γ⁻¹ γ z
  rw [inv_mul_cancel, thetaAutomorphyFactor_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- For `n : ℤ`, `ModularGroup.T ^ n` acts by `z ↦ z + n` with automorphy factor `1`. -/
@[simp]
theorem thetaAutomorphyFactor_T_zpow (n : ℤ) (z : ℍ) :
    thetaAutomorphyFactor (ModularGroup.T ^ n) z = 1 := by
  rw [thetaAutomorphyFactor_def, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    ofReal_intCast, mul_add, add_comm (2 * (n : ℂ)), mul_comm (2 : ℂ) (n : ℂ),
    (periodic_jacobiTheta_two.int_mul n) (2 * (z : ℂ)), div_self (jacobiTheta_two_mul_ne_zero z)]

/-- Unit-translation case: `ModularGroup.T` has automorphy factor `1`. -/
@[simp]
theorem thetaAutomorphyFactor_T (z : ℍ) : thetaAutomorphyFactor ModularGroup.T z = 1 := by
  simpa using thetaAutomorphyFactor_T_zpow 1 z

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
    mul_div_cancel_right₀ _ (jacobiTheta_two_mul_ne_zero z)]

/-- **Square of the theta automorphy factor on `Γ₀(4)`**:
`thetaAutomorphyFactor γ z ^ 2 = χ₄(d) · (c z + d)`. -/
theorem thetaAutomorphyFactor_sq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphyFactor γ z ^ 2 = (ZMod.χ₄ (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hdo : Odd (γ 1 1) := odd_apply_one_one_of_mem_Gamma0_four hγ
  have hcop : (γ 1 0).gcd (γ 1 1) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_row 1)
  have hχ_inv : ((ZMod.χ₄ (γ 1 1) : ℤ) : ℂ)⁻¹ = ZMod.χ₄ (γ 1 1) :=
    inv_eq_of_mul_eq_one_left (by rw [← sq, chi4_sq_eq_one_of_odd hdo])
  rw [thetaAutomorphyFactor_of_mem_Gamma0 hγ z, mul_pow, mul_pow, inv_pow,
    thetaMultiplierPhase_sq, hχ_inv, sq_intCast_kroneckerSym_eq_one hcop, mul_one,
    Complex.sq_sqrt]

/-- On `Γ₁(4)`, the square of the theta automorphy factor simplifies to `c z + d`. -/
theorem thetaAutomorphyFactor_sq_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 4) (z : ℍ) :
    thetaAutomorphyFactor γ z ^ 2 = (γ 1 0 : ℂ) * z + γ 1 1 := by
  have h := thetaAutomorphyFactor_sq_of_mem_Gamma0 (Gamma1_le_Gamma0 4 hγ) z
  have hd : (4 : ℤ) ∣ γ 1 1 - 1 := (mem_Gamma1_iff_dvd_lowerRow.mp hγ).2
  have hχ : ZMod.χ₄ (γ 1 1) = 1 :=
    ZMod.χ₄_int_one_mod_four (by obtain ⟨k, hk⟩ := hd; omega)
  rwa [hχ, Int.cast_one, one_mul] at h

end TauCeti
