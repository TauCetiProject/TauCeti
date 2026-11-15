/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Sqrt
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# The transformation of the Dedekind eta function under `SL(2, ℤ)`

This file proves the two generator laws of Mathlib's Dedekind eta function
`η(τ) = e^{2π i τ / 24} ∏_{n ≥ 1} (1 - qⁿ)` and its transformation under an arbitrary
`γ = (a b; c d) ∈ SL(2, ℤ)`:
* the translation law `η(τ + 1) = e^{π i / 12} η(τ)`, valid on all of `ℂ`;
* the inversion law `η(-1/τ) = √(-i τ) η(τ)` on the upper half-plane, with the principal
  square root, positive at `τ = i`; this is Mathlib's `ModularForm.eta_comp_eq_csqrt_I_inv`
  rewritten, since on the upper half-plane `√(-i τ) = (√i)⁻¹ √τ`;
* the eta multiplier `ε(γ)`, a 24th root of unity with `η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the
  upper half-plane, with the principal square root.

The existence of `ε(γ)` is proved without the Euclidean algorithm. The 24th power of
`τ ↦ η(γ τ) / (√(c τ + d) η(τ))` is `1` by the level-one modularity of `Δ = η²⁴`. This
quotient is continuous on the connected upper half-plane, because `c τ + d` is constant when
`c = 0` and otherwise avoids the real axis. So it is constant.

For `γ = (a b; c d)` with `d > 0`, right multiplication by `S` multiplies the
eta multiplier by `exp(-π i / 4)`. At `τ = i`, the new automorphy factor `-c + d i`
lies in the upper half-plane, controlling the principal square root. Together with the
translation laws and the initial case `c = 1` (`exp(π i ((a + d) / 12 - 1/4))`), this yields the
Euclidean uniqueness principle on `c > 0`, while the branch jump of `√(c τ + d)` under `γ ↦ -γ`
and the `±Tⁿ` description of upper-triangular elements settle negation, `c = 0`, and
lower-triangular transvections `(1 0; c 1)`.

## Main definitions

* `TauCeti.ModularForm.etaMultiplier γ`: the eta multiplier `ε(γ)`.

## Main results

* `TauCeti.ModularForm.eta_add_one`, `TauCeti.ModularForm.eta_add_intCast`: the translation law.
* `TauCeti.ModularForm.eta_neg_one_div`: the inversion law with the root `√(-i τ)`.
* `TauCeti.ModularForm.eta_smul`: `η(γ τ) = ε(γ) √(c τ + d) η(τ)` for `γ ∈ SL(2, ℤ)`.
* `TauCeti.ModularForm.etaMultiplier_pow_twentyFour`: `ε(γ)²⁴ = 1`.
* `TauCeti.ModularForm.etaMultiplier_eq_of_eta_smul_eq`: `ε(γ)` is determined by the
  transformation law at a single point.
* `TauCeti.ModularForm.etaMultiplier_T_zpow`, `TauCeti.ModularForm.etaMultiplier_S`,
  `TauCeti.ModularForm.etaMultiplier_neg_one`: `ε(Tⁿ) = e^{π i n / 12}`, `ε(S) = e^{-π i / 4}`
  and `ε(-1) = -i`.
* `TauCeti.ModularForm.etaMultiplier_mul_T_zpow`, `TauCeti.ModularForm.etaMultiplier_T_zpow_mul`:
  `ε(γ Tⁿ) = ε(Tⁿ γ) = e^{π i n / 12} ε(γ)`.
* `TauCeti.ModularForm.etaMultiplier_mul_S`: `ε(γ S) = e^{-π i / 4} ε(γ)` when `d > 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_one`: the explicit multiplier when `c = 1`.
* `TauCeti.ModularForm.etaMultiplier_eq_of_mul_T_zpow_of_mul_S_of_c_pos`: Euclidean induction
  principle for `ε(γ)` on `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`: `ε(-γ) = ±i ε(γ)` for `c ≷ 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_neg`: `ε(γ)` when `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_of_b_eq_zero_of_d_eq_one`: `ε((1 0; c 1)) = e^{-π i c / 12}`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, Theorems 3.1
  and 3.4.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### The two generator laws -/

/-- **The translation law of `η`**: `η(τ + n) = e^{π i n / 12} η(τ)` for every integer `n`. -/
theorem eta_add_intCast (τ : ℂ) (n : ℤ) : η (τ + n) = cexp (π * I * n / 12) * η τ := by
  have hq (m : ℕ) : _root_.ModularForm.eta_q m (τ + n) = _root_.ModularForm.eta_q m τ := by
    have harg : 2 * π * I * (m + 1) * (τ + n) =
        2 * π * I * (m + 1) * τ + ((m + 1) * n : ℤ) * (2 * π * I) := by
      push_cast
      ring
    simp only [_root_.ModularForm.eta_q_eq_cexp]
    rw [harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  have hexp : Function.Periodic.qParam 24 (τ + n) =
      cexp (π * I * n / 12) * Function.Periodic.qParam 24 τ := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [_root_.ModularForm.eta, hq, hexp, mul_assoc]

/-- **The translation law of `η`**: `η(τ + 1) = e^{π i / 12} η(τ)`. -/
theorem eta_add_one (τ : ℂ) : η (τ + 1) = cexp (π * I / 12) * η τ := by
  simpa using eta_add_intCast τ 1

/-- **The inversion law of `η`**: `η(-1/τ) = √(-i τ) η(τ)` on the upper half-plane, with the
principal square root, which is positive at `τ = i`. -/
theorem eta_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    η (-1 / τ) = Complex.sqrt (-I * τ) * η τ := by
  rw [Complex.sqrt_neg_I_mul hτ, mul_assoc]
  simpa using _root_.ModularForm.eta_comp_eq_csqrt_I_inv hτ

/-! ### The eta multiplier -/

/-- The automorphy factor `c τ + d` of `γ ∈ SL(2, ℤ)` does not vanish on the upper half-plane. -/
private theorem denom_ne_zero' (γ : SL(2, ℤ)) (τ : ℍ) : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
  simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ

private theorem sqrt_denom_mul_eta_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ ≠ 0 :=
  mul_ne_zero (Complex.sqrt_eq_zero_iff.not.2 (denom_ne_zero' γ τ))
    (_root_.ModularForm.eta_ne_zero τ.2)

/-- `Δ(γ τ) = (c τ + d)¹² Δ(τ)` for `γ ∈ SL(2, ℤ)`, in terms of `η`. -/
private theorem eta_smul_pow_twentyFour (γ : SL(2, ℤ)) (τ : ℍ) :
    η (γ • τ : ℍ) ^ 24 = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 * η τ ^ 24 := by
  have h := SlashInvariantForm.slash_action_eqn' CuspForm.discriminant
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ) (MonoidHom.mem_range.2 ⟨γ, rfl⟩) τ
  rw [MulAction.compHom_smul_def]
  simpa [_root_.ModularForm.discriminant] using h

/-- The quotient `η(γ τ) / (√(c τ + d) η(τ))`, constant in `τ` by `etaQuotient_eq`. -/
private noncomputable def etaQuotient (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  η (γ • τ : ℍ) / (Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ)

private theorem etaQuotient_pow_twentyFour (γ : SL(2, ℤ)) (τ : ℍ) :
    etaQuotient γ τ ^ 24 = 1 := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero τ.2
  have hs : Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 24 = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 :=
    (pow_mul _ 2 12).trans (congrArg (· ^ 12) (Complex.sq_sqrt _))
  rw [etaQuotient, div_pow, mul_pow, hs,
    eta_smul_pow_twentyFour, div_self (mul_ne_zero (pow_ne_zero _ (denom_ne_zero' γ τ))
      (pow_ne_zero _ hη))]

private theorem continuous_etaQuotient (γ : SL(2, ℤ)) : Continuous (etaQuotient γ) := by
  have hη : Continuous fun τ : ℍ ↦ η τ := continuous_iff_continuousAt.2 fun τ ↦
    (_root_.ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.2).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  have hγ : Continuous fun τ : ℍ ↦ γ • τ := by
    simp_rw [MulAction.compHom_smul_def]
    exact continuous_const_smul _
  have hs : Continuous fun τ : ℍ ↦ Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    simpa using UpperHalfPlane.continuous_sqrt_ofReal_mul_add (γ 1 0) (γ 1 1)
  exact (hη.comp hγ).div (hs.mul hη) (sqrt_denom_mul_eta_ne_zero γ)

/-- The quotient `η(γ τ) / (√(c τ + d) η(τ))` is independent of `τ`: it is a continuous function
on the connected upper half-plane with values in the finite set of 24th roots of unity. -/
private theorem etaQuotient_eq (γ : SL(2, ℤ)) (τ τ' : ℍ) :
    etaQuotient γ τ = etaQuotient γ τ' := by
  let R : Set ℂ := ((Polynomial.nthRoots 24 (1 : ℂ)).toFinset : Set ℂ)
  refine isPreconnected_univ.constant_of_mapsTo (Finset.finite_toSet _).isDiscrete
    (continuous_etaQuotient γ).continuousOn (T := R) (fun σ _ ↦ ?_) (Set.mem_univ τ)
    (Set.mem_univ τ')
  simpa [R, Polynomial.mem_nthRoots] using etaQuotient_pow_twentyFour γ σ

/-- **The eta multiplier** `ε(γ)` of `γ = (a b; c d) ∈ SL(2, ℤ)`: the constant with
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane, with the principal square root
(`eta_smul`). It is a 24th root of unity (`etaMultiplier_pow_twentyFour`). -/
noncomputable def etaMultiplier (γ : SL(2, ℤ)) : ℂ :=
  etaQuotient γ UpperHalfPlane.I

/-- **The transformation law of `η` under `SL(2, ℤ)`**: for `γ = (a b; c d)`,
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane, with the principal square root. -/
theorem eta_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    η (γ • τ : ℍ) = etaMultiplier γ * Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [etaMultiplier, ← etaQuotient_eq γ τ, etaQuotient, mul_assoc,
    div_mul_cancel₀ _ (sqrt_denom_mul_eta_ne_zero γ τ)]

/-- The eta multiplier is a 24th root of unity. -/
theorem etaMultiplier_pow_twentyFour (γ : SL(2, ℤ)) : etaMultiplier γ ^ 24 = 1 :=
  etaQuotient_pow_twentyFour γ _

/-- The eta multiplier is determined by the transformation law of `η` at a single point. -/
theorem etaMultiplier_eq_of_eta_smul_eq {γ : SL(2, ℤ)} {ε : ℂ} {τ : ℍ}
    (h : η (γ • τ : ℍ) = ε * Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ) :
    etaMultiplier γ = ε := by
  rw [eta_smul, mul_assoc, mul_assoc] at h
  exact mul_right_cancel₀ (sqrt_denom_mul_eta_ne_zero γ τ) h

/-- `ε(1) = 1`. -/
@[simp]
theorem etaMultiplier_one : etaMultiplier 1 = 1 :=
  etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) (by simp)

/-- `ε(-1) = -i`: the identity transformation with the automorphy factor `-1`, whose
principal root is `i`. -/
@[simp]
theorem etaMultiplier_neg_one : etaMultiplier (-1) = -I := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  simp [Complex.sqrt_neg_one]

/-- `ε(Tⁿ) = e^{π i n / 12}`, by the translation law. -/
@[simp]
theorem etaMultiplier_T_zpow (n : ℤ) : etaMultiplier (T ^ n) = cexp (π * I * n / 12) := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  rw [coe_T_zpow_smul_eq, eta_add_intCast]
  simp [coe_T_zpow]

/-- `ε(T) = e^{π i / 12}`, by the translation law. -/
@[simp]
theorem etaMultiplier_T : etaMultiplier T = cexp (π * I / 12) := by
  simpa using etaMultiplier_T_zpow 1

/-- `ε(S) = e^{-π i / 4}` for `S = (0 -1; 1 0)`, with the root `√τ` of the automorphy factor `τ`,
by the inversion law. -/
@[simp]
theorem etaMultiplier_S : etaMultiplier S = cexp (-(π * I / 4)) := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hS : ((S • UpperHalfPlane.I : ℍ) : ℂ) = -1 / (UpperHalfPlane.I : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [neg_div]
  rw [hS, eta_neg_one_div (by simp), Complex.sqrt_neg_I_mul (by simp), Complex.sqrt_I_eq_exp,
    ← Complex.exp_neg]
  simp [coe_S]

/-- `ε(γ Tⁿ) = e^{π i n / 12} ε(γ)`: right translation by `Tⁿ` replaces `τ` by `τ + n`. -/
theorem etaMultiplier_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) :
    etaMultiplier (γ * T ^ n) = cexp (π * I * n / 12) * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hτ : 0 < ((UpperHalfPlane.I : ℂ) + n).im := by simp
  have h := eta_smul γ ⟨(UpperHalfPlane.I : ℂ) + n, hτ⟩
  have hsmul : (γ * T ^ n) • UpperHalfPlane.I = γ • (⟨(UpperHalfPlane.I : ℂ) + n, hτ⟩ : ℍ) := by
    rw [mul_smul]
    congr 1
    ext
    exact coe_T_zpow_smul_eq _
  rw [hsmul, h, γ.mul_T_zpow_apply_one_zero, γ.mul_T_zpow_apply_one_one]
  simp only [eta_add_intCast, Int.cast_add, Int.cast_mul]
  rw [mul_add, add_assoc]
  ring

/-- `ε(γ T) = e^{π i / 12} ε(γ)`. -/
theorem etaMultiplier_mul_T (γ : SL(2, ℤ)) :
    etaMultiplier (γ * T) = cexp (π * I / 12) * etaMultiplier γ := by
  simpa using etaMultiplier_mul_T_zpow γ 1

/-- `ε(Tⁿ γ) = e^{π i n / 12} ε(γ)`: left translation by `Tⁿ` replaces `γ τ` by `γ τ + n`. -/
theorem etaMultiplier_T_zpow_mul (γ : SL(2, ℤ)) (n : ℤ) :
    etaMultiplier (T ^ n * γ) = cexp (π * I * n / 12) * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  rw [mul_smul, coe_T_zpow_smul_eq, eta_add_intCast, eta_smul, T_pow_mul_apply_one]
  ring

/-- `ε(T γ) = e^{π i / 12} ε(γ)`. -/
theorem etaMultiplier_T_mul (γ : SL(2, ℤ)) :
    etaMultiplier (T * γ) = cexp (π * I / 12) * etaMultiplier γ := by
  simpa using etaMultiplier_T_zpow_mul γ 1

/-- Right inversion multiplies the eta multiplier by `exp(-π i / 4)` when the
lower-right entry is positive. No sign condition on the lower-left entry is needed. -/
theorem etaMultiplier_mul_S (γ : SL(2, ℤ)) (hd : 0 < γ 1 1) :
    etaMultiplier (γ * S) = cexp (-(π * I / 4)) * etaMultiplier γ := by
  have hpos : 0 < ((γ 1 1 : ℂ) * I - γ 1 0).im := by
    simpa using (Int.cast_pos.mpr hd : (0 : ℝ) < γ 1 1)
  have hroot := Complex.sqrt_neg_I_mul hpos
  have hrotate : -I * ((γ 1 1 : ℂ) * I - γ 1 0) = (γ 1 0 : ℂ) * I + γ 1 1 := by
    ring_nf
    simp
  rw [hrotate, Complex.sqrt_I_eq_exp, ← Complex.exp_neg] at hroot
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hfixed : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    simp
  rw [mul_smul, hfixed, eta_smul, γ.mul_S_apply_one_zero, γ.mul_S_apply_one_one]
  simp only [UpperHalfPlane.coe_I, Int.cast_neg, ← sub_eq_add_neg]
  rw [hroot]
  ring

/-- If the lower-left entry is `1`, the eta multiplier is
`exp(π i ((a + d) / 12 - 1/4))`. This is the initial case of its Dedekind-sum formula. -/
theorem etaMultiplier_of_c_eq_one (γ : SL(2, ℤ)) (hc : γ 1 0 = 1) :
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / 12 - 1 / 4)) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_one] at hdet
  have hfactor : γ = T ^ (γ 0 0) * S * T ^ (γ 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_S,
        Matrix.mul_apply, Fin.sum_univ_two, hc]
    omega
  rw [congrArg etaMultiplier hfactor, etaMultiplier_mul_T_zpow,
    etaMultiplier_T_zpow_mul, etaMultiplier_S,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- Euclidean strong induction on `c = γ 1 0 > 0`: any function `F : SL(2, ℤ) → ℂ` that agrees with
`etaMultiplier` at `(a b; 1 0)` and transforms like `etaMultiplier` under right multiplication by
`T ^ n` and `S` (when `c, d > 0`) agrees with `etaMultiplier` on `{γ | 0 < γ 1 0}`. -/
theorem etaMultiplier_eq_of_mul_T_zpow_of_mul_S_of_c_pos {F : SL(2, ℤ) → ℂ}
    (hbase : ∀ γ : SL(2, ℤ), γ 1 0 = 1 → γ 1 1 = 0 → etaMultiplier γ = F γ)
    (hT : ∀ (γ : SL(2, ℤ)) (n : ℤ), 0 < γ 1 0 → F (γ * T ^ n) = cexp (π * I * n / 12) * F γ)
    (hS : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → 0 < γ 1 1 → cexp (π * I / 4) * F (γ * S) = F γ)
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = F γ := by
  suffices ∀ (n : ℕ) (γ : SL(2, ℤ)), γ 1 0 = n → 0 < n → etaMultiplier γ = F γ from
    this (γ 1 0).toNat γ (Int.toNat_of_nonneg hc.le).symm (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro γ hcn hn
    have hc : 0 < γ 1 0 := by omega
    let q : ℤ := γ 1 1 / γ 1 0
    let γ₁ : SL(2, ℤ) := γ * T ^ (-q)
    have hγ : γ = γ₁ * T ^ q := by simp [γ₁, mul_assoc, zpow_neg]
    have hc₁ : γ₁ 1 0 = γ 1 0 := γ.mul_T_zpow_apply_one_zero (-q)
    have hr : γ₁ 1 1 = γ 1 1 % γ 1 0 := by
      rw [γ.mul_T_zpow_apply_one_one (-q), Int.emod_def]
      ring
    have hr_nonneg : 0 ≤ γ₁ 1 1 := hr ▸ Int.emod_nonneg _ hc.ne'
    have hr_lt : γ₁ 1 1 < γ 1 0 := hr ▸ Int.emod_lt_of_pos _ hc
    rw [hγ, etaMultiplier_mul_T_zpow, hT γ₁ q (hc₁ ▸ hc)]
    congr 1
    rcases hr_nonneg.eq_or_lt with hr0 | hr_pos
    · exact hbase γ₁
        (Matrix.SpecialLinearGroup.apply_one_zero_eq_one_of_nonneg_of_apply_one_one_eq_zero
          (hc₁ ▸ hc.le) hr0.symm) hr0.symm
    · have hm : (γ₁ * S) 1 0 = (γ₁ 1 1).toNat := by
        rw [γ₁.mul_S_apply_one_zero, Int.toNat_of_nonneg hr_pos.le]
      have ihS := ih (γ₁ 1 1).toNat (by omega) (γ₁ * S) hm (by omega)
      have hcancel : cexp (π * I / 4) * etaMultiplier (γ₁ * S) = etaMultiplier γ₁ := by
        rw [etaMultiplier_mul_S γ₁ hr_pos, ← mul_assoc, ← Complex.exp_add]
        simp
      rw [← hcancel, ihS, hS γ₁ (hc₁ ▸ hc) hr_pos]

/-! ### Negation `-γ`, upper-triangular elements (`c = 0`), and lower transvections -/

/-- For `γ ∈ SL(2, ℤ)` with `c > 0`, negating `γ` multiplies `ε(γ)` by `i`: `-γ` acts as `γ` on
the upper half-plane while `√(-c τ - d) = -i √(c τ + d)`. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have him : 0 < ((γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1).im := by
    simpa using (Int.cast_pos.mpr hc : (0 : ℝ) < γ 1 0)
  have hneg : ((-γ) 1 0 : ℂ) * UpperHalfPlane.I + (-γ) 1 1 =
      -((γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1) := by
    simp [neg_add_rev, add_comm]
  rw [SL_neg_smul, eta_smul, hneg, Complex.sqrt_neg_of_im_pos him]
  linear_combination etaMultiplier γ * Complex.sqrt ((γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1) *
    η UpperHalfPlane.I * I_sq

/-- For `γ ∈ SL(2, ℤ)` with `c < 0`, negating `γ` multiplies `ε(γ)` by `-i`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  linear_combination I * h + etaMultiplier (-γ) * I_sq

/-- An upper-triangular element `(1 b; 0 1) ∈ SL(2, ℤ)` has `ε(γ) = e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ
  · rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow]
  · exfalso
    have hd1 : γ 1 1 = -1 := by
      simpa [coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 1 1) hγ
    omega

/-- An upper-triangular element `(-1 b; 0 -1) ∈ SL(2, ℤ)` has `ε(γ) = -i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ
  · exfalso
    have hd1 : γ 1 1 = 1 := by
      simpa [coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 1 1) hγ
    omega
  · rw [congrArg etaMultiplier hγ, ← neg_one_mul, etaMultiplier_mul_T_zpow, etaMultiplier_neg_one]
    simp only [Int.cast_neg, mul_neg, neg_div]
    ring

/-- For any upper-triangular `γ ∈ SL(2, ℤ)` (`c = 0`), `ε(γ)` is `e^{π i b / 12}` when `d > 0`
and `-i e^{-π i b / 12}` when `d < 0`. -/
theorem etaMultiplier_of_c_eq_zero (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    etaMultiplier γ =
      if 0 < γ 1 1 then cexp (π * I * γ 0 1 / 12) else -I * cexp (-(π * I * γ 0 1 / 12)) := by
  split_ifs with hd
  · exact etaMultiplier_of_c_eq_zero_of_d_pos γ hc hd
  · have hdet := γ.fin_two_mul_sub_mul_eq_one
    rw [hc, mul_zero, sub_zero] at hdet
    exact etaMultiplier_of_c_eq_zero_of_d_neg γ hc
      (lt_of_le_of_ne (not_lt.mp hd) (by rintro h0; rw [h0, mul_zero] at hdet; norm_num at hdet))

/-- Every lower-triangular transvection `(1 0; c 1) ∈ SL(2, ℤ)` has `ε(γ) = e^{-π i c / 12}`, for
all `c ∈ ℤ` (positive, zero, or negative). -/
theorem etaMultiplier_of_b_eq_zero_of_d_eq_one (γ : SL(2, ℤ)) (hb : γ 0 1 = 0) (hd : γ 1 1 = 1) :
    etaMultiplier γ = cexp (-(π * I * γ 1 0 / 12)) := by
  have ha : γ 0 0 = 1 := by simpa [hb, hd] using γ.fin_two_mul_sub_mul_eq_one
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · have hfac : -γ = S * T ^ (-γ 1 0) * S := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T_zpow, ha, hb, hd]
    have hd_pos : 0 < (S * T ^ (-γ 1 0)) 1 1 := by
      rw [S.mul_T_zpow_apply_one_one]
      simpa [coe_S] using hc
    have hlhs := etaMultiplier_neg_of_c_neg γ hc
    rw [congrArg etaMultiplier hfac, etaMultiplier_mul_S _ hd_pos, etaMultiplier_mul_T_zpow,
      etaMultiplier_S] at hlhs
    have hrot : cexp (-(π * I / 4)) * (cexp (π * I * ↑(-γ 1 0) / 12) * cexp (-(π * I / 4))) =
        -I * cexp (-(π * I * γ 1 0 / 12)) := by
      rw [mul_left_comm, ← Complex.exp_add,
        show -(π * I / 4) + -(π * I / 4) = -(π / 2 * I) by ring, Complex.exp_neg,
        exp_pi_div_two_mul_I, inv_I]
      simp only [Int.cast_neg, mul_neg, neg_div]
      ring
    rw [hrot] at hlhs
    exact mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) hlhs.symm
  · have hγ1 : γ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    rw [congrArg etaMultiplier hγ1, etaMultiplier_one, hc]
    simp
  · have hfac : γ = (-S) * T ^ (-γ 1 0) * S := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T_zpow, ha, hb, hd]
    have hd_pos : 0 < ((-S) * T ^ (-γ 1 0)) 1 1 := by
      rw [(-S).mul_T_zpow_apply_one_one]
      simpa [coe_S] using hc
    have hnegS : etaMultiplier (-S) = cexp (π * I / 4) := by
      calc
        etaMultiplier (-S) = I * cexp (-(π * I / 4)) := by
          rw [etaMultiplier_neg_of_c_pos S (by decide), etaMultiplier_S]
        _ = cexp (π / 2 * I) * cexp (-(π * I / 4)) :=
          congrArg (· * cexp (-(π * I / 4))) exp_pi_div_two_mul_I.symm
        _ = cexp (π * I / 4) := by rw [← Complex.exp_add]; congr 1; ring
    rw [congrArg etaMultiplier hfac, etaMultiplier_mul_S _ hd_pos, etaMultiplier_mul_T_zpow,
      hnegS, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    simp [neg_div]

end TauCeti.ModularForm
