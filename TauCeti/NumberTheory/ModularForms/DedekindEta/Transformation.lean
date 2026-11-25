/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import TauCeti.NumberTheory.DedekindSum
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Sqrt
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.Modular.Reduction

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
translation laws, this is the inversion step in the Euclidean calculation of the multiplier, and
also shows that negating `γ` multiplies `ε(γ)` by `i` when `c > 0` and by `-i` when `c < 0`.
When `c > 0` and `d < 0`, right multiplication by `S` multiplies `ε` by `-exp(-π i / 4)`.
When `c = 0` (`γ = ±T^{±b}`), `ε(γ)` is `e^{π i b / 12}` for `d > 0` and `-i e^{-π i b / 12}`
for `d < 0`; when `c = 1`, `ε(γ) = exp(π i ((a + d) / 12 - 1/4))`; and when `c ≠ 0`, `c i + d`
avoids the branch cut of the principal square root so `ε(γ⁻¹) = ε(γ)⁻¹`.

For `c > 0` the multiplier is `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, with the
Dedekind sum `s(d, c)`. This is proved by strong induction on `c`, along the Euclidean
algorithm: a translation `γ Tⁿ` reduces `d` modulo `c`, matched by `s(c n + d, c) = s(d, c)`, and
for `0 < d < c` the inversion step passes to `γ S = (b -a; d -c)`, with smaller lower-left entry,
matched by the reciprocity law of Dedekind sums.

## Main definitions

* `TauCeti.ModularForm.etaMultiplier γ`: the eta multiplier `ε(γ)`.

## Main results

* `TauCeti.ModularForm.eta_add_one`, `TauCeti.ModularForm.eta_add_intCast`: the translation law.
* `TauCeti.ModularForm.eta_neg_one_div`: the inversion law with the root `√(-i τ)`.
* `TauCeti.ModularForm.eta_smul`: `η(γ τ) = ε(γ) √(c τ + d) η(τ)` for `γ ∈ SL(2, ℤ)`.
* `TauCeti.ModularForm.etaMultiplier_pow_twentyFour`,
  `TauCeti.ModularForm.etaMultiplier_ne_zero`, `TauCeti.ModularForm.norm_etaMultiplier`:
  `ε(γ)²⁴ = 1`, `ε(γ) ≠ 0`, and `‖ε(γ)‖ = 1`.
* `TauCeti.ModularForm.etaMultiplier_eq_of_eta_smul_eq`: `ε(γ)` is determined by the
  transformation law at a single point.
* `TauCeti.ModularForm.etaMultiplier_T_zpow`, `TauCeti.ModularForm.etaMultiplier_S`,
  `TauCeti.ModularForm.etaMultiplier_neg_one`: `ε(Tⁿ) = e^{π i n / 12}`, `ε(S) = e^{-π i / 4}`
  and `ε(-1) = -i`.
* `TauCeti.ModularForm.etaMultiplier_mul_T_zpow`, `TauCeti.ModularForm.etaMultiplier_T_zpow_mul`:
  `ε(γ Tⁿ) = ε(Tⁿ γ) = e^{π i n / 12} ε(γ)`.
* `TauCeti.ModularForm.etaMultiplier_mul_S`: `ε(γ S) = e^{-π i / 4} ε(γ)` when `d > 0`.
* `TauCeti.ModularForm.etaMultiplier_mul_S_of_c_pos_of_d_neg`: `ε(γ S) = -e^{-π i / 4} ε(γ)` when
  `c > 0` and `d < 0`.
* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`: `ε(-γ) = i ε(γ)` for `c > 0` and
  `ε(-γ) = -i ε(γ)` for `c < 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_neg`: explicit values when `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_one`: the explicit multiplier when `c = 1`.
* `TauCeti.ModularForm.etaMultiplier_inv_of_c_ne_zero`: `ε(γ⁻¹) = ε(γ)⁻¹` when `c ≠ 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_pos`: the Dedekind-sum value of the multiplier when
  `c > 0`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, Theorems 3.1
  and 3.4.
-/

public section

open Complex ModularGroup TauCeti.ModularGroup
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

private theorem sqrt_denom_mul_eta_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ ≠ 0 :=
  mul_ne_zero (UpperHalfPlane.sqrt_denom_ne_zero γ τ) (_root_.ModularForm.eta_ne_zero τ.coe_im_pos)

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
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero τ.coe_im_pos
  have hden : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  have hs : Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 24 = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 :=
    (pow_mul _ 2 12).trans (congrArg (· ^ 12) (Complex.sq_sqrt _))
  rw [etaQuotient, div_pow, mul_pow, hs,
    eta_smul_pow_twentyFour, div_self (mul_ne_zero (pow_ne_zero _ hden) (pow_ne_zero _ hη))]

private theorem continuous_etaQuotient (γ : SL(2, ℤ)) : Continuous (etaQuotient γ) := by
  have hη : Continuous fun τ : ℍ ↦ η τ := continuous_iff_continuousAt.2 fun τ ↦
    (_root_.ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
        τ.coe_im_pos).continuousAt.comp
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

/-- The eta multiplier never vanishes. -/
@[simp]
theorem etaMultiplier_ne_zero (γ : SL(2, ℤ)) : etaMultiplier γ ≠ 0 := by
  intro h
  have h24 := etaMultiplier_pow_twentyFour γ
  simp [h] at h24

/-- The eta multiplier has unit norm, since its 24th power is `1`. -/
@[simp]
theorem norm_etaMultiplier (γ : SL(2, ℤ)) : ‖etaMultiplier γ‖ = 1 :=
  norm_eq_one_of_pow_eq_one (etaMultiplier_pow_twentyFour γ) (by decide)

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
  rw [hsmul, h, mul_T_zpow_apply_apply_zero, mul_T_zpow_apply_apply_one]
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
  rw [mul_smul, hfixed, eta_smul, mul_S_apply_apply_zero, mul_S_apply_apply_one]
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

/-! ### The Dedekind-sum value of the eta multiplier -/

/-- The Dedekind-sum formula for `ε(γ)` is preserved in both directions under `γ ↦ γ T`: both
sides gain the factor `e^{π i / 12}`, since `s(c + d, c) = s(d, c)`. -/
private theorem etaMultiplier_eq_iff_of_mul_T (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier (γ * T) = cexp (π * I * ((((γ * T) 0 0 : ℂ) + (γ * T) 1 1) /
      (12 * (γ * T) 1 0) - dedekindSum ((γ * T) 1 1) ((γ * T) 1 0) - 1 / 4)) ↔
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
      dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  have h00 : (γ * T) 0 0 = γ 0 0 := by rw [γ.coe_mul_T]; simp
  have h10 : (γ * T) 1 0 = γ 1 0 := by rw [γ.coe_mul_T]; simp
  have h11 : (γ * T) 1 1 = γ 1 0 + γ 1 1 := by rw [γ.coe_mul_T]; simp
  rw [etaMultiplier_mul_T, h00, h10, h11, dedekindSum_self_add]
  push_cast
  have hexp :
      π * I * (((γ 0 0 : ℂ) + ((γ 1 0 : ℂ) + γ 1 1)) / (12 * γ 1 0) -
        dedekindSum (γ 1 1) (γ 1 0) - 1 / 4) =
      π * I / 12 + π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
        dedekindSum (γ 1 1) (γ 1 0) - 1 / 4) := by
    have hc'' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
    field_simp
    ring
  rw [hexp, Complex.exp_add, mul_right_inj' (Complex.exp_ne_zero _)]

/-- The Dedekind-sum formula for `ε(γ)` passes from `γ S` to `γ` when `c, d > 0`: the inversion
step contributes `e^{-π i / 4}`, and the change of the Dedekind sums from `s(-c, d)` to `s(d, c)`
is the reciprocity law, with `a d - b c = 1`. -/
private theorem etaMultiplier_eq_of_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1)
    (h : etaMultiplier (γ * S) = cexp (π * I * ((((γ * S) 0 0 : ℂ) + (γ * S) 1 1) /
      (12 * (γ * S) 1 0) - dedekindSum ((γ * S) 1 1) ((γ * S) 1 0) - 1 / 4))) :
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
      dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hcop := (γ.isCoprime_row 1).symm
  have hrec := dedekindSum_add_dedekindSum hd hc hcop
  -- The exponents agree in `ℚ`, by the reciprocity law and `a d - b c = 1`.
  have hexp : ((γ 0 1 - γ 1 0 : ℤ) : ℚ) / (12 * γ 1 1) + dedekindSum (γ 1 0) (γ 1 1) =
      ((γ 0 0 + γ 1 1 : ℤ) : ℚ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4 := by
    have hc'' : (γ 1 0 : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd'' : (γ 1 1 : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [eq_sub_of_add_eq' hrec]
    have hdetq : (γ 0 0 : ℚ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
    push_cast
    field_simp
    linear_combination (-4 : ℚ) * hdetq
  rw [etaMultiplier_mul_S γ hd, mul_S_apply_apply_zero, mul_S_apply_apply_zero,
    mul_S_apply_apply_one, dedekindSum_neg] at h
  rw [← mul_right_inj' (Complex.exp_ne_zero (-(π * I / 4))), h, ← Complex.exp_add]
  congr 1
  have hexpC := congrArg (fun x : ℚ ↦ (x : ℂ)) hexp
  push_cast at hexpC ⊢
  linear_combination π * I * hexpC

/-- **The Dedekind-sum value of the eta multiplier** (Apostol, Theorem 3.4): for
`γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where `s(d, c)` is the Dedekind sum.
Apostol's formula is stated for the root `√(-i (c τ + d))`; the `-1/4` converts it to the
principal root `√(c τ + d)` of `eta_smul`. -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
      dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  refine Matrix.SpecialLinearGroup.induction_on_of_c_pos γ hc
    (P := fun δ ↦ etaMultiplier δ = cexp (π * I * (((δ 0 0 : ℂ) + δ 1 1) / (12 * δ 1 0) -
      dedekindSum (δ 1 1) (δ 1 0) - 1 / 4))) ?_ ?_ ?_
  · intro δ h1
    rw [etaMultiplier_of_c_eq_one δ h1, h1]
    simp
  · exact fun δ hδ ↦ etaMultiplier_eq_iff_of_mul_T δ hδ.ne'
  · exact fun δ hδc hδd ↦ etaMultiplier_eq_of_mul_S δ hδc hδd

/-- When `c > 0`, negating `γ ∈ SL(2, ℤ)` multiplies the eta multiplier by `i`:
`ε(-γ) = i ε(γ)`. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  -- Shift on the right by `T ^ (-n)` so the lower-right entry becomes negative; then both `-γ'`
  -- and `(-γ') * S` have positive lower-right entry, so `etaMultiplier_mul_S` applies twice.
  let n : ℤ := |γ 1 1| + 1
  let γ' : SL(2, ℤ) := γ * T ^ (-n)
  have hn_pos : 0 < n := by have := abs_nonneg (γ 1 1); omega
  have hγ'10 : γ' 1 0 = γ 1 0 := by dsimp only [γ']; rw [γ.coe_mul_T_zpow]; simp
  have hγ'11 : γ' 1 1 = γ 1 0 * (-n) + γ 1 1 := by dsimp only [γ']; rw [γ.coe_mul_T_zpow]; simp
  have hγ'11_neg : γ' 1 1 < 0 := by
    have hle : γ 1 1 ≤ |γ 1 1| := le_abs_self _
    have hmul : n ≤ γ 1 0 * n := le_mul_of_one_le_left hn_pos.le hc
    linarith [hγ'11, mul_neg (γ 1 0) n]
  have hd1 : 0 < (-γ') 1 1 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
    exact hγ'11_neg
  have hd2 : 0 < ((-γ') * S) 1 1 := by
    rw [(-γ').coe_mul_S]
    simpa [hγ'10] using hc
  have hS1 := etaMultiplier_mul_S (-γ') hd1
  have hS2 := etaMultiplier_mul_S ((-γ') * S) hd2
  have hSS : ((-γ') * S) * S = γ' := by
    rw [mul_assoc, ← sq, TauCeti.ModularGroup.S_sq, mul_neg_one, neg_neg]
  rw [hSS, hS1, ← mul_assoc, ← Complex.exp_add] at hS2
  have hexp : cexp (-(π * I / 4) + -(π * I / 4)) = -I := by
    have harg : -(π * I / 4) + -(π * I / 4) = -(π / 2 * I) := by ring
    rw [harg, Complex.exp_neg, exp_pi_div_two_mul_I, inv_I]
  rw [hexp] at hS2
  have hγ' : etaMultiplier (-γ') = I * etaMultiplier γ' := by rw [hS2, ← mul_assoc]; simp
  have hrestore : γ' * T ^ n = γ := by simp [γ', mul_assoc]
  have hrestore_neg : (-γ') * T ^ n = -γ := by rw [neg_mul, hrestore]
  rw [← hrestore_neg, etaMultiplier_mul_T_zpow, hγ', ← mul_left_comm, ← etaMultiplier_mul_T_zpow,
    hrestore]

/-- When `c < 0`, negating `γ ∈ SL(2, ℤ)` multiplies the eta multiplier by `-i`:
`ε(-γ) = -i ε(γ)`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have hc' : 0 < (-γ) 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
    exact hc
  have h := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg] at h
  rw [h, ← mul_assoc]
  simp

/-- Right inversion multiplies the eta multiplier by `-exp(-π i / 4)` when `c > 0` and `d < 0`.
This complements `etaMultiplier_mul_S`, where `d > 0` gives the factor `exp(-π i / 4)`. -/
theorem etaMultiplier_mul_S_of_c_pos_of_d_neg (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : γ 1 1 < 0) :
    etaMultiplier (γ * S) = -cexp (-(π * I / 4)) * etaMultiplier γ := by
  have hd' : 0 < (-γ) 1 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff] using hd
  have hc' : (γ * S) 1 0 < 0 := by rwa [mul_S_apply_apply_zero]
  -- `-(γ S) = (-γ) S`, and `-γ` has positive lower-right entry.
  have h := etaMultiplier_mul_S (-γ) hd'
  rw [neg_mul, etaMultiplier_neg_of_c_neg (γ * S) hc', etaMultiplier_neg_of_c_pos γ hc] at h
  rw [← mul_right_inj' (neg_ne_zero.mpr I_ne_zero), h]
  ring

/-- Explicit eta multiplier when `c = 0` and `d > 0`: then `γ = T ^ b` and
`ε(γ) = e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ
  · rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow]
  · exfalso
    have hd' : γ 1 1 = -1 := by
      simpa [coe_T_zpow] using congrArg (fun B : SL(2, ℤ) ↦ B 1 1) hγ
    omega

/-- Explicit eta multiplier when `c = 0` and `d < 0`: then `γ = -T ^ (-b)` and
`ε(γ) = -i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ
  · exfalso
    have hd' : γ 1 1 = 1 := by
      simpa [coe_T_zpow] using congrArg (fun B : SL(2, ℤ) ↦ B 1 1) hγ
    omega
  · have hγ' : γ = T ^ (-γ 0 1) * (-1 : SL(2, ℤ)) := hγ.trans (mul_neg_one _).symm
    have harg : π * I * -(γ 0 1 : ℂ) / 12 = -(π * I * γ 0 1 / 12) := by ring
    rw [congrArg etaMultiplier hγ', etaMultiplier_T_zpow_mul, etaMultiplier_neg_one, Int.cast_neg,
      harg, mul_comm]

/-- When `c ≠ 0`, the eta multiplier of `γ⁻¹` is the inverse of the eta multiplier of `γ`:
`ε(γ⁻¹) = ε(γ)⁻¹`. The hypothesis `c ≠ 0` cannot be dropped altogether: when `c = 0`, the
identity holds for `d > 0` (`γ = T ^ b`) and fails for `d < 0` (e.g. at `γ = -1`, where
`ε(-1) = -i ≠ i = ε(-1)⁻¹`). -/
theorem etaMultiplier_inv_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ := by
  let τ : ℍ := UpperHalfPlane.I
  set w : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1 with hw_def
  set w' : ℂ := ((γ⁻¹ : SL(2, ℤ)) 1 0 : ℂ) * (γ • τ : ℍ) + (γ⁻¹ : SL(2, ℤ)) 1 1 with hw'_def
  have hcocycle : w' * w = 1 := by
    have h := Matrix.SpecialLinearGroup.denom_mapGL_mul γ⁻¹ γ τ
    rw [inv_mul_cancel, map_one, UpperHalfPlane.denom_one, ModularGroup.denom_mapGL,
      ModularGroup.denom_mapGL] at h
    exact h.symm
  have hw' : w' = w⁻¹ := eq_inv_of_mul_eq_one_left hcocycle
  have hw_im : w.im ≠ 0 := by simpa [hw_def, τ] using hc
  have hw_arg : w.arg ≠ π := fun harg ↦ hw_im (Complex.arg_eq_pi_iff.mp harg).2
  have hsqrt : Complex.sqrt w' = (Complex.sqrt w)⁻¹ := by
    rw [hw', Complex.sqrt, Complex.inv_cpow w (2⁻¹ : ℂ) hw_arg, ← Complex.sqrt]
  refine etaMultiplier_eq_of_eta_smul_eq (τ := γ • τ) ?_
  have hsqrt_ne : Complex.sqrt w ≠ 0 := UpperHalfPlane.sqrt_denom_ne_zero γ τ
  rw [inv_smul_smul, ← hw'_def, hsqrt, eta_smul γ τ, ← hw_def]
  field_simp [etaMultiplier_ne_zero γ, hsqrt_ne]

end TauCeti.ModularForm
