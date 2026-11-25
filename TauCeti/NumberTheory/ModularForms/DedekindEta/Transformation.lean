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
translation laws, this is the inversion step in the Euclidean calculation of the multiplier. When
`c > 0` and `d < 0`, right multiplication by `S` multiplies `ε` by `-exp(-π i / 4)`. The file also
evaluates `ε(γ)` on upper-triangular matrices (`c = 0`) and at `c = 1`, and records its
transformation under `γ ↦ -γ` and `γ ↦ γ⁻¹` across all of `SL(2, ℤ)`.

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
  `TauCeti.ModularForm.etaMultiplier_ne_zero`, `TauCeti.ModularForm.norm_etaMultiplier`,
  `TauCeti.ModularForm.conj_etaMultiplier`: `ε(γ)²⁴ = 1` and its unit-circle consequences.
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
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_one`: the explicit multiplier when `c = 1`.
* `TauCeti.ModularForm.etaMultiplier_of_c_pos`: the Dedekind-sum value of the multiplier when
  `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_neg`, `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_neg_of_c_neg`: behavior of `ε` under `γ ↦ -γ`.
* `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_pos`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero_of_d_neg`: explicit multiplier when `c = 0`.
* `TauCeti.ModularForm.etaMultiplier_inv`, `TauCeti.ModularForm.etaMultiplier_inv_of_c_ne_zero`:
  behavior of `ε` under matrix inversion.

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

/-- The eta multiplier never vanishes, as a 24th root of unity. -/
@[simp]
theorem etaMultiplier_ne_zero (γ : SL(2, ℤ)) : etaMultiplier γ ≠ 0 := by
  intro h
  have h24 := etaMultiplier_pow_twentyFour γ
  simp [h] at h24

/-- The eta multiplier has unit norm, since its 24th power is `1`. -/
@[simp]
theorem norm_etaMultiplier (γ : SL(2, ℤ)) : ‖etaMultiplier γ‖ = 1 :=
  norm_eq_one_of_pow_eq_one (etaMultiplier_pow_twentyFour γ) (by decide)

/-- Complex conjugation inverts the eta multiplier. -/
@[simp]
theorem conj_etaMultiplier (γ : SL(2, ℤ)) :
    (starRingEnd ℂ) (etaMultiplier γ) = (etaMultiplier γ)⁻¹ :=
  (Complex.inv_eq_conj (norm_etaMultiplier γ)).symm

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

/-- The Dedekind-sum formula for `ε(γ)` passes from `γ Tⁿ` to `γ`: both sides gain the factor
`e^{π i n / 12}`, since `s(c n + d, c) = s(d, c)`. -/
private theorem etaMultiplier_eq_of_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) (hc : γ 1 0 ≠ 0)
    (h : etaMultiplier (γ * T ^ n) = cexp (π * I * ((((γ * T ^ n) 0 0 : ℂ) + (γ * T ^ n) 1 1) /
      (12 * (γ * T ^ n) 1 0) - dedekindSum ((γ * T ^ n) 1 1) ((γ * T ^ n) 1 0) - 1 / 4))) :
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
      dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  rw [etaMultiplier_mul_T_zpow, mul_T_zpow_apply_apply_zero, mul_T_zpow_apply_apply_zero,
    mul_T_zpow_apply_apply_one, dedekindSum_self_mul_add] at h
  rw [← mul_right_inj' (Complex.exp_ne_zero (π * I * n / 12)), h, ← Complex.exp_add]
  congr 1
  have hc'' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp
  ring

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
  -- Strong induction on `c`, along the Euclidean algorithm.
  suffices H : ∀ c : ℕ, ∀ γ : SL(2, ℤ), γ 1 0 = c → 0 < c → etaMultiplier γ =
      cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4))
    from H (γ 1 0).toNat γ (by omega) (by omega)
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro γ hγc hc
  obtain rfl | hc1 := eq_or_ne c 1
  · rw [etaMultiplier_of_c_eq_one γ hγc, hγc]
    simp
  -- Reduce `d` modulo `c` by a translation `γ Tⁿ`, with `n = -⌊d / c⌋`.
  set n := -(γ 1 1 / c)
  refine etaMultiplier_eq_of_mul_T_zpow γ n (by omega) ?_
  set γ' := γ * T ^ n
  have hc' : γ' 1 0 = c := by
    rw [mul_T_zpow_apply_apply_zero, hγc]
  have hd' : γ' 1 1 = γ 1 1 % c := by
    rw [mul_T_zpow_apply_apply_one, hγc, Int.emod_def]
    ring
  -- The reduced `d` is positive: `c` and `d` are coprime, so `c ∣ d` forces `c = 1`.
  have hdpos : 0 < γ' 1 1 := by
    refine lt_of_le_of_ne (hd' ▸ Int.emod_nonneg _ (by omega)) fun h ↦ hc1 ?_
    have hunit := (γ'.isCoprime_row 1).isUnit_of_dvd (h ▸ dvd_zero _)
    rcases Int.isUnit_iff.mp hunit with h1 | h1 <;> omega
  have hdlt : γ' 1 1 < c := hd' ▸ Int.emod_lt_of_pos _ (by omega)
  -- Invert: `γ' S` has lower-left entry `d mod c`, which lies strictly between `0` and `c`.
  have hS : (γ' * S) 1 0 = γ' 1 1 := mul_S_apply_apply_zero γ' 1
  exact etaMultiplier_eq_of_mul_S γ' (by omega) hdpos
    (ih (γ' 1 1).toNat (by omega) (γ' * S) (by omega) (by omega))

/-! ### Negation, triangular matrices, and inversion -/

/-- Explicit negation law for `etaMultiplier` across all of `SL(2, ℤ)`: `ε(-γ) = i ε(γ)` when
`γ 1 0 > 0` or (`γ 1 0 = 0` and `γ 1 1 < 0`), and `ε(-γ) = -i ε(γ)` otherwise. -/
theorem etaMultiplier_neg (γ : SL(2, ℤ)) :
    etaMultiplier (-γ) =
      if 0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ γ 1 1 < 0) then I * etaMultiplier γ
      else -I * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  set z : ℂ := (γ 1 0 : ℂ) * UpperHalfPlane.I + γ 1 1
  have hdenom : ((-γ : SL(2, ℤ)) 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (-γ : SL(2, ℤ)) 1 1 = -z := by
    simp only [z, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    ring
  have hcond : (0 < z.im ∨ (z.im = 0 ∧ z.re < 0)) ↔ 0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ γ 1 1 < 0) := by
    simp [z]
  rw [ModularGroup.SL_neg_smul, eta_smul, hdenom, Complex.sqrt_neg z]
  simp_rw [hcond]
  split_ifs <;> linear_combination (etaMultiplier γ * Complex.sqrt z * η UpperHalfPlane.I) * I_sq

/-- When `c = γ 1 0 > 0`, negating `γ` multiplies the eta multiplier by `i`. -/
theorem etaMultiplier_neg_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  rw [etaMultiplier_neg, ite_eq_left (Or.inl hc)]

/-- When `c = γ 1 0 < 0`, negating `γ` multiplies the eta multiplier by `-i`. -/
theorem etaMultiplier_neg_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  rw [etaMultiplier_neg, ite_eq_right (by omega)]

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

/-- Explicit formula for the eta multiplier of any upper-triangular matrix (`γ 1 0 = 0`) in
`SL(2, ℤ)`. -/
theorem etaMultiplier_of_c_eq_zero (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    etaMultiplier γ =
      if 0 < γ 1 1 then cexp (π * I * γ 0 1 / 12) else -I * cexp (-(π * I * γ 0 1 / 12)) := by
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ <;>
    generalize γ 0 1 = b at hγ ⊢ <;> subst hγ
  · simp [etaMultiplier_T_zpow, coe_T_zpow]
  · rw [ite_eq_right (by simp [coe_T_zpow]), neg_eq_neg_one_mul (T ^ (-b) : SL(2, ℤ)),
      etaMultiplier_mul_T_zpow, etaMultiplier_neg_one, Int.cast_neg, mul_comm]
    congr 2
    ring

/-- For an upper-triangular matrix `γ ∈ SL(2, ℤ)` with `γ 1 0 = 0` and `γ 1 1 > 0` (so `γ = Tᵇ`),
`ε(γ) = e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  rw [etaMultiplier_of_c_eq_zero γ hc, ite_eq_left hd]

/-- For an upper-triangular matrix `γ ∈ SL(2, ℤ)` with `γ 1 0 = 0` and `γ 1 1 < 0`
(so `γ = -T⁻ᵇ`), `ε(γ) = -i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  rw [etaMultiplier_of_c_eq_zero γ hc, ite_eq_right hd.not_gt]

/-- Explicit inversion law for `etaMultiplier` across all of `SL(2, ℤ)`: `ε(γ⁻¹) = ε(γ)⁻¹` except
on the negative upper-triangular coset `γ = -T⁻ᵇ` (`γ 1 0 = 0` and `γ 1 1 < 0`), where the
automorphy factor `-1` sits on the negative real branch cut and `ε(γ⁻¹) = -ε(γ)⁻¹`. -/
theorem etaMultiplier_inv (γ : SL(2, ℤ)) :
    etaMultiplier γ⁻¹ =
      if γ 1 0 = 0 ∧ γ 1 1 < 0 then -(etaMultiplier γ)⁻¹ else (etaMultiplier γ)⁻¹ := by
  -- Compare `η(i) = η(γ (γ⁻¹ i))` with `η(γ⁻¹ i)` using the automorphy cocycle `w * z = 1`,
  -- determine the branch of `√w * √z` (which is `-1` only when `z = -1`), and cancel `η(i)`.
  have h1 := eta_smul γ (γ⁻¹ • UpperHalfPlane.I)
  rw [smul_inv_smul] at h1
  have h2 := eta_smul γ⁻¹ UpperHalfPlane.I
  set z : ℂ := ((γ⁻¹ : SL(2, ℤ)) 1 0 : ℂ) * UpperHalfPlane.I + (γ⁻¹ : SL(2, ℤ)) 1 1
  set w : ℂ := (γ 1 0 : ℂ) * (γ⁻¹ • UpperHalfPlane.I : ℍ) + γ 1 1
  have hw : w = z⁻¹ := by
    have hcoc := Matrix.SpecialLinearGroup.denom_mapGL_mul γ γ⁻¹ UpperHalfPlane.I
    rw [mul_inv_cancel, map_one, UpperHalfPlane.denom_one,
      Matrix.SpecialLinearGroup.denom_mapGL, Matrix.SpecialLinearGroup.denom_mapGL] at hcoc
    simp only [algebraMap_int_eq, eq_intCast] at hcoc
    exact eq_inv_of_mul_eq_one_left hcoc.symm
  -- An upper-triangular matrix in `SL(2, ℤ)` is `±T ^ n`, so its diagonal entries agree (`±1`).
  have hdiag (hc : γ 1 0 = 0) :
      (γ 0 0 = 1 ∧ γ 1 1 = 1) ∨ (γ 0 0 = -1 ∧ γ 1 1 = -1) := by
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hγ | hγ <;>
      [left; right] <;>
      exact ⟨by rw [hγ]; simp [coe_T_zpow], by rw [hγ]; simp [coe_T_zpow]⟩
  have harg : z.arg = π ↔ γ 1 0 = 0 ∧ γ 1 1 < 0 := by
    have hz_re : z.re = (γ 0 0 : ℝ) := by simp [z]
    have hz_im : z.im = -(γ 1 0 : ℝ) := by simp [z]
    rw [Complex.arg_eq_pi_iff, hz_re, hz_im, neg_eq_zero, Int.cast_eq_zero, Int.cast_lt_zero,
      and_comm]
    exact and_congr_right fun hc ↦ by rcases hdiag hc with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]
  have hroot : Complex.sqrt w * Complex.sqrt z =
      if γ 1 0 = 0 ∧ γ 1 1 < 0 then -1 else 1 := by
    by_cases h : γ 1 0 = 0 ∧ γ 1 1 < 0
    · have ha : γ 0 0 = -1 := by rcases hdiag h.1 with ⟨_, h1⟩ | ⟨h0, _⟩ <;> omega
      have hz : z = -1 := by simp [z, h.1, ha]
      rw [ite_eq_left h, hw, hz, inv_neg, inv_one, Complex.sqrt_neg_one, I_mul_I]
    · have hz_ne : z ≠ 0 := by
        have hne := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹)
          UpperHalfPlane.I
        rw [Matrix.SpecialLinearGroup.denom_mapGL] at hne
        simpa [z] using hne
      rw [ite_eq_right h, hw, Complex.sqrt, Complex.sqrt, Complex.inv_cpow z _ (harg.not.mpr h),
        ← Complex.sqrt]
      exact inv_mul_cancel₀ (Complex.sqrt_eq_zero_iff.not.mpr hz_ne)
  have hprod : etaMultiplier γ * etaMultiplier γ⁻¹ *
      (if γ 1 0 = 0 ∧ γ 1 1 < 0 then -1 else 1) = 1 := by
    apply mul_right_cancel₀ (_root_.ModularForm.eta_ne_zero UpperHalfPlane.I.coe_im_pos)
    rw [one_mul, ← hroot]
    linear_combination -h1 - etaMultiplier γ * Complex.sqrt w * h2
  apply mul_left_cancel₀ (etaMultiplier_ne_zero γ)
  split_ifs at hprod ⊢
  · rw [mul_neg, mul_inv_cancel₀ (etaMultiplier_ne_zero γ)]
    linear_combination -hprod
  · rw [mul_inv_cancel₀ (etaMultiplier_ne_zero γ)]
    linear_combination hprod

/-- When `c ≠ 0`, the eta multiplier of `γ⁻¹` is the inverse of the eta multiplier of `γ`:
`ε(γ⁻¹) = ε(γ)⁻¹`. The hypothesis `c ≠ 0` cannot be dropped altogether: when `c = 0`, the
identity holds for `d > 0` (`γ = T ^ b`) and fails for `d < 0` (e.g. at `γ = -1`, where
`ε(-1) = -i ≠ i = ε(-1)⁻¹`). -/
theorem etaMultiplier_inv_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ := by
  rw [etaMultiplier_inv, ite_eq_right (fun h ↦ hc h.1)]

end TauCeti.ModularForm
