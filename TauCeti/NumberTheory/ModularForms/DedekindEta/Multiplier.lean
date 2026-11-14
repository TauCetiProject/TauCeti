/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import Mathlib.Data.Rat.BigOperators
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# The Dedekind-sum formula for the eta multiplier

This file evaluates the Dedekind eta multiplier `TauCeti.ModularForm.etaMultiplier` across all of
`SL(2, ℤ)` in terms of the Dedekind sum `TauCeti.dedekindSum`.

For `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where the `-1/4` converts Apostol's
square root `√(-i(c τ + d))` to the principal square root `√(c τ + d)` used in `eta_smul`.
The proof abstracts the Euclidean-algorithm uniqueness principle on `{γ ∈ SL(2, ℤ) | c > 0}`:
any function agreeing with `ε` at `c = 1` and transforming like `ε` under right multiplication by
`T` and by `S` (when `d > 0`) equals `ε` everywhere on `{c > 0}`. Checking the `T`-step uses the
periodicity `s(c + d, c) = s(d, c)`, while checking the `S`-step uses Dedekind's reciprocity law
`dedekindSum_add_dedekindSum` together with `a d - b c = 1`.

Combining the `c > 0` formula with the branch behavior of `Complex.sqrt` on the half-planes and on
the negative real axis yields explicit formulas for `ε(-γ)`, for `c < 0`, for parabolic matrices
`c = 0`, for `ε(γ⁻¹)`, and for lower-triangular transvections `(1 0; n 1)`. Equating `ε(γ)²⁴` with
`1` also recovers Rademacher's integrality and congruence theorem for `12 c s(d, c)`.

## Main results

* `TauCeti.ModularForm.eq_etaMultiplier_of_c_pos`: Euclidean uniqueness criterion for `ε(γ)` on
  `c > 0` from the `c = 1` base case and the `T`- and `S`-transformation laws.
* `TauCeti.ModularForm.etaMultiplier_of_c_pos`, `TauCeti.ModularForm.eta_smul_of_c_pos`,
  `TauCeti.ModularForm.etaTransformation`: Dedekind's functional equation with the Dedekind sum.
* `TauCeti.ModularForm.etaMultiplier_neg_of_c_pos`, `TauCeti.ModularForm.etaMultiplier_of_c_neg`,
  `TauCeti.ModularForm.etaMultiplier_of_c_eq_zero`: explicit values on the remaining sign cases.
* `TauCeti.ModularForm.etaMultiplier_inv_of_c_ne_zero`, `TauCeti.ModularForm.etaMultiplier_inv`:
  behavior of `ε` under matrix inversion.
* `TauCeti.ModularForm.etaMultiplier_of_a_eq_one_of_b_eq_zero`: `ε(1 0; c 1) = e^{-π i c / 12}`
  for every integer `c`.
* `TauCeti.exists_int_twelve_mul_dedekindSum`: `12 c s(d, c)` is an integer congruent to `a + d`
  modulo `c` whenever `a d ≡ 1 (mod c)` and `c > 0`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, Chapter 2,
  Theorem 2.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Unit-circle properties of the eta multiplier -/

/-- The eta multiplier never vanishes, as a 24th root of unity. -/
@[simp]
theorem etaMultiplier_ne_zero (γ : SL(2, ℤ)) : etaMultiplier γ ≠ 0 := by
  intro h
  have h24 := etaMultiplier_pow_twentyFour γ
  rw [h, zero_pow (by decide)] at h24
  exact zero_ne_one h24

/-- The eta multiplier has unit norm. -/
@[simp]
theorem norm_etaMultiplier (γ : SL(2, ℤ)) : ‖etaMultiplier γ‖ = 1 := by
  have h := congrArg norm (etaMultiplier_pow_twentyFour γ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide)).mp h

/-- Complex conjugation inverts the eta multiplier. -/
theorem star_etaMultiplier (γ : SL(2, ℤ)) : star (etaMultiplier γ) = (etaMultiplier γ)⁻¹ := by
  apply mul_left_cancel₀ (etaMultiplier_ne_zero γ)
  rw [mul_inv_cancel₀ (etaMultiplier_ne_zero γ), RCLike.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, norm_etaMultiplier]
  norm_num

/-! ### Euclidean uniqueness on `{c > 0}` -/

/-- Iterating a single `T`-step `f (γ * T) = e^{π i / 12} f γ` on `{c > 0}` gives the `Tⁿ`-step for
all integers `n`, since right multiplication by `Tⁿ` preserves the lower-left entry. -/
private theorem mul_T_zpow_of_mul_T {f : SL(2, ℤ) → ℂ}
    (hT : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → f (γ * T) = cexp (π * I / 12) * f γ)
    {γ : SL(2, ℤ)} (hc : 0 < γ 1 0) (n : ℤ) :
    f (γ * T ^ n) = cexp (π * I * n / 12) * f γ := by
  have hnat : ∀ (δ : SL(2, ℤ)), 0 < δ 1 0 → ∀ k : ℕ,
      f (δ * T ^ (k : ℤ)) = cexp (π * I * (k : ℤ) / 12) * f δ := by
    intro δ hδ k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc' : 0 < (δ * T ^ (k : ℤ)) 1 0 := by
        rwa [TauCeti.ModularGroup.mul_T_zpow_apply, Matrix.cons_val_zero]
      rw [Nat.cast_succ, zpow_add_one, ← mul_assoc, hT _ hc', ih, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact hnat γ hc k
  · have hc' : 0 < (γ * T ^ (-(k : ℤ))) 1 0 := by
      rwa [TauCeti.ModularGroup.mul_T_zpow_apply, Matrix.cons_val_zero]
    have hk := hnat (γ * T ^ (-(k : ℤ))) hc' k
    have hcancel : γ * T ^ (-(k : ℤ)) * T ^ (k : ℤ) = γ := by
      rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [hcancel] at hk
    apply mul_left_cancel₀ (Complex.exp_ne_zero (π * I * (k : ℤ) / 12))
    rw [← hk, ← mul_assoc, ← Complex.exp_add]
    have hexp : π * I * (k : ℤ) / 12 + π * I * (-(k : ℤ) : ℤ) / 12 = 0 := by
      push_cast
      ring
    rw [hexp, Complex.exp_zero, one_mul]

/-- **Euclidean uniqueness of the eta multiplier on `c > 0`.** Any function `f : SL(2, ℤ) → ℂ`
that agrees with `etaMultiplier` when `γ 1 0 = 1` and transforms by `e^{π i / 12}` under right
multiplication by `T` (for `γ 1 0 > 0`) and by `e^{-π i / 4}` under right multiplication by `S`
(for `γ 1 0 > 0` and `γ 1 1 > 0`) equals `etaMultiplier` on every matrix with `γ 1 0 > 0`. -/
theorem eq_etaMultiplier_of_c_pos {f : SL(2, ℤ) → ℂ}
    (hc1 : ∀ γ : SL(2, ℤ), γ 1 0 = 1 → f γ = etaMultiplier γ)
    (hT : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → f (γ * T) = cexp (π * I / 12) * f γ)
    (hS : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → 0 < γ 1 1 → f (γ * S) = cexp (-(π * I / 4)) * f γ) :
    ∀ γ : SL(2, ℤ), 0 < γ 1 0 → f γ = etaMultiplier γ := by
  intro γ hc
  induction hn : (γ 1 0).natAbs using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
    by_cases h1 : γ 1 0 = 1
    · exact hc1 γ h1
    have hc_gt : 1 < γ 1 0 := by omega
    set c := γ 1 0
    set d := γ 1 1
    -- Since `a d - b c = 1` and `c > 1`, `r = d % c` lies strictly between `0` and `c`.
    have hr_pos : 0 < d % c := by
      have hr_nonneg : 0 ≤ d % c := Int.emod_nonneg d hc.ne'
      refine lt_of_le_of_ne hr_nonneg fun hr0 ↦ ?_
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hr0.symm
      have hdet := γ.det_coe
      rw [Matrix.det_fin_two] at hdet
      have hdvd : c ∣ 1 := ⟨γ 0 0 * k - γ 0 1, by linear_combination -hdet + γ 0 0 * hk⟩
      exact (Int.le_of_dvd one_pos hdvd).not_gt hc_gt
    have hr_lt : d % c < c := Int.emod_lt_of_pos d hc
    let γ₁ : SL(2, ℤ) := γ * T ^ (-(d / c))
    let γ₂ : SL(2, ℤ) := γ₁ * S
    have hγ₁0 : γ₁ 1 0 = c := by
      simp only [γ₁, TauCeti.ModularGroup.mul_T_zpow_apply, Matrix.cons_val_zero, c]
    have hγ₁1 : γ₁ 1 1 = d % c := by
      simp only [γ₁, TauCeti.ModularGroup.mul_T_zpow_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, c, d, Int.emod_def]
      ring
    have hγ₂0 : γ₂ 1 0 = d % c := by
      simp [γ₂, TauCeti.ModularGroup.mul_S_apply, hγ₁1]
    have hlt : (γ₂ 1 0).natAbs < n := by
      rw [← hn, hγ₂0]
      omega
    have h₂ : f γ₂ = etaMultiplier γ₂ := ih _ hlt γ₂ (hγ₂0 ▸ hr_pos) rfl
    have h₁ : f γ₁ = etaMultiplier γ₁ := by
      apply mul_left_cancel₀ (Complex.exp_ne_zero (-(π * I / 4)))
      rw [← hS γ₁ (hγ₁0 ▸ hc) (hγ₁1 ▸ hr_pos), ← etaMultiplier_mul_S γ₁ (hγ₁1 ▸ hr_pos), h₂]
    apply mul_left_cancel₀ (Complex.exp_ne_zero (π * I * (-(d / c) : ℤ) / 12))
    rw [← mul_T_zpow_of_mul_T hT hc (-(d / c)), ← etaMultiplier_mul_T_zpow γ (-(d / c)), h₁]

/-! ### The Dedekind-sum formula -/

/-- **Dedekind's formula for the eta multiplier** (Apostol, Theorem 3.4): for `γ = (a b; c d)` in
`SL(2, ℤ)` with `c > 0`, `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`. -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  symm
  refine eq_etaMultiplier_of_c_pos
    (f := fun δ ↦ cexp (π * I *
      (((δ 0 0 + δ 1 1 : ℤ) : ℂ) / (12 * δ 1 0) - dedekindSum (δ 1 1) (δ 1 0) - 1 / 4)))
    (fun δ hδ ↦ ?_) (fun δ hδ ↦ ?_) (fun δ hδ0 hδ1 ↦ ?_) γ hc
  · rw [etaMultiplier_of_c_eq_one δ hδ, hδ, dedekindSum_one_right]
    push_cast
    congr 1
    ring
  · have hc' : (δ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ.ne'
    simp only [TauCeti.ModularGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dedekindSum_self_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  · have hc' : (δ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ0.ne'
    have hd' : (δ 1 1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ1.ne'
    have hcop : IsCoprime (δ 1 1) (δ 1 0) := (δ.isCoprime_row 1).symm
    have hrec := congrArg (Rat.cast : ℚ → ℂ) (dedekindSum_add_dedekindSum hδ1 hδ0 hcop)
    push_cast at hrec
    have hdet : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
      have h := δ.det_coe
      rw [Matrix.det_fin_two] at h
      exact_mod_cast h
    simp only [TauCeti.ModularGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dedekindSum_neg, ← Complex.exp_add]
    congr 1
    push_cast
    have hexp : (((δ 0 1 : ℂ) + -δ 1 0) / (12 * δ 1 1) - -(dedekindSum (δ 1 0) (δ 1 1) : ℂ) -
        1 / 4) -
        (-1 / 4 + (((δ 0 0 : ℂ) + δ 1 1) / (12 * δ 1 0) - dedekindSum (δ 1 1) (δ 1 0) - 1 / 4)) =
        (dedekindSum (δ 1 1) (δ 1 0) + dedekindSum (δ 1 0) (δ 1 1) -
          (((δ 1 1 : ℂ) ^ 2 + (δ 1 0 : ℂ) ^ 2 + 1) / (12 * δ 1 1 * δ 1 0) - 1 / 4)) -
        ((δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 - 1) / (12 * δ 1 1 * δ 1 0) := by
      field_simp
      ring
    have hzero : (((δ 0 1 : ℂ) + -δ 1 0) / (12 * δ 1 1) - -(dedekindSum (δ 1 0) (δ 1 1) : ℂ) -
        1 / 4) -
        (-1 / 4 + (((δ 0 0 : ℂ) + δ 1 1) / (12 * δ 1 0) - dedekindSum (δ 1 1) (δ 1 0) - 1 / 4)) =
        0 := by
      rw [hexp, hrec, hdet]
      simp
    linear_combination π * I * hzero

/-- **The transformation law of `η` for positive lower-left entry** (Apostol, Theorem 3.4). -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
      Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul, etaMultiplier_of_c_pos γ hc]

/-- **Dedekind's functional equation**: under each element `γ ∈ SL(2, ℤ)`, `η` transforms by a
24th root of unity times the principal square root of `c τ + d`, and when `c = γ 1 0 > 0` that root
of unity is given explicitly by the finite `Int.fract` Dedekind sum (Apostol, Theorem 3.4). -/
theorem etaTransformation (γ : SL(2, ℤ)) :
    ∃ ε : ℂ, ε ^ 24 = 1 ∧
      (∀ τ : ℍ, η (γ • τ : ℍ) =
        ε * Complex.sqrt ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * η τ) ∧
      (0 < γ 1 0 → ε = cexp (π * I *
        (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * (γ 1 0 : ℂ)) -
          ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
            (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) -
          1 / 4))) := by
  refine ⟨etaMultiplier γ, etaMultiplier_pow_twentyFour γ, eta_smul γ, fun hc ↦ ?_⟩
  rw [etaMultiplier_of_c_pos γ hc]
  have hcast : (dedekindSum (γ 1 1) (γ 1 0) : ℂ) = ((dedekindSum (γ 1 1) (γ 1 0) : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, (γ.isCoprime_row 1).symm.cast_dedekindSum]
  push_cast
  rfl

/-! ### Negation, negative `c`, parabolic elements, and inversion -/

/-- When `c = γ 1 0 > 0`, negating `γ` multiplies the eta multiplier by `i`: at `τ = i`, the
automorphy factor `c i + d` has positive imaginary part, so `√(-(c i + d)) = -i √(c i + d)`. -/
theorem etaMultiplier_neg_of_c_pos {γ : SL(2, ℤ)} (hc : 0 < γ 1 0) :
    etaMultiplier (-γ) = I * etaMultiplier γ := by
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have him : 0 < ((γ 1 0 : ℂ) * I + γ 1 1).im := by
    simpa using (Int.cast_pos.mpr hc : (0 : ℝ) < γ 1 0)
  have hsmul : (-γ) • UpperHalfPlane.I = γ • UpperHalfPlane.I := by
    rw [show -γ = (-1 : SL(2, ℤ)) * γ by simp, mul_smul]
    simp
  have hdenom : ((-γ : SL(2, ℤ)) 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (-γ : SL(2, ℤ)) 1 1 =
      -((γ 1 0 : ℂ) * I + γ 1 1) := by
    simp
    ring
  rw [hsmul, eta_smul, hdenom, Complex.sqrt_neg_of_im_pos him]
  simp only [UpperHalfPlane.coe_I]
  ring_nf
  rw [I_sq]
  ring

/-- When `c = γ 1 0 < 0`, negating `γ` multiplies the eta multiplier by `-i`. -/
theorem etaMultiplier_neg_of_c_neg {γ : SL(2, ℤ)} (hc : γ 1 0 < 0) :
    etaMultiplier (-γ) = -I * etaMultiplier γ := by
  have h := etaMultiplier_neg_of_c_pos (γ := -γ) (by simpa using hc)
  rw [neg_neg] at h
  rw [h, ← mul_assoc]
  simp

/-- Explicit Dedekind-sum formula for negative lower-left entry `c = γ 1 0 < 0`:
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) + dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have hneg := etaMultiplier_neg_of_c_pos hc'
  rw [neg_neg] at hneg
  have hmulI : ∀ z : ℂ, I * cexp z = cexp (π * I / 2 + z) := fun z ↦ by
    rw [Complex.exp_add, show π * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
  rw [hneg, etaMultiplier_of_c_pos (-γ) hc', hmulI]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, dedekindSum_neg]
  have hc0 : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  congr 1
  push_cast
  field_simp
  ring

/-- For an upper-triangular matrix `γ ∈ SL(2, ℤ)` with `γ 1 0 = 0` and `γ 1 1 > 0` (so `γ = Tᵇ`),
`ε(γ) = e^{π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_pos {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) (hd : 0 < γ 1 1) :
    etaMultiplier γ = cexp (π * I * γ 0 1 / 12) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha1, hd1⟩ | ⟨_, hd1⟩
  · have hγ : γ = T ^ (γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, hc, ha1, hd1]
    rw [congrArg etaMultiplier hγ, etaMultiplier_T_zpow]
  · omega

/-- For an upper-triangular matrix `γ ∈ SL(2, ℤ)` with `γ 1 0 = 0` and `γ 1 1 < 0`
(so `γ = -T⁻ᵇ`), `ε(γ) = -i e^{-π i b / 12}`. -/
theorem etaMultiplier_of_c_eq_zero_of_d_neg {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) (hd : γ 1 1 < 0) :
    etaMultiplier γ = -I * cexp (-(π * I * γ 0 1 / 12)) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, hd1⟩ | ⟨ha1, hd1⟩
  · omega
  · have hγ : γ = (-1 : SL(2, ℤ)) * T ^ (-γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, hc, ha1, hd1]
    rw [congrArg etaMultiplier hγ, etaMultiplier_mul_T_zpow, etaMultiplier_neg_one]
    push_cast
    ring_nf

/-- Explicit formula for the eta multiplier of any parabolic element (`γ 1 0 = 0`) in `SL(2, ℤ)`. -/
theorem etaMultiplier_of_c_eq_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) :
    etaMultiplier γ =
      if 0 < γ 1 1 then cexp (π * I * γ 0 1 / 12) else -I * cexp (-(π * I * γ 0 1 / 12)) := by
  split_ifs with hd
  · exact etaMultiplier_of_c_eq_zero_of_d_pos hc hd
  · have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have hd_ne : γ 1 1 ≠ 0 := fun h0 ↦ by simp [h0] at hdet
    exact etaMultiplier_of_c_eq_zero_of_d_neg hc (by omega)

/-- Whenever `γ 1 0 ≠ 0`, the eta multiplier of `γ⁻¹` is `(ε(γ))⁻¹`. -/
theorem etaMultiplier_inv_of_c_ne_zero {γ : SL(2, ℤ)} (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ := by
  have hpos : ∀ δ : SL(2, ℤ), 0 < δ 1 0 → etaMultiplier δ⁻¹ = (etaMultiplier δ)⁻¹ := by
    intro δ hδ
    have hinv_c : (δ⁻¹ : SL(2, ℤ)) 1 0 < 0 := by
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      simpa using hδ
    have hmod : δ 0 0 * δ 1 1 ≡ 1 [ZMOD δ 1 0] := by
      rw [Int.modEq_iff_dvd]
      have hdet := δ.det_coe
      rw [Matrix.det_fin_two] at hdet
      exact ⟨-δ 0 1, by linear_combination -hdet⟩
    rw [etaMultiplier_of_c_neg δ⁻¹ hinv_c, etaMultiplier_of_c_pos δ hδ, ← Complex.exp_neg]
    simp only [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_neg]
    rw [dedekindSum_eq_of_mul_modEq_one hmod]
    have hc' : (δ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ.ne'
    congr 1
    push_cast
    field_simp
    ring
  rcases hc.lt_or_gt with hc_neg | hc_pos
  · have hc_inv : 0 < (γ⁻¹ : SL(2, ℤ)) 1 0 := by
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      simpa using hc_neg
    have h := hpos γ⁻¹ hc_inv
    rw [inv_inv] at h
    rw [h, inv_inv]
  · exact hpos γ hc_pos

/-- Explicit inversion law for `etaMultiplier` across all of `SL(2, ℤ)`: `ε(γ⁻¹) = ε(γ)⁻¹` except
on the negative parabolic coset `γ = -Tᵇ` (`γ 1 0 = 0` and `γ 1 1 < 0`), where the automorphy
factor `-1` sits on the negative real branch cut and `ε(γ⁻¹) = -ε(γ)⁻¹`. -/
theorem etaMultiplier_inv (γ : SL(2, ℤ)) :
    etaMultiplier γ⁻¹ =
      if γ 1 0 = 0 ∧ γ 1 1 < 0 then -(etaMultiplier γ)⁻¹ else (etaMultiplier γ)⁻¹ := by
  by_cases hc : γ 1 0 = 0
  · have hinv10 : (γ⁻¹ : SL(2, ℤ)) 1 0 = 0 := by
      simp [Matrix.SpecialLinearGroup.SL2_inv_expl, hc]
    have hinv01 : (γ⁻¹ : SL(2, ℤ)) 0 1 = -γ 0 1 := by
      simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha1, hd1⟩ | ⟨ha1, hd1⟩
    · have hinv11 : 0 < (γ⁻¹ : SL(2, ℤ)) 1 1 := by
        simp [Matrix.SpecialLinearGroup.SL2_inv_expl, ha1]
      rw [ite_eq_right (by omega), etaMultiplier_of_c_eq_zero_of_d_pos hinv10 hinv11,
        etaMultiplier_of_c_eq_zero_of_d_pos hc (by omega), hinv01, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    · have hinv11 : (γ⁻¹ : SL(2, ℤ)) 1 1 < 0 := by
        simp [Matrix.SpecialLinearGroup.SL2_inv_expl, ha1]
      rw [ite_eq_left (by omega), etaMultiplier_of_c_eq_zero_of_d_neg hinv10 hinv11,
        etaMultiplier_of_c_eq_zero_of_d_neg hc (by omega), hinv01, mul_inv, ← Complex.exp_neg]
      have hI : (-I : ℂ)⁻¹ = I := by
        apply mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero)
        rw [mul_inv_cancel₀ (neg_ne_zero.mpr I_ne_zero), neg_mul, I_mul_I, neg_neg]
      rw [hI]
      push_cast
      ring_nf
  · rw [ite_eq_right (fun h ↦ hc h.1)]
    exact etaMultiplier_inv_of_c_ne_zero hc

/-- For a lower-triangular transvection `γ = (1 0; c 1) ∈ SL(2, ℤ)`, `ε(γ) = e^{-π i c / 12}` for
every integer `c` (positive, zero, or negative). -/
theorem etaMultiplier_of_a_eq_one_of_b_eq_zero {γ : SL(2, ℤ)} (ha : γ 0 0 = 1) (hb : γ 0 1 = 0) :
    etaMultiplier γ = cexp (-(π * I * γ 1 0 / 12)) := by
  have hd : γ 1 1 = 1 := by
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two, ha, hb, one_mul, zero_mul, sub_zero] at hdet
    exact hdet
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · rw [etaMultiplier_of_c_neg γ hc, ha, hd, dedekindSum_one_left (by omega)]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
    congr 1
    push_cast
    field_simp
    ring
  · rw [etaMultiplier_of_c_eq_zero_of_d_pos hc (by omega), hb, hc]
    simp
  · rw [etaMultiplier_of_c_pos γ hc, ha, hd, dedekindSum_one_left hc.le]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
    congr 1
    push_cast
    field_simp
    ring

end TauCeti.ModularForm

namespace TauCeti

open Complex

/-- **Rademacher's integrality and congruence theorem for Dedekind sums**
(Rademacher–Grosswald, Chapter 2, Theorem 2): for coprime integers `d` and `c > 0`,
`12 c s(d, c)` is an integer, and for every `a` with `a d ≡ 1 (mod c)` that integer is congruent
to `a + d` modulo `c`. -/
theorem exists_int_twelve_mul_dedekindSum {d c : ℤ} (hc : 0 < c) (hdc : IsCoprime d c) :
    ∃ m : ℤ, 12 * (c : ℚ) * dedekindSum d c = m ∧
      ∀ a : ℤ, a * d ≡ 1 [ZMOD c] → m ≡ a + d [ZMOD c] := by
  -- Lift `(c, d)` to the bottom row of a matrix `γ₀ ∈ SL(2, ℤ)` and use `ε(γ₀)²⁴ = 1`.
  obtain ⟨γ₀, hγ₀c, hγ₀d⟩ := hdc.symm.exists_SL2_row 1
  have hc₀ : 0 < γ₀ 1 0 := hγ₀c ▸ hc
  have h24 := ModularForm.etaMultiplier_pow_twentyFour γ₀
  rw [ModularForm.etaMultiplier_of_c_pos γ₀ hc₀, ← Complex.exp_nat_mul] at h24
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h24
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hrat_c : (((γ₀ 0 0 + d : ℤ) : ℚ) / c - 12 * dedekindSum d c - 3 : ℂ) = k := by
    apply mul_right_cancel₀ hpi
    rw [← hk, hγ₀c, hγ₀d]
    push_cast
    ring
  have hrat : ((γ₀ 0 0 + d : ℤ) : ℚ) / c - 12 * dedekindSum d c - 3 = k := by
    exact_mod_cast hrat_c
  refine ⟨γ₀ 0 0 + d - (k + 3) * c, ?_, fun a ha ↦ ?_⟩
  · have hc' : (c : ℚ) ≠ 0 := by positivity
    push_cast at hrat ⊢
    field_simp at hrat ⊢
    linear_combination -hrat
  · have ha_eq : γ₀ 0 0 ≡ a [ZMOD c] := by
      have hdvd_prod : c ∣ (a - γ₀ 0 0) * d := by
        obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp ha
        have hdet := γ₀.det_coe
        rw [Matrix.det_fin_two, hγ₀c, hγ₀d] at hdet
        exact ⟨-q - γ₀ 0 1, by linear_combination -hq - hdet⟩
      exact Int.modEq_iff_dvd.mpr (hdc.symm.dvd_of_dvd_mul_right hdvd_prod)
    have hmod : γ₀ 0 0 + d - (k + 3) * c ≡ γ₀ 0 0 + d [ZMOD c] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨k + 3, by ring⟩
    exact hmod.trans (ha_eq.add_right d)

end TauCeti
