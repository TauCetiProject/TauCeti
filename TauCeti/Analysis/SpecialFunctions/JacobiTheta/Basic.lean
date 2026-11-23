/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Jacobi's four theta functions

This file defines Jacobi's theta functions `θ₁(z|τ), …, θ₄(z|τ)` of a complex variable `z`, in the
normalization of Whittaker–Watson and of the DLMF: with the nome `q = e^{iπτ}` and
`q^α = e^{iαπτ}`,

  `θ₁(z|τ) = 2 ∑_{n≥0} (-1)ⁿ q^{(n+½)²} sin((2n + 1)z)`,
  `θ₂(z|τ) = 2 ∑_{n≥0} q^{(n+½)²} cos((2n + 1)z)`,
  `θ₃(z|τ) = 1 + 2 ∑_{n≥1} q^{n²} cos(2nz)`,
  `θ₄(z|τ) = 1 + 2 ∑_{n≥1} (-1)ⁿ q^{n²} cos(2nz)`.

They are defined as half-period translates of Mathlib's two-variable theta function
`jacobiTheta₂ z τ = ∑_{n∈ℤ} e^{2πinz + πin²τ}`, rescaled by `z ↦ z/π`: with the multiplier
`M(z|τ) = e^{iz + iπτ/4}` (`TauCeti.thetaMultiplier`),

  `θ₃(z|τ) = jacobiTheta₂ (z/π) τ`, `θ₄(z|τ) = jacobiTheta₂ (z/π + 1/2) τ`,
  `θ₂(z|τ) = M(z|τ) jacobiTheta₂ (z/π + τ/2) τ`,
  `θ₁(z|τ) = -i M(z|τ) jacobiTheta₂ (z/π + 1/2 + τ/2) τ`.

For `τ.im ≤ 0` all four take the junk value `0` of `jacobiTheta₂`. The powers `q^α` are always
`e^{iαπτ}`, never principal powers of `q`.

The series, holomorphy, parity and conjugation laws proved here are the basic API through which
the classical identities between the four functions (quasi-periodicity, Riemann's theta formula,
the product formula and the modular function `λ`) are reached.

## Main results

* `TauCeti.hasSum_int_jacobiThetaOne`, …, `TauCeti.hasSum_int_jacobiThetaFour`: the bilateral
  Fourier series over `ℤ`, such as `θ₃(z|τ) = ∑_{n∈ℤ} q^{n²} e^{2inz}`.
* `TauCeti.hasSum_jacobiThetaOne`, …, `TauCeti.hasSum_jacobiThetaFour`: the series over `ℕ`
  displayed above (DLMF 20.2.1–20.2.4).
* `TauCeti.differentiableOn_uncurry_jacobiThetaOne`, …: each `θⱼ` is holomorphic in `(z, τ)` on
  `ℂ × {τ | 0 < τ.im}`, and `TauCeti.differentiable_jacobiThetaOne`, …: it is entire in `z`.
* `TauCeti.jacobiThetaOne_neg`, …: `θ₁` is odd and `θ₂`, `θ₃`, `θ₄` are even in `z`.
* `TauCeti.jacobiThetaOne_conj`, …: `θⱼ(conj z | -conj τ) = conj θⱼ(z|τ)`.
* `TauCeti.jacobiThetaThree_zero`: the theta constant `θ₃(0|τ)` is Mathlib's `jacobiTheta τ`.

## References

* E. T. Whittaker, G. N. Watson, *A Course of Modern Analysis*, 4th ed., §§21.1–21.11.
* NIST *Digital Library of Mathematical Functions*, §§20.2 (20.2.1–20.2.4, 20.2.11–20.2.14).
* E. M. Stein, R. Shakarchi, *Complex Analysis*, Ch. 10, Prop. 1.1.
-/

public section

open Complex
open scoped Real ComplexConjugate

namespace TauCeti

/-! ### Definitions -/

/-- The multiplier `M(z|τ) = e^{iz + iπτ/4}` relating `θ₁`, `θ₂` to half-period translates of
`θ₃` (DLMF 20.2.10). -/
noncomputable def thetaMultiplier (z τ : ℂ) : ℂ := cexp (I * z + π * I * τ / 4)

/-- Jacobi's theta function `θ₃(z|τ) = ∑_{n∈ℤ} q^{n²} e^{2inz}`, `q = e^{iπτ}`, defined as
`jacobiTheta₂ (z/π) τ`. It is `0` for `τ.im ≤ 0`. -/
noncomputable def jacobiThetaThree (z τ : ℂ) : ℂ := jacobiTheta₂ (z / π) τ

/-- Jacobi's theta function `θ₄(z|τ) = ∑_{n∈ℤ} (-1)ⁿ q^{n²} e^{2inz}`, `q = e^{iπτ}`, the
translate `θ₃(z + π/2|τ)`. It is `0` for `τ.im ≤ 0`. -/
noncomputable def jacobiThetaFour (z τ : ℂ) : ℂ := jacobiTheta₂ (z / π + 1 / 2) τ

/-- Jacobi's theta function `θ₂(z|τ) = ∑_{n∈ℤ} q^{(n+½)²} e^{(2n+1)iz}`, with
`q^{(n+½)²} = e^{iπτ(n+½)²}`; it is `e^{iz + iπτ/4} θ₃(z + πτ/2|τ)`. It is `0` for
`τ.im ≤ 0`. -/
noncomputable def jacobiThetaTwo (z τ : ℂ) : ℂ :=
  thetaMultiplier z τ * jacobiTheta₂ (z / π + τ / 2) τ

/-- Jacobi's theta function `θ₁(z|τ) = -i ∑_{n∈ℤ} (-1)ⁿ q^{(n+½)²} e^{(2n+1)iz}`, with
`q^{(n+½)²} = e^{iπτ(n+½)²}`; it is `-i e^{iz + iπτ/4} θ₃(z + π/2 + πτ/2|τ)`. It is `0` for
`τ.im ≤ 0`. -/
noncomputable def jacobiThetaOne (z τ : ℂ) : ℂ :=
  -I * thetaMultiplier z τ * jacobiTheta₂ (z / π + 1 / 2 + τ / 2) τ

/-- The defining formula of the multiplier `M(z|τ)`. -/
theorem thetaMultiplier_def (z τ : ℂ) : thetaMultiplier z τ = cexp (I * z + π * I * τ / 4) := (rfl)

/-- The defining formula of `θ₃` through `jacobiTheta₂`. -/
theorem jacobiThetaThree_def (z τ : ℂ) :
    jacobiThetaThree z τ = jacobiTheta₂ (z / π) τ := (rfl)

/-- The defining formula of `θ₄` through `jacobiTheta₂`. -/
theorem jacobiThetaFour_def (z τ : ℂ) :
    jacobiThetaFour z τ = jacobiTheta₂ (z / π + 1 / 2) τ := (rfl)

/-- The defining formula of `θ₂` through `jacobiTheta₂`. -/
theorem jacobiThetaTwo_def (z τ : ℂ) :
    jacobiThetaTwo z τ = thetaMultiplier z τ * jacobiTheta₂ (z / π + τ / 2) τ := (rfl)

/-- The defining formula of `θ₁` through `jacobiTheta₂`. -/
theorem jacobiThetaOne_def (z τ : ℂ) :
    jacobiThetaOne z τ =
      -I * thetaMultiplier z τ * jacobiTheta₂ (z / π + 1 / 2 + τ / 2) τ := (rfl)

/-- The theta constant `θ₃(0|τ)` is Mathlib's one-variable `jacobiTheta τ`. -/
theorem jacobiThetaThree_zero (τ : ℂ) : jacobiThetaThree 0 τ = jacobiTheta τ := by
  rw [jacobiThetaThree_def, zero_div, jacobiTheta_eq_jacobiTheta₂]

/-- The junk value of `θ₁` off the upper half-plane. -/
theorem jacobiThetaOne_undef (z : ℂ) {τ : ℂ} (hτ : τ.im ≤ 0) : jacobiThetaOne z τ = 0 := by
  rw [jacobiThetaOne_def, jacobiTheta₂_undef _ hτ, mul_zero]

/-- The junk value of `θ₂` off the upper half-plane. -/
theorem jacobiThetaTwo_undef (z : ℂ) {τ : ℂ} (hτ : τ.im ≤ 0) : jacobiThetaTwo z τ = 0 := by
  rw [jacobiThetaTwo_def, jacobiTheta₂_undef _ hτ, mul_zero]

/-- The junk value of `θ₃` off the upper half-plane. -/
theorem jacobiThetaThree_undef (z : ℂ) {τ : ℂ} (hτ : τ.im ≤ 0) : jacobiThetaThree z τ = 0 :=
  jacobiTheta₂_undef _ hτ

/-- The junk value of `θ₄` off the upper half-plane. -/
theorem jacobiThetaFour_undef (z : ℂ) {τ : ℂ} (hτ : τ.im ≤ 0) : jacobiThetaFour z τ = 0 :=
  jacobiTheta₂_undef _ hτ

/-! ### The bilateral Fourier series -/

/-- The bilateral Fourier series `θ₁(z|τ) = -i ∑_{n∈ℤ} (-1)ⁿ q^{(n+½)²} e^{(2n+1)iz}`, stated for
`i θ₁(z|τ)` (Whittaker–Watson §21.11; DLMF 20.2.1). -/
theorem hasSum_int_jacobiThetaOne (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ ↦ (-1) ^ n * cexp (π * I * τ * (n + 1 / 2) ^ 2) *
      cexp ((2 * n + 1) * I * z)) (I * jacobiThetaOne z τ) := by
  have h : I * jacobiThetaOne z τ =
      thetaMultiplier z τ * jacobiTheta₂ (z / π + 1 / 2 + τ / 2) τ := by
    rw [jacobiThetaOne_def, ← mul_assoc, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  rw [h, thetaMultiplier_def]
  refine ((hasSum_jacobiTheta₂_term _ hτ).mul_left _).congr_fun fun n ↦ ?_
  simp only [jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_intCast_mul, ← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The bilateral Fourier series `θ₂(z|τ) = ∑_{n∈ℤ} q^{(n+½)²} e^{(2n+1)iz}` (Whittaker–Watson
§21.11; DLMF 20.2.2). -/
theorem hasSum_int_jacobiThetaTwo (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ ↦ cexp (π * I * τ * (n + 1 / 2) ^ 2) * cexp ((2 * n + 1) * I * z))
      (jacobiThetaTwo z τ) := by
  rw [jacobiThetaTwo_def, thetaMultiplier_def]
  refine ((hasSum_jacobiTheta₂_term _ hτ).mul_left _).congr_fun fun n ↦ ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The bilateral Fourier series `θ₃(z|τ) = ∑_{n∈ℤ} q^{n²} e^{2inz}` (Whittaker–Watson §21.11;
DLMF 20.2.3). -/
theorem hasSum_int_jacobiThetaThree (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ ↦ cexp (π * I * τ * n ^ 2) * cexp (2 * n * I * z))
      (jacobiThetaThree z τ) := by
  rw [jacobiThetaThree_def]
  refine (hasSum_jacobiTheta₂_term _ hτ).congr_fun fun n ↦ ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The bilateral Fourier series `θ₄(z|τ) = ∑_{n∈ℤ} (-1)ⁿ q^{n²} e^{2inz}` (Whittaker–Watson
§21.11; DLMF 20.2.4). -/
theorem hasSum_int_jacobiThetaFour (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ ↦ (-1) ^ n * cexp (π * I * τ * n ^ 2) * cexp (2 * n * I * z))
      (jacobiThetaFour z τ) := by
  rw [jacobiThetaFour_def]
  refine (hasSum_jacobiTheta₂_term _ hτ).congr_fun fun n ↦ ?_
  rw [jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_intCast_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring

/-! ### The Fourier series over `ℕ` -/

/-- The bilateral terms of `θ₁`, `θ₂` of index `n` and `-(n+1)` pair to
`q^{(n+½)²} e^{±(2n+1)iz}`. -/
private lemma cexp_odd_index (n : ℕ) (z τ : ℂ) :
    cexp ((2 * ((n : ℤ) : ℂ) + 1) * I * z) = cexp ((2 * n + 1) * z * I) ∧
    cexp ((2 * ((-((n : ℤ) + 1) : ℤ) : ℂ) + 1) * I * z) = cexp (-((2 * n + 1) * z) * I) ∧
    cexp (π * I * τ * (((-((n : ℤ) + 1) : ℤ) : ℂ) + 1 / 2) ^ 2) =
      cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> push_cast <;> ring

/-- The bilateral terms of `θ₃`, `θ₄` of index `n+1` and `-(n+1)` pair to
`q^{(n+1)²} e^{±2(n+1)iz}`. -/
private lemma cexp_even_index (n : ℕ) (z τ : ℂ) :
    cexp (2 * (((n + 1 : ℕ) : ℤ) : ℂ) * I * z) = cexp (2 * ((n : ℂ) + 1) * z * I) ∧
    cexp (2 * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) * I * z) = cexp (-(2 * ((n : ℂ) + 1) * z) * I) ∧
    cexp (π * I * τ * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) ^ 2) =
      cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> push_cast <;> ring

/-- The Fourier series `θ₁(z|τ) = 2 ∑_{n≥0} (-1)ⁿ q^{(n+½)²} sin((2n + 1)z)` (Whittaker–Watson
§21.11; DLMF 20.2.1). -/
theorem hasSum_jacobiThetaOne (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ ↦ 2 * (-1) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      Complex.sin ((2 * n + 1) * z)) (jacobiThetaOne z τ) := by
  have h := ((hasSum_int_jacobiThetaOne z hτ).nat_add_neg_add_one).mul_left (-I)
  rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul] at h
  refine h.congr_fun fun n ↦ ?_
  obtain ⟨e₁, e₂, e₃⟩ := cexp_odd_index n z τ
  rw [e₁, e₂, e₃, ← inv_zpow', inv_neg_one, zpow_add_one₀ (neg_ne_zero.2 one_ne_zero),
    zpow_natCast, Int.cast_natCast]
  linear_combination (-1) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * two_sin ((2 * n + 1) * z)

/-- The Fourier series `θ₂(z|τ) = 2 ∑_{n≥0} q^{(n+½)²} cos((2n + 1)z)` (Whittaker–Watson §21.11;
DLMF 20.2.2). -/
theorem hasSum_jacobiThetaTwo (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ ↦ 2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      Complex.cos ((2 * n + 1) * z)) (jacobiThetaTwo z τ) := by
  refine (hasSum_int_jacobiThetaTwo z hτ).nat_add_neg_add_one.congr_fun fun n ↦ ?_
  obtain ⟨e₁, e₂, e₃⟩ := cexp_odd_index n z τ
  rw [e₁, e₂, e₃, Int.cast_natCast]
  linear_combination cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * two_cos ((2 * n + 1) * z)

/-- The Fourier series `θ₃(z|τ) = 1 + 2 ∑_{n≥1} q^{n²} cos(2nz)` (Whittaker–Watson §21.11;
DLMF 20.2.3). -/
theorem hasSum_jacobiThetaThree (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ ↦ 2 * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
      Complex.cos (2 * ((n : ℂ) + 1) * z)) (jacobiThetaThree z τ - 1) := by
  have h := (hasSum_int_jacobiThetaThree z hτ).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at h
  convert h using 1
  · funext n
    obtain ⟨e₁, e₂, e₃⟩ := cexp_even_index n z τ
    rw [e₁, e₂, e₃, Int.cast_natCast, Nat.cast_succ]
    linear_combination cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) * two_cos (2 * ((n : ℂ) + 1) * z)
  · simp

/-- The Fourier series `θ₄(z|τ) = 1 + 2 ∑_{n≥1} (-1)ⁿ q^{n²} cos(2nz)` (Whittaker–Watson §21.11;
DLMF 20.2.4). -/
theorem hasSum_jacobiThetaFour (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ ↦ 2 * (-1) ^ (n + 1) * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
      Complex.cos (2 * ((n : ℂ) + 1) * z)) (jacobiThetaFour z τ - 1) := by
  have h := (hasSum_int_jacobiThetaFour z hτ).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at h
  convert h using 1
  · funext n
    obtain ⟨e₁, e₂, e₃⟩ := cexp_even_index n z τ
    rw [e₁, e₂, e₃, ← inv_zpow', inv_neg_one, zpow_natCast, Int.cast_natCast, Nat.cast_succ]
    linear_combination (-1) ^ (n + 1) * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
      two_cos (2 * ((n : ℂ) + 1) * z)
  · simp

/-! ### Holomorphy -/

/-- `θ₁(z|τ)` is holomorphic in `(z, τ)` on `ℂ × {τ | 0 < τ.im}`. -/
theorem differentiableOn_uncurry_jacobiThetaOne :
    DifferentiableOn ℂ (Function.uncurry jacobiThetaOne) {p : ℂ × ℂ | 0 < p.2.im} := by
  refine fun p hp ↦ DifferentiableAt.differentiableWithinAt ?_
  simp only [Function.uncurry_def, jacobiThetaOne_def, thetaMultiplier_def]
  exact (by fun_prop : DifferentiableAt ℂ _ p).mul
    ((hasFDerivAt_jacobiTheta₂ _ hp).differentiableAt.comp
      (f := fun q : ℂ × ℂ ↦ (q.1 / π + 1 / 2 + q.2 / 2, q.2)) p (by fun_prop))

/-- `θ₂(z|τ)` is holomorphic in `(z, τ)` on `ℂ × {τ | 0 < τ.im}`. -/
theorem differentiableOn_uncurry_jacobiThetaTwo :
    DifferentiableOn ℂ (Function.uncurry jacobiThetaTwo) {p : ℂ × ℂ | 0 < p.2.im} := by
  refine fun p hp ↦ DifferentiableAt.differentiableWithinAt ?_
  simp only [Function.uncurry_def, jacobiThetaTwo_def, thetaMultiplier_def]
  exact (by fun_prop : DifferentiableAt ℂ _ p).mul
    ((hasFDerivAt_jacobiTheta₂ _ hp).differentiableAt.comp
      (f := fun q : ℂ × ℂ ↦ (q.1 / π + q.2 / 2, q.2)) p (by fun_prop))

/-- `θ₃(z|τ)` is holomorphic in `(z, τ)` on `ℂ × {τ | 0 < τ.im}`. -/
theorem differentiableOn_uncurry_jacobiThetaThree :
    DifferentiableOn ℂ (Function.uncurry jacobiThetaThree) {p : ℂ × ℂ | 0 < p.2.im} := by
  refine fun p hp ↦ DifferentiableAt.differentiableWithinAt ?_
  simp only [Function.uncurry_def, jacobiThetaThree_def]
  exact (hasFDerivAt_jacobiTheta₂ _ hp).differentiableAt.comp
    (f := fun q : ℂ × ℂ ↦ (q.1 / π, q.2)) p (by fun_prop)

/-- `θ₄(z|τ)` is holomorphic in `(z, τ)` on `ℂ × {τ | 0 < τ.im}`. -/
theorem differentiableOn_uncurry_jacobiThetaFour :
    DifferentiableOn ℂ (Function.uncurry jacobiThetaFour) {p : ℂ × ℂ | 0 < p.2.im} := by
  refine fun p hp ↦ DifferentiableAt.differentiableWithinAt ?_
  simp only [Function.uncurry_def, jacobiThetaFour_def]
  exact (hasFDerivAt_jacobiTheta₂ _ hp).differentiableAt.comp
    (f := fun q : ℂ × ℂ ↦ (q.1 / π + 1 / 2, q.2)) p (by fun_prop)

/-- `θ₁(·|τ)` is entire for `0 < τ.im`. -/
theorem differentiable_jacobiThetaOne {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (jacobiThetaOne · τ) := by
  simp only [jacobiThetaOne_def, thetaMultiplier_def]
  exact fun z ↦ (by fun_prop : DifferentiableAt ℂ _ z).mul
    ((differentiableAt_jacobiTheta₂_fst _ hτ).comp z (by fun_prop))

/-- `θ₂(·|τ)` is entire for `0 < τ.im`. -/
theorem differentiable_jacobiThetaTwo {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (jacobiThetaTwo · τ) := by
  simp only [jacobiThetaTwo_def, thetaMultiplier_def]
  exact fun z ↦ (by fun_prop : DifferentiableAt ℂ _ z).mul
    ((differentiableAt_jacobiTheta₂_fst _ hτ).comp z (by fun_prop))

/-- `θ₃(·|τ)` is entire for `0 < τ.im`. -/
theorem differentiable_jacobiThetaThree {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (jacobiThetaThree · τ) := by
  simp only [jacobiThetaThree_def]
  exact fun z ↦ (differentiableAt_jacobiTheta₂_fst _ hτ).comp z (by fun_prop)

/-- `θ₄(·|τ)` is entire for `0 < τ.im`. -/
theorem differentiable_jacobiThetaFour {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (jacobiThetaFour · τ) := by
  simp only [jacobiThetaFour_def]
  exact fun z ↦ (differentiableAt_jacobiTheta₂_fst _ hτ).comp z (by fun_prop)

/-! ### Parity -/

/-- `θ₁` is odd in `z`. -/
@[simp]
theorem jacobiThetaOne_neg (z τ : ℂ) : jacobiThetaOne (-z) τ = -jacobiThetaOne z τ := by
  have hw : z / π + 1 / 2 + τ / 2 = -(-z / π + 1 / 2 + τ / 2) + 1 + τ := by ring
  have hM : cexp (I * z + π * I * τ / 4) * cexp (-π * I * (τ + 2 * (-(-z / π + 1 / 2 + τ / 2) + 1)))
      = -cexp (I * -z + π * I * τ / 4) := by
    have h : cexp (-(π * I)) = -1 := by rw [exp_neg, exp_pi_mul_I, inv_neg_one]
    conv_rhs => rw [← mul_neg_one, ← h, ← Complex.exp_add]
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring
  rw [jacobiThetaOne_def, jacobiThetaOne_def, thetaMultiplier_def, thetaMultiplier_def, hw,
    jacobiTheta₂_add_left', jacobiTheta₂_add_left, jacobiTheta₂_neg_left]
  linear_combination (-I * jacobiTheta₂ (-z / π + 1 / 2 + τ / 2) τ) * hM

/-- `θ₁` vanishes at `z = 0`. -/
@[simp]
theorem jacobiThetaOne_zero (τ : ℂ) : jacobiThetaOne 0 τ = 0 := by
  simpa [CharZero.eq_neg_self_iff] using jacobiThetaOne_neg 0 τ

/-- `θ₂` is even in `z`. -/
@[simp]
theorem jacobiThetaTwo_neg (z τ : ℂ) : jacobiThetaTwo (-z) τ = jacobiThetaTwo z τ := by
  have hw : z / π + τ / 2 = -(-z / π + τ / 2) + τ := by ring
  rw [jacobiThetaTwo_def, jacobiThetaTwo_def, thetaMultiplier_def, thetaMultiplier_def, hw,
    jacobiTheta₂_add_left', jacobiTheta₂_neg_left, ← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-- `θ₃` is even in `z`. -/
@[simp]
theorem jacobiThetaThree_neg (z τ : ℂ) : jacobiThetaThree (-z) τ = jacobiThetaThree z τ := by
  rw [jacobiThetaThree_def, jacobiThetaThree_def, neg_div, jacobiTheta₂_neg_left]

/-- `θ₄` is even in `z`. -/
@[simp]
theorem jacobiThetaFour_neg (z τ : ℂ) : jacobiThetaFour (-z) τ = jacobiThetaFour z τ := by
  have hw : z / π + 1 / 2 = -(-z / π + 1 / 2) + 1 := by ring
  rw [jacobiThetaFour_def, jacobiThetaFour_def, hw, jacobiTheta₂_add_left, jacobiTheta₂_neg_left]

/-! ### Conjugation -/

/-- `conj M(z|τ) = M(-conj z | -conj τ)`. -/
theorem thetaMultiplier_conj (z τ : ℂ) :
    conj (thetaMultiplier z τ) = thetaMultiplier (-conj z) (-conj τ) := by
  rw [thetaMultiplier_def, thetaMultiplier_def, ← exp_conj]
  congr 1
  simp only [map_add, map_mul, map_div₀, conj_I, conj_ofReal, map_ofNat]
  ring

/-- `θ₁(conj z | -conj τ) = conj θ₁(z|τ)`. -/
theorem jacobiThetaOne_conj (z τ : ℂ) :
    jacobiThetaOne (conj z) (-conj τ) = conj (jacobiThetaOne z τ) := by
  have hw : conj (z / π + 1 / 2 + τ / 2) = -(-conj z / π + 1 / 2 + -conj τ / 2) + 1 := by
    simp only [map_add, map_div₀, conj_ofReal, map_one, map_ofNat]
    ring
  rw [← neg_neg (jacobiThetaOne (conj z) _), ← jacobiThetaOne_neg, jacobiThetaOne_def,
    jacobiThetaOne_def, map_mul, map_mul, jacobiTheta₂_conj, hw, jacobiTheta₂_add_left,
    jacobiTheta₂_neg_left, thetaMultiplier_conj, map_neg, conj_I]
  ring

/-- `θ₂(conj z | -conj τ) = conj θ₂(z|τ)`. -/
theorem jacobiThetaTwo_conj (z τ : ℂ) :
    jacobiThetaTwo (conj z) (-conj τ) = conj (jacobiThetaTwo z τ) := by
  have hw : conj (z / π + τ / 2) = -(-conj z / π + -conj τ / 2) := by
    simp only [map_add, map_div₀, conj_ofReal, map_ofNat]
    ring
  rw [← jacobiThetaTwo_neg, jacobiThetaTwo_def, jacobiThetaTwo_def, map_mul, jacobiTheta₂_conj, hw,
    jacobiTheta₂_neg_left, thetaMultiplier_conj]

/-- `θ₃(conj z | -conj τ) = conj θ₃(z|τ)`. -/
theorem jacobiThetaThree_conj (z τ : ℂ) :
    jacobiThetaThree (conj z) (-conj τ) = conj (jacobiThetaThree z τ) := by
  rw [jacobiThetaThree_def, jacobiThetaThree_def, jacobiTheta₂_conj, map_div₀, conj_ofReal]

/-- `θ₄(conj z | -conj τ) = conj θ₄(z|τ)`. -/
theorem jacobiThetaFour_conj (z τ : ℂ) :
    jacobiThetaFour (conj z) (-conj τ) = conj (jacobiThetaFour z τ) := by
  rw [jacobiThetaFour_def, jacobiThetaFour_def, jacobiTheta₂_conj]
  simp only [map_add, map_div₀, conj_ofReal, map_one, map_ofNat]

end TauCeti
