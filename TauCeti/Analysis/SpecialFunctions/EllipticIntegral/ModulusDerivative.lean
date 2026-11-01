/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Elementary
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Continuity and derivatives of Legendre's integrals in the modulus

This file studies Legendre's elliptic integrals as functions of the modulus `k`.

* **Continuity.** On the nonsingular range `k ^ 2 < 1`, `legendreF φ`, `legendrePi φ · α2` (for
  `α2 < 1`) and their complete values `legendreK`, `legendrePic · α2` are continuous in `k`. The
  integrals of the second kind `legendreE φ` and `legendreEc` are continuous on all of `ℝ`, in
  particular at the singular moduli `k = ±1`.
* **Derivatives** (DLMF §19.4). For `k ≠ 0` and `k ^ 2 < 1`, with
  `k′² = 1 - k²` and `Δ = √(1 - k² sin² φ)`,
  `∂F/∂k = (E - k′² F) / (k k′²) - k sin φ cos φ / (k′² Δ)` and `∂E/∂k = (E - F) / k`. At `φ = π/2`
  these become `dK/dk = (E(k) - k′² K(k)) / (k k′²)` and `dE/dk = (E(k) - K(k)) / k`. At `k = 0`
  every derivative in the modulus vanishes.
* **Legendre's differential equations.** Differentiating the formulas for `dK/dk` and `dE/dk` once
  more shows that `K` and `E` are twice differentiable at every `k ≠ 0` with `k ^ 2 < 1`, and that
  on all of `k ^ 2 < 1`
  `k k′² K′′ + (1 - 3k²) K′ - k K = 0` and `k k′² E′′ + k′² E′ + k E = 0`.

The integrals are differentiated under the integral sign
(`TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn`), using the smoothness
`TauCeti.contDiffOn_one_sub_sq_mul_sin_sq_rpow` of the integrands. For the first kind, the
integrand of the derivative is rewritten as a difference of the integrands of `Π(φ, k, k²)` and
`F(φ, k)`, and the evaluation `TauCeti.Real.legendrePi_modulus_sq` of `Π(φ, k, k²)` in terms of
`E(φ, k)` supplies the integration by parts. For the second kind, the integrand of the derivative
is already the difference of the integrands of `E(φ, k)` and `F(φ, k)`, divided by `k`.

The first-derivative formulas are also the input to the proof by differentiation of Legendre's
relation `E(k) K(k′) + E(k′) K(k) - K(k) K(k′) = π/2` for `0 < k < 1`, where `k′ = √(1 - k²)` is
the complementary modulus.

## Main statements

* `TauCeti.Real.continuousOn_legendreK`, `TauCeti.Real.continuous_legendreEc` and
  `TauCeti.Real.continuousOn_legendrePic`: continuity of the complete integrals in the modulus.
* `TauCeti.Real.hasDerivAt_legendreF_modulus` and `TauCeti.Real.hasDerivAt_legendreE_modulus`: the
  derivatives of the incomplete integrals in the modulus.
* `TauCeti.Real.hasDerivAt_legendreK` and `TauCeti.Real.hasDerivAt_legendreEc`: the derivatives of
  the complete integrals, with `TauCeti.Real.hasDerivAt_legendreK_zero` and
  `TauCeti.Real.hasDerivAt_legendreEc_zero` at `k = 0`.
* `TauCeti.Real.hasDerivAt_deriv_legendreK` and `TauCeti.Real.hasDerivAt_deriv_legendreEc`: the
  second derivatives of the complete integrals.
* `TauCeti.Real.legendreK_differential_equation` and
  `TauCeti.Real.legendreEc_differential_equation`: Legendre's differential equations.

## References

* NIST *Digital Library of Mathematical Functions*, §19.4, <https://dlmf.nist.gov/19.4>.
-/

public section

namespace TauCeti.Real

open _root_.Real Set intervalIntegral Filter

open scoped Topology

/-! ### Differentiation under the integral sign -/

/-- The open set of pairs `(k, θ)` with `k ^ 2 < 1`, on which the integrands are smooth. -/
private theorem isOpen_setOf_fst_sq_lt_one : IsOpen {z : ℝ × ℝ | z.1 ^ 2 < 1} :=
  isOpen_lt (by fun_prop) continuous_const

private theorem singleton_prod_subset_setOf_fst_sq_lt_one {k : ℝ} (hk : k ^ 2 < 1) (a b : ℝ) :
    {k} ×ˢ uIcc a b ⊆ {z : ℝ × ℝ | z.1 ^ 2 < 1} := fun z hz ↦ by
  simpa [mem_singleton_iff.mp hz.1] using hk

/-- **Differentiation in the modulus under the integral sign.** For `k ^ 2 < 1` and every real
exponent `p`, the derivative in `k` of `∫ θ in a..b, (1 - k² sin² θ) ^ p` is
`∫ θ in a..b, -2 p k sin² θ (1 - k² sin² θ) ^ (p - 1)`. The cases `p = -1/2` and `p = 1/2` over
`[0, φ]` are the integrals `legendreF φ k` and `legendreE φ k`. -/
theorem hasDerivAt_integral_one_sub_sq_mul_sin_sq_rpow {k : ℝ} (hk : k ^ 2 < 1) (p a b : ℝ) :
    HasDerivAt (fun k ↦ ∫ θ in a..b, (1 - k ^ 2 * sin θ ^ 2) ^ p)
      (∫ θ in a..b, -(2 * p * k * sin θ ^ 2 * (1 - k ^ 2 * sin θ ^ 2) ^ (p - 1))) k := by
  have hG := contDiffOn_one_sub_sq_mul_sin_sq_rpow (n := 1) p
  obtain ⟨-, h⟩ := hasDerivAt_intervalIntegral_of_contDiffOn isOpen_setOf_fst_sq_lt_one hG
    (singleton_prod_subset_setOf_fst_sq_lt_one hk a b)
  refine h.congr_deriv (integral_congr fun θ _ ↦ ?_)
  -- the Fréchet derivative in the direction `(1, 0)` is the partial derivative in `k`
  have hz : (k, θ) ∈ {z : ℝ × ℝ | z.1 ^ 2 < 1} := hk
  have hGz := ((hG.differentiableOn one_ne_zero _ hz).differentiableAt
    (isOpen_setOf_fst_sq_lt_one.mem_nhds hz)).hasFDerivAt
  have hd := hGz.comp_hasDerivAt k ((hasDerivAt_id k).prodMk (hasDerivAt_const k θ))
  exact hd.unique (hasDerivAt_one_sub_sq_mul_sin_sq_rpow hk p θ)

/-! ### Continuity in the modulus -/

/-- The incomplete integral of the first kind is continuous in the modulus on `k ^ 2 < 1`. -/
theorem continuousOn_legendreF_modulus (φ : ℝ) :
    ContinuousOn (legendreF φ) {k | k ^ 2 < 1} := fun k hk ↦ by
  rw [funext (legendreF_def φ)]
  exact (hasDerivAt_integral_one_sub_sq_mul_sin_sq_rpow hk _ 0 φ).continuousAt.continuousWithinAt

/-- The incomplete integral of the second kind is continuous in the modulus on all of `ℝ`. -/
theorem continuous_legendreE_modulus (φ : ℝ) : Continuous (legendreE φ) := by
  rw [funext (legendreE_def φ)]
  exact continuous_parametric_intervalIntegral_of_continuous'
    ((by fun_prop : Continuous fun z : ℝ × ℝ ↦ 1 - z.1 ^ 2 * sin z.2 ^ 2).rpow_const
      fun _ ↦ Or.inr (by norm_num)) 0 φ

/-- For `α2 < 1`, the incomplete integral of the third kind is continuous in the modulus on
`k ^ 2 < 1`. -/
theorem continuousOn_legendrePi_modulus (φ : ℝ) {α2 : ℝ} (hα : α2 < 1) :
    ContinuousOn (legendrePi φ · α2) {k | k ^ 2 < 1} := fun k hk ↦ by
  simp_rw [legendrePi_def]
  have hG : ContDiffOn ℝ 1
      (fun z : ℝ × ℝ ↦ (1 - α2 * sin z.2 ^ 2)⁻¹ * (1 - z.1 ^ 2 * sin z.2 ^ 2) ^ (-1 / 2 : ℝ))
      {z : ℝ × ℝ | z.1 ^ 2 < 1} :=
    ((by fun_prop : ContDiff ℝ 1 fun z : ℝ × ℝ ↦ 1 - α2 * sin z.2 ^ 2).inv
      fun z ↦ (one_sub_mul_sin_sq_pos hα z.2).ne').contDiffOn.mul
      (contDiffOn_one_sub_sq_mul_sin_sq_rpow _)
  exact (hasDerivAt_intervalIntegral_of_contDiffOn isOpen_setOf_fst_sq_lt_one hG
    (singleton_prod_subset_setOf_fst_sq_lt_one hk 0 φ)).2.continuousAt.continuousWithinAt

/-- **Continuity of `K`** in the modulus on `k ^ 2 < 1`. -/
theorem continuousOn_legendreK : ContinuousOn legendreK {k | k ^ 2 < 1} := by
  rw [funext legendreK_def]
  exact continuousOn_legendreF_modulus (π / 2)

/-- **Continuity of `E`** in the modulus on all of `ℝ`, including the singular moduli `±1`. -/
theorem continuous_legendreEc : Continuous legendreEc := by
  rw [funext legendreEc_def]
  exact continuous_legendreE_modulus (π / 2)

/-- **Continuity of `Π(·, α²)`** in the modulus on `k ^ 2 < 1`, for `α2 < 1`. -/
theorem continuousOn_legendrePic {α2 : ℝ} (hα : α2 < 1) :
    ContinuousOn (legendrePic · α2) {k | k ^ 2 < 1} := by
  simp_rw [legendrePic_def]
  exact continuousOn_legendrePi_modulus (π / 2) hα

/-! ### Derivatives in the modulus -/

/-- At `k = 0` the incomplete integral of the first kind has derivative `0` in the modulus. -/
theorem hasDerivAt_legendreF_modulus_zero (φ : ℝ) : HasDerivAt (legendreF φ) 0 0 := by
  rw [funext (legendreF_def φ)]
  simpa using hasDerivAt_integral_one_sub_sq_mul_sin_sq_rpow (k := 0) (by norm_num) (-1 / 2) 0 φ

/-- At `k = 0` the incomplete integral of the second kind has derivative `0` in the modulus. -/
theorem hasDerivAt_legendreE_modulus_zero (φ : ℝ) : HasDerivAt (legendreE φ) 0 0 := by
  rw [funext (legendreE_def φ)]
  simpa using hasDerivAt_integral_one_sub_sq_mul_sin_sq_rpow (k := 0) (by norm_num) (1 / 2) 0 φ

/-- **The derivative of `F(φ, k)` in the modulus** (DLMF §19.4): for `k ≠ 0` and `k ^ 2 < 1`,
`∂F/∂k = (E - (1 - k²) F) / (k (1 - k²)) - k sin φ cos φ / ((1 - k²) √(1 - k² sin² φ))`. -/
theorem hasDerivAt_legendreF_modulus (φ : ℝ) {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt (legendreF φ)
      ((legendreE φ k - (1 - k ^ 2) * legendreF φ k) / (k * (1 - k ^ 2)) -
        k * sin φ * cos φ / ((1 - k ^ 2) * √(1 - k ^ 2 * sin φ ^ 2))) k := by
  have h := hasDerivAt_integral_one_sub_sq_mul_sin_sq_rpow hk (-1 / 2) 0 φ
  -- `k` times the integrand of the derivative is the integrand of `Π(φ, k, k²)` minus that of `F`
  have hint : k * ∫ θ in (0 : ℝ)..φ,
      -(2 * (-1 / 2) * k * sin θ ^ 2 * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 - 1 : ℝ)) =
      legendrePi φ k (k ^ 2) - legendreF φ k := by
    rw [legendrePi_def, legendreF_def, ← integral_sub
      (intervalIntegrable_legendrePi_integrand hk hk 0 φ)
      (intervalIntegrable_legendreF_integrand hk 0 φ), ← integral_const_mul]
    refine integral_congr fun θ _ ↦ ?_
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    simp only [rpow_sub_one hΔ.ne']
    field_simp
    ring
  rw [legendrePi_modulus_sq hk] at hint
  rw [← funext (legendreF_def φ)] at h
  refine h.congr_deriv ?_
  have h1k : 1 - k ^ 2 ≠ 0 := by linarith
  have hr : √(1 - k ^ 2 * sin φ ^ 2) ≠ 0 := (sqrt_pos.2 (one_sub_mul_sin_sq_pos hk φ)).ne'
  rw [← mul_div_cancel_left₀ (∫ θ in (0 : ℝ)..φ, _) hk₀, hint]
  field_simp
  ring

/-- **The derivative of `E(φ, k)` in the modulus** (DLMF §19.4): for `k ≠ 0` and `k ^ 2 < 1`,
`∂E/∂k = (E - F) / k`. -/
theorem hasDerivAt_legendreE_modulus (φ : ℝ) {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt (legendreE φ) ((legendreE φ k - legendreF φ k) / k) k := by
  have h := hasDerivAt_integral_one_sub_sq_mul_sin_sq_rpow hk (1 / 2) 0 φ
  -- `k` times the integrand of the derivative is the integrand of `E` minus that of `F`
  have hint : k * ∫ θ in (0 : ℝ)..φ,
      -(2 * (1 / 2) * k * sin θ ^ 2 * (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 - 1 : ℝ)) =
      legendreE φ k - legendreF φ k := by
    rw [legendreE_def, legendreF_def, ← integral_sub (intervalIntegrable_legendreE_integrand k 0 φ)
      (intervalIntegrable_legendreF_integrand hk 0 φ), ← integral_const_mul]
    refine integral_congr fun θ _ ↦ ?_
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    have hsplit : (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) =
        (1 - k ^ 2 * sin θ ^ 2) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) := by
      rw [← rpow_one_add' hΔ.le (by norm_num)]
      norm_num
    rw [hsplit, show (1 / 2 - 1 : ℝ) = -1 / 2 by norm_num]
    ring
  rw [← funext (legendreE_def φ)] at h
  refine h.congr_deriv ?_
  rw [← hint]
  field_simp

/-- **The derivative of `K`** (DLMF 19.4.1): for `k ≠ 0` and `k ^ 2 < 1`,
`K′(k) = (E(k) - (1 - k²) K(k)) / (k (1 - k²))`. -/
theorem hasDerivAt_legendreK {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt legendreK ((legendreEc k - (1 - k ^ 2) * legendreK k) / (k * (1 - k ^ 2))) k := by
  have h := hasDerivAt_legendreF_modulus (π / 2) hk₀ hk
  rw [← funext legendreK_def, ← legendreEc_def] at h
  simpa using h

/-- **The derivative of `E`** (DLMF 19.4.1): for `k ≠ 0` and `k ^ 2 < 1`,
`E′(k) = (E(k) - K(k)) / k`. -/
theorem hasDerivAt_legendreEc {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt legendreEc ((legendreEc k - legendreK k) / k) k := by
  have h := hasDerivAt_legendreE_modulus (π / 2) hk₀ hk
  rw [← funext legendreEc_def, ← legendreK_def] at h
  exact h

/-- `K′(0) = 0`. -/
theorem hasDerivAt_legendreK_zero : HasDerivAt legendreK 0 0 := by
  rw [funext legendreK_def]
  exact hasDerivAt_legendreF_modulus_zero (π / 2)

/-- `E′(0) = 0`. -/
theorem hasDerivAt_legendreEc_zero : HasDerivAt legendreEc 0 0 := by
  rw [funext legendreEc_def]
  exact hasDerivAt_legendreE_modulus_zero (π / 2)

/-! ### Second derivatives and Legendre's differential equations -/

/-- `K′(k) = (E(k) - (1 - k²) K(k)) / (k (1 - k²))` for `k ≠ 0` and `k ^ 2 < 1`, in `deriv`
form. -/
theorem deriv_legendreK {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    deriv legendreK k = (legendreEc k - (1 - k ^ 2) * legendreK k) / (k * (1 - k ^ 2)) :=
  (hasDerivAt_legendreK hk₀ hk).deriv

/-- `E′(k) = (E(k) - K(k)) / k` for `k ≠ 0` and `k ^ 2 < 1`, in `deriv` form. -/
theorem deriv_legendreEc {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    deriv legendreEc k = (legendreEc k - legendreK k) / k :=
  (hasDerivAt_legendreEc hk₀ hk).deriv

@[simp]
theorem deriv_legendreK_zero : deriv legendreK 0 = 0 :=
  hasDerivAt_legendreK_zero.deriv

@[simp]
theorem deriv_legendreEc_zero : deriv legendreEc 0 = 0 :=
  hasDerivAt_legendreEc_zero.deriv

/-- Near a modulus `k ≠ 0` with `k ^ 2 < 1`, the moduli are again nonzero with square below `1`. -/
private theorem eventually_ne_zero_and_sq_lt_one {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    ∀ᶠ x in 𝓝 k, x ≠ 0 ∧ x ^ 2 < 1 :=
  (eventually_ne_nhds hk₀).and ((isOpen_lt (continuous_pow 2) continuous_const).eventually_mem hk)

/-- **The second derivative of `K`**: for `k ≠ 0` and `k ^ 2 < 1`,
`K′′(k) = ((1 - k²) (1 - 2k²) K(k) - (1 - 3k²) E(k)) / (k² (1 - k²)²)`. In particular `K` is twice
differentiable at `k`. -/
theorem hasDerivAt_deriv_legendreK {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt (deriv legendreK)
      (((1 - k ^ 2) * (1 - 2 * k ^ 2) * legendreK k - (1 - 3 * k ^ 2) * legendreEc k) /
        (k ^ 2 * (1 - k ^ 2) ^ 2)) k := by
  have hc : 1 - k ^ 2 ≠ 0 := (sub_pos.2 hk).ne'
  have hsq := (hasDerivAt_pow 2 k).const_sub 1
  have h := ((hasDerivAt_legendreEc hk₀ hk).sub (hsq.mul (hasDerivAt_legendreK hk₀ hk))).div
    ((hasDerivAt_id' k).mul hsq) (mul_ne_zero hk₀ hc)
  refine (h.congr_of_eventuallyEq ((eventually_ne_zero_and_sq_lt_one hk₀ hk).mono
    fun x hx ↦ deriv_legendreK hx.1 hx.2)).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

/-- **The second derivative of `E`** (DLMF §19.4): for `k ≠ 0` and `k ^ 2 < 1`,
`E′′(k) = -(E(k) - (1 - k²) K(k)) / (k² (1 - k²))`, that is `E′′(k) = -K′(k) / k`. In particular `E`
is twice differentiable at `k`. -/
theorem hasDerivAt_deriv_legendreEc {k : ℝ} (hk₀ : k ≠ 0) (hk : k ^ 2 < 1) :
    HasDerivAt (deriv legendreEc)
      (-(legendreEc k - (1 - k ^ 2) * legendreK k) / (k ^ 2 * (1 - k ^ 2))) k := by
  have hc : 1 - k ^ 2 ≠ 0 := (sub_pos.2 hk).ne'
  have h := ((hasDerivAt_legendreEc hk₀ hk).sub (hasDerivAt_legendreK hk₀ hk)).div
    (hasDerivAt_id' k) hk₀
  refine (h.congr_of_eventuallyEq ((eventually_ne_zero_and_sq_lt_one hk₀ hk).mono
    fun x hx ↦ deriv_legendreEc hx.1 hx.2)).congr_deriv ?_
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- **Legendre's differential equation for `K`** (DLMF §19.4): for `k ^ 2 < 1`,
`k (1 - k²) K′′(k) + (1 - 3k²) K′(k) - k K(k) = 0`. At `k = 0` it reduces to `K′(0) = 0`. -/
theorem legendreK_differential_equation {k : ℝ} (hk : k ^ 2 < 1) :
    k * (1 - k ^ 2) * deriv^[2] legendreK k + (1 - 3 * k ^ 2) * deriv legendreK k -
      k * legendreK k = 0 := by
  rcases eq_or_ne k 0 with rfl | hk₀
  · simp
  have hc : 1 - k ^ 2 ≠ 0 := (sub_pos.2 hk).ne'
  rw [Function.iterate_succ_apply', Function.iterate_one,
    (hasDerivAt_deriv_legendreK hk₀ hk).deriv, deriv_legendreK hk₀ hk]
  field_simp
  ring

/-- **Legendre's differential equation for `E`** (DLMF §19.4): for `k ^ 2 < 1`,
`k (1 - k²) E′′(k) + (1 - k²) E′(k) + k E(k) = 0`. At `k = 0` it reduces to `E′(0) = 0`. -/
theorem legendreEc_differential_equation {k : ℝ} (hk : k ^ 2 < 1) :
    k * (1 - k ^ 2) * deriv^[2] legendreEc k + (1 - k ^ 2) * deriv legendreEc k +
      k * legendreEc k = 0 := by
  rcases eq_or_ne k 0 with rfl | hk₀
  · simp
  have hc : 1 - k ^ 2 ≠ 0 := (sub_pos.2 hk).ne'
  rw [Function.iterate_succ_apply', Function.iterate_one,
    (hasDerivAt_deriv_legendreEc hk₀ hk).deriv, deriv_legendreEc hk₀ hk]
  field_simp
  ring

end TauCeti.Real
