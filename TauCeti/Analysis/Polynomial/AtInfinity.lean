/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.MeasureTheory.Integral.Asymptotics

/-!
# Complex polynomials at infinity

A monic complex polynomial `P` of degree `m` satisfies `P z / z ^ m → 1` as `z → ∞` in the
cocompact filter of `ℂ`, which is uniform in the argument of `z`. For every complex polynomial,
`‖P'‖² / (1 + ‖P‖²)²` is integrable on the plane, and when `P` is nonconstant `(1 + ‖P‖²)⁻¹` is
square integrable; both decay like `‖z‖ ^ (-4)` or faster at infinity. These functions are the
density of the pullback of the Fubini–Study area form by `P` and the defect of the squared
modulus `‖P‖² / (1 + ‖P‖²)` from `1`.

The polynomial input is Mathlib's `Polynomial.isEquivalent_cobounded_leading_monomial`.

## Main results

* `Polynomial.Monic.tendsto_eval_div_pow_natDegree_cocompact`: `P z / z ^ m → 1`.
* `Polynomial.integrable_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq`:
  `‖P'‖² / (1 + ‖P‖²)²` is integrable.
* `Polynomial.memLp_inv_one_add_norm_eval_sq`: `(1 + ‖P‖²)⁻¹` is square integrable when `P` is
  nonconstant.
-/

public section

namespace Polynomial

open Asymptotics Filter MeasureTheory Topology

variable {P : Polynomial ℂ}

/-- A monic complex polynomial of degree `m` is asymptotic to `z ^ m` at infinity:
`P z / z ^ m → 1` in the cocompact filter. -/
theorem Monic.tendsto_eval_div_pow_natDegree_cocompact (hP : P.Monic) :
    Tendsto (fun z ↦ P.eval z / z ^ P.natDegree) (cocompact ℂ) (𝓝 1) := by
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have he := Polynomial.isEquivalent_cobounded_leading_monomial (P := P)
  simp only [hP.leadingCoeff, one_mul, Metric.cobounded_eq_cocompact] at he
  exact (isEquivalent_iff_tendsto_one (hz.mono fun z hz ↦ pow_ne_zero _ hz)).mp he

-- Polynomial growth bounds at infinity, in the form used below: `‖z‖ ^ m ≤ c ‖P z‖` gives
-- `(‖z‖ ^ m) ^ 4 ≤ c ^ 4 (1 + ‖P z‖²)²`, and `‖P' z‖ ≤ c ‖z‖ ^ (m - 1)` is squared.
private theorem exists_eventually_norm_bounds (hm : 0 < P.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℂ in cocompact ℂ, 1 ≤ ‖z‖ ∧ (1 + ‖z‖) ^ 4 ≤ 16 * ‖z‖ ^ 4 ∧
      (‖z‖ ^ P.natDegree) ^ 4 ≤ c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2 ∧
      ‖P.derivative.eval z‖ ^ 2 ≤ c ^ 2 * ‖z‖ ^ (2 * (P.natDegree - 1)) := by
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hm
  have hlow : (fun z : ℂ ↦ z ^ P.natDegree) =O[cocompact ℂ] P.eval := by
    have he := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).symm.isBigO
    rw [Metric.cobounded_eq_cocompact] at he
    exact (isBigO_self_const_mul (Polynomial.leadingCoeff_ne_zero.mpr hP) _ _).trans he
  have hup : P.derivative.eval =O[cocompact ℂ] fun z : ℂ ↦ z ^ (P.natDegree - 1) := by
    have h := (Polynomial.isBigO_cobounded_pow_natDegree P.derivative).trans
      (isBigO_pow_pow_cobounded_of_le (Polynomial.natDegree_derivative_le P))
    rwa [Metric.cobounded_eq_cocompact] at h
  obtain ⟨c₁, hc₁⟩ := hlow.bound
  obtain ⟨c₂, hc₂⟩ := hup.bound
  set c := max (max c₁ c₂) 1
  refine ⟨c, by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, tendsto_norm_cocompact_atTop.eventually_ge_atTop 1]
    with z h₁ h₂ h₃
  rw [norm_pow] at h₁ h₂
  have h₁' : ‖z‖ ^ P.natDegree ≤ c * ‖P.eval z‖ :=
    h₁.trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _))
  have h₂' : ‖P.derivative.eval z‖ ≤ c * ‖z‖ ^ (P.natDegree - 1) :=
    h₂.trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _))
  refine ⟨h₃, ?_, ?_, ?_⟩
  · calc (1 + ‖z‖) ^ 4 ≤ (2 * ‖z‖) ^ 4 := by gcongr; linarith
      _ = 16 * ‖z‖ ^ 4 := by ring
  · calc (‖z‖ ^ P.natDegree) ^ 4 ≤ (c * ‖P.eval z‖) ^ 4 := by gcongr
      _ = c ^ 4 * (‖P.eval z‖ ^ 2) ^ 2 := by ring
      _ ≤ c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2 := by gcongr; linarith
  · calc ‖P.derivative.eval z‖ ^ 2 ≤ (c * ‖z‖ ^ (P.natDegree - 1)) ^ 2 := by gcongr
      _ = c ^ 2 * ‖z‖ ^ (2 * (P.natDegree - 1)) := by ring

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²`, the density of the
pullback by `P` of the Fubini–Study area form up to a constant, is integrable on the plane. -/
theorem integrable_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq (P : Polynomial ℂ) :
    Integrable fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · simp [derivative_of_natDegree_zero h0]
  have hcont : Continuous fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 :=
    (P.derivative.continuous.norm.pow 2).div
      ((continuous_const.add (P.continuous.norm.pow 2)).pow 2) fun z ↦ by positivity
  obtain ⟨c, hc, hb⟩ := exists_eventually_norm_bounds hm
  refine hcont.locallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg (r := 4)
    (by simp [Complex.finrank_real_complex]; norm_num) (IsBigO.of_bound (16 * c ^ 6) ?_)
  filter_upwards [hb] with z ⟨h₁, hr, ha, hd⟩
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hk] at ha hd
  rw [Nat.add_sub_cancel] at hd
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  -- `‖P'‖² (1 + ‖z‖)⁴ ≲ ‖z‖ ^ (2m + 2) ≤ ‖z‖ ^ (4m) ≲ (1 + ‖P‖²)²`, using `m ≥ 1`.
  have hpow : ‖z‖ ^ (2 * k) * ‖z‖ ^ 4 ≤ (‖z‖ ^ (k + 1)) ^ 4 := by
    rw [← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ h₁ (by omega)
  calc ‖P.derivative.eval z‖ ^ 2 * (1 + ‖z‖) ^ 4 ≤
        (c ^ 2 * ‖z‖ ^ (2 * k)) * (16 * ‖z‖ ^ 4) := by gcongr
    _ = 16 * c ^ 2 * (‖z‖ ^ (2 * k) * ‖z‖ ^ 4) := by ring
    _ ≤ 16 * c ^ 2 * (c ^ 4 * (1 + ‖P.eval z‖ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (hpow.trans ha) (by positivity)
    _ = 16 * c ^ 6 * (1 + ‖P.eval z‖ ^ 2) ^ 2 := by ring

/-- For a complex polynomial `P` of degree `m ≥ 1`, the function `(1 + ‖P‖²)⁻¹` is square
integrable on the plane. -/
theorem memLp_inv_one_add_norm_eval_sq (hm : 0 < P.natDegree) :
    MemLp (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) 2 := by
  have hcont : Continuous fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹ :=
    (continuous_const.add (P.continuous.norm.pow 2)).inv₀ fun z ↦
      (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne'
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  obtain ⟨c, hc, hb⟩ := exists_eventually_norm_bounds hm
  refine (hcont.pow 2).locallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg (r := 4)
    (by simp [Complex.finrank_real_complex]; norm_num) (IsBigO.of_bound (16 * c ^ 4) ?_)
  filter_upwards [hb] with z ⟨h₁, hr, ha, _⟩
  rw [Pi.pow_apply, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Real.rpow_neg (by positivity), Real.rpow_ofNat, inv_pow, ← one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hpow : ‖z‖ ^ 4 ≤ (‖z‖ ^ P.natDegree) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ h₁ (by omega)
  linarith [hpow.trans ha]

end Polynomial
