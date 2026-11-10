/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Sign.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Radial actions of the Kepler problem and the isotropic oscillator

A particle of mass `m > 0` in a central potential `U` with angular momentum `ℓ` moves radially in
the effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`. At energy `E` its radial momentum is
`p_r = ±√(2 m (E - U_ℓ(r)))`, and the radial motion oscillates between two **turning points**
`0 < r₁ < r₂`, the zeros of `2 m (E - U_ℓ)`. Between them one has the classical quadratures:

* the **radial action** `I_r = (1 / π) ∫_{r₁}^{r₂} √(2 m (E - U_ℓ(r))) dr`, the area enclosed by
  the radial phase curve divided by `2π` (`TauCeti.radialAction`);
* the **radial period** `T_r = 2 ∫_{r₁}^{r₂} m dr / √(2 m (E - U_ℓ(r)))`, twice the time from
  pericentre to apocentre, since `dr/dt = p_r / m` (`TauCeti.radialPeriod`);
* the **apsidal angle** `Δθ = ∫_{r₁}^{r₂} ℓ dr / (r² √(2 m (E - U_ℓ(r))))`, the polar angle swept
  from pericentre to apocentre (`TauCeti.apsidalAngle`).

All three are integrals of `TauCeti.absRadialMomentum`, the function
`r ↦ √(2 m (E - U(r)) - ℓ² / r²) = √(2 m (E - U_ℓ(r)))`.

This file evaluates them in closed form for the two potentials singled out by Bertrand's theorem,
whose bounded orbits are all closed. Each turning-point hypothesis is the equation
`2 m (E - U(rᵢ)) = ℓ² / rᵢ²`.

* **Kepler**, `U(r) = -κ / r`: `I_r = κ √(m / (-2 E)) - |ℓ|`, hence
  `E = -m κ² / (2 (I_r + |ℓ|)²)`; Kepler's third law `T_r = 2π √(m / κ) a^(3/2)` for the semi-major
  axis `a = (r₁ + r₂) / 2`; and `Δθ = π sign ℓ`, so the radial and angular frequencies agree up to
  the sign of `ℓ`.
* **Isotropic oscillator**, `U(r) = m ν² r² / 2`: `I_r = (E / ν - |ℓ|) / 2`, `T_r = π / ν` and
  `Δθ = (π / 2) sign ℓ`, so the radial frequency is twice the magnitude
  of the angular one.

In both cases the turning-point equations force `2 m (E - U_ℓ(r)) = c (r - r₁) (r₂ - r) / r²`
(in the variable `r²` for the oscillator), so every quadrature is one of the integrals of
`TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic`.

## Main declarations

* `TauCeti.absRadialMomentum`, `TauCeti.radialAction`, `TauCeti.radialPeriod`,
  `TauCeti.apsidalAngle`, with `TauCeti.absRadialMomentum_nonneg` and
  `TauCeti.absRadialMomentum_eq_zero_iff` (vanishing at the turning points).
* `TauCeti.kepler_kappa_eq`, `TauCeti.kepler_sq_eq_neg_two_mul_mul_mul` (Vieta's formulas for the
  Kepler turning points), `TauCeti.kepler_energy_neg`, `TauCeti.kepler_kappa_pos` and
  `TauCeti.kepler_sqrt_mul_sqrt_eq_abs`.
* `TauCeti.kepler_radialAction`, `TauCeti.kepler_energy_eq_neg_div_sq_radialAction_add_abs`,
  `TauCeti.kepler_radialPeriod`, `TauCeti.kepler_apsidalAngle`.
* `TauCeti.isotropicOscillator_energy_eq`, `TauCeti.isotropicOscillator_sq_eq_sq_mul`
  (Vieta's formulas for the oscillator turning points) and
  `TauCeti.isotropicOscillator_abs_eq_mul`.
* `TauCeti.isotropicOscillator_radialAction`, `TauCeti.isotropicOscillator_radialPeriod`,
  `TauCeti.isotropicOscillator_apsidalAngle`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Chapter 3 and Section 10.8.
-/

public section

open Real Set intervalIntegral

namespace TauCeti

/-- The **absolute radial momentum** `√(2 m (E - U(r)) - ℓ² / r²)` at radius `r` of a particle of
mass `m` with angular momentum `ℓ` and energy `E` in the central potential `U`. Where the radicand
is nonnegative this is `|p_r|`, written as a function of `r` at fixed `ℓ` and `E` rather than as a
phase-space coordinate; it vanishes at the turning points. -/
noncomputable def absRadialMomentum (m : ℝ) (U : ℝ → ℝ) (ℓ E r : ℝ) : ℝ :=
  √(2 * m * (E - U r) - ℓ ^ 2 / r ^ 2)

/-- The **radial action** `(1 / π) ∫_{r₁}^{r₂} |p_r| dr` between the turning points `r₁` and `r₂`,
the area enclosed by the radial phase curve divided by `2π`. -/
noncomputable def radialAction (m : ℝ) (U : ℝ → ℝ) (ℓ E r₁ r₂ : ℝ) : ℝ :=
  π⁻¹ * ∫ r in r₁..r₂, absRadialMomentum m U ℓ E r

/-- The **radial period** `2 ∫_{r₁}^{r₂} m dr / |p_r|`: the radial velocity is `p_r / m`, so this is
the time to travel from `r₁` to `r₂` and back. -/
noncomputable def radialPeriod (m : ℝ) (U : ℝ → ℝ) (ℓ E r₁ r₂ : ℝ) : ℝ :=
  2 * ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r

/-- The **apsidal angle** `∫_{r₁}^{r₂} ℓ dr / (r² |p_r|)`, the polar angle swept while the radius
moves from `r₁` to `r₂`: along the orbit `dθ / dr = ℓ / (r² p_r)`. -/
noncomputable def apsidalAngle (m : ℝ) (U : ℝ → ℝ) (ℓ E r₁ r₂ : ℝ) : ℝ :=
  ∫ r in r₁..r₂, ℓ / (r ^ 2 * absRadialMomentum m U ℓ E r)

/-- Unfolds `TauCeti.absRadialMomentum`. -/
theorem absRadialMomentum_def (m : ℝ) (U : ℝ → ℝ) (ℓ E r : ℝ) :
    absRadialMomentum m U ℓ E r = √(2 * m * (E - U r) - ℓ ^ 2 / r ^ 2) := (rfl)

/-- Unfolds `TauCeti.radialAction`. -/
theorem radialAction_def (m : ℝ) (U : ℝ → ℝ) (ℓ E r₁ r₂ : ℝ) :
    radialAction m U ℓ E r₁ r₂ = π⁻¹ * ∫ r in r₁..r₂, absRadialMomentum m U ℓ E r := (rfl)

/-- Unfolds `TauCeti.radialPeriod`. -/
theorem radialPeriod_def (m : ℝ) (U : ℝ → ℝ) (ℓ E r₁ r₂ : ℝ) :
    radialPeriod m U ℓ E r₁ r₂ = 2 * ∫ r in r₁..r₂, m / absRadialMomentum m U ℓ E r := (rfl)

/-- Unfolds `TauCeti.apsidalAngle`. -/
theorem apsidalAngle_def (m : ℝ) (U : ℝ → ℝ) (ℓ E r₁ r₂ : ℝ) :
    apsidalAngle m U ℓ E r₁ r₂ = ∫ r in r₁..r₂, ℓ / (r ^ 2 * absRadialMomentum m U ℓ E r) := (rfl)

/-- The absolute radial momentum is nonnegative. -/
theorem absRadialMomentum_nonneg (m : ℝ) (U : ℝ → ℝ) (ℓ E r : ℝ) :
    0 ≤ absRadialMomentum m U ℓ E r :=
  sqrt_nonneg _

/-- The absolute radial momentum vanishes exactly where `2 m (E - U(r)) ≤ ℓ² / r²`; in particular it
vanishes at a turning point, where `2 m (E - U(r)) = ℓ² / r²`. -/
theorem absRadialMomentum_eq_zero_iff {m : ℝ} {U : ℝ → ℝ} {ℓ E r : ℝ} :
    absRadialMomentum m U ℓ E r = 0 ↔ 2 * m * (E - U r) ≤ ℓ ^ 2 / r ^ 2 := by
  rw [absRadialMomentum_def, sqrt_eq_zero', sub_nonpos]

/-- The absolute radial momentum is positive exactly where `ℓ² / r² < 2 m (E - U(r))`. -/
theorem absRadialMomentum_pos_iff {m : ℝ} {U : ℝ → ℝ} {ℓ E r : ℝ} :
    0 < absRadialMomentum m U ℓ E r ↔ ℓ ^ 2 / r ^ 2 < 2 * m * (E - U r) := by
  rw [absRadialMomentum_def, sqrt_pos, sub_pos]

variable {m κ ν ℓ E r₁ r₂ : ℝ}

/-! ### The Kepler problem -/

/-- A Kepler turning-point equation `2 m (E + κ / r) = ℓ² / r²` with `r ≠ 0`, with the
denominators cleared. -/
private theorem kepler_turningPoint_eq {r : ℝ} (hr : r ≠ 0)
    (h : 2 * m * (E + κ / r) = ℓ ^ 2 / r ^ 2) : 2 * m * E * r ^ 2 + 2 * m * κ * r = ℓ ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hr)] at h
  rw [← h]; field_simp

/-- **Vieta's formula for the Kepler sum of turning points.** If `r₁ ≠ r₂` are nonzero turning
points of a Kepler orbit with `m ≠ 0`, then `κ = -E (r₁ + r₂)`; equivalently, for `E ≠ 0` the
semi-major axis `(r₁ + r₂) / 2` is `κ / (-2 E)`. -/
theorem kepler_kappa_eq (hm : m ≠ 0) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (hne : r₁ ≠ r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    κ = -E * (r₁ + r₂) := by
  have hprod : (2 * m * (r₂ - r₁)) * (E * (r₁ + r₂) + κ) = 0 := by
    linear_combination kepler_turningPoint_eq h₂ hr₂ - kepler_turningPoint_eq h₁ hr₁
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero two_ne_zero hm) (sub_ne_zero.2 hne.symm))
  · linarith

/-- **Vieta's formula for the Kepler product of turning points.** If `r₁ ≠ r₂` are nonzero
turning points of a Kepler orbit, then `ℓ² = -2 m E r₁ r₂`. -/
theorem kepler_sq_eq_neg_two_mul_mul_mul (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (hne : r₁ ≠ r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    ℓ ^ 2 = -2 * m * E * (r₁ * r₂) := by
  rcases eq_or_ne m 0 with rfl | hm
  · linear_combination -kepler_turningPoint_eq h₁ hr₁
  · linear_combination -kepler_turningPoint_eq h₁ hr₁ +
      2 * m * r₁ * kepler_kappa_eq hm h₁ h₂ hne hr₁ hr₂

/-- Two distinct positive turning points of a Kepler orbit with `m > 0` and `ℓ ≠ 0` force
negative energy. -/
theorem kepler_energy_neg (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    E < 0 := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hℓ2 := kepler_sq_eq_neg_two_mul_mul_mul h₁.ne' h₂.ne' hlt.ne hr₁ hr₂
  by_contra hE
  have : 0 < ℓ ^ 2 := by positivity
  nlinarith [mul_nonneg (not_lt.1 hE) (mul_pos hm (mul_pos h₁ h₂)).le]

/-- Two distinct positive turning points of a Kepler orbit with `m > 0` and `ℓ ≠ 0` force an
attractive potential: `κ > 0`. -/
theorem kepler_kappa_pos (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    0 < κ := by
  have hE := kepler_energy_neg hm hℓ h₁ hlt hr₁ hr₂
  rw [kepler_kappa_eq hm.ne' h₁.ne' (h₁.trans hlt).ne' hlt.ne hr₁ hr₂]
  nlinarith

/-- If `0 < r₁ < r₂` are turning points of a Kepler orbit, then
`√(-2 m E) √(r₁ r₂) = |ℓ|`. -/
theorem kepler_sqrt_mul_sqrt_eq_abs (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    √(-2 * m * E) * √(r₁ * r₂) = |ℓ| := by
  rw [← sqrt_mul' _ (mul_pos h₁ (h₁.trans hlt)).le, ← sqrt_sq_eq_abs,
    kepler_sq_eq_neg_two_mul_mul_mul h₁.ne' (h₁.trans hlt).ne' hlt.ne hr₁ hr₂]

/-- The Kepler turning-point facts used by the quadratures below, bundled together. -/
private theorem kepler_vieta (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    E < 0 ∧ 0 < κ ∧ κ = -E * (r₁ + r₂) ∧ ℓ ^ 2 = -2 * m * E * (r₁ * r₂) ∧
      √(-2 * m * E) * √(r₁ * r₂) = |ℓ| :=
  ⟨kepler_energy_neg hm hℓ h₁ hlt hr₁ hr₂, kepler_kappa_pos hm hℓ h₁ hlt hr₁ hr₂,
    kepler_kappa_eq hm.ne' h₁.ne' (h₁.trans hlt).ne' hlt.ne hr₁ hr₂,
    kepler_sq_eq_neg_two_mul_mul_mul h₁.ne' (h₁.trans hlt).ne' hlt.ne hr₁ hr₂,
    kepler_sqrt_mul_sqrt_eq_abs h₁ hlt hr₁ hr₂⟩

/-- If `m > 0` and `0 < r₁ < r₂` are turning points of a Kepler orbit of zero angular momentum,
then `E = 0` and `κ = 0`. -/
private theorem kepler_energy_eq_zero_and_kappa_eq_zero (hm : 0 < m) (hℓ : ℓ = 0) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    E = 0 ∧ κ = 0 := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hℓ2 := kepler_sq_eq_neg_two_mul_mul_mul h₁.ne' h₂.ne' hlt.ne hr₁ hr₂
  have hκ := kepler_kappa_eq hm.ne' h₁.ne' h₂.ne' hlt.ne hr₁ hr₂
  have hE : E = 0 := by
    have : m * (r₁ * r₂) * E = 0 := by rw [hℓ] at hℓ2; linarith
    exact (mul_eq_zero.1 this).resolve_left (mul_pos hm (mul_pos h₁ h₂)).ne'
  exact ⟨hE, by rw [hκ, hE]; ring⟩

/-- Between the turning points, the Kepler absolute radial momentum is
`√(-2 m E) √((r - r₁) (r₂ - r)) / r`. -/
private theorem kepler_absRadialMomentum_eq (hm : 0 < m) (hκ : κ = -E * (r₁ + r₂))
    (hℓ2 : ℓ ^ 2 = -2 * m * E * (r₁ * r₂)) (hE : E < 0) {r : ℝ} (hr : 0 < r) :
    absRadialMomentum m (fun r => -κ / r) ℓ E r = √(-2 * m * E) * √((r - r₁) * (r₂ - r)) / r := by
  have : 2 * m * (E - -κ / r) - ℓ ^ 2 / r ^ 2 = -2 * m * E * ((r - r₁) * (r₂ - r)) / r ^ 2 := by
    rw [hκ, hℓ2]; field_simp; ring
  rw [absRadialMomentum_def, this, sqrt_div' _ (by positivity), sqrt_mul (by nlinarith),
    sqrt_sq hr.le]

/-- `√(-2 m E) = -2 E √(m / (-2 E))` for `E < 0`. -/
private theorem sqrt_neg_two_mul_mul (hm : 0 < m) (hE : E < 0) :
    √(-2 * m * E) = -2 * E * √(m / (-2 * E)) := by
  have h2E : 0 < -2 * E := by linarith
  calc √(-2 * m * E) = √((-2 * E) ^ 2 * (m / (-2 * E))) := by
        congr 1
        field_simp
    _ = -2 * E * √(m / (-2 * E)) := by rw [sqrt_mul (sq_nonneg _), sqrt_sq h2E.le]

/-- **The Kepler radial action.** Between two distinct turning points `0 < r₁ < r₂` of a Kepler
orbit of mass `m > 0` and angular momentum `ℓ` in the potential `-κ / r`, the radial action
`(1 / π) ∫_{r₁}^{r₂} √(2 m (E + κ / r) - ℓ² / r²) dr` is `κ √(m / (-2 E)) - |ℓ|`. -/
theorem kepler_radialAction (hm : 0 < m) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    radialAction m (fun r => -κ / r) ℓ E r₁ r₂ = κ * √(m / (-2 * E)) - |ℓ| := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · obtain ⟨rfl, rfl⟩ := kepler_energy_eq_zero_and_kappa_eq_zero hm rfl h₁ hlt hr₁ hr₂
    simp [radialAction_def, absRadialMomentum_def]
  obtain ⟨hE, -, hκ, hℓ2, habs⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have hint : ∫ r in r₁..r₂, absRadialMomentum m (fun r => -κ / r) ℓ E r =
      √(-2 * m * E) * ∫ r in r₁..r₂, √((r - r₁) * (r₂ - r)) / r := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    simp only [kepler_absRadialMomentum_eq hm hκ hℓ2 hE (h₁.trans_le hr.1), mul_div_assoc]
  have hπ : π⁻¹ * (√(-2 * m * E) * (π * ((r₁ + r₂) / 2 - √(r₁ * r₂)))) =
      √(-2 * m * E) * (r₁ + r₂) / 2 - √(-2 * m * E) * √(r₁ * r₂) := by
    field_simp
  rw [radialAction_def, hint, integral_sqrt_mul_sub_mul_sub_div h₁.le hlt.le, hπ, habs,
    sqrt_neg_two_mul_mul hm hE, hκ]
  ring

/-- **The Kepler energy in terms of the actions.** Between two distinct turning points
`0 < r₁ < r₂` of a Kepler orbit of mass `m > 0`, `E = -m κ² / (2 (I_r + |ℓ|)²)`, where `I_r` is
the radial action and `|ℓ|` the angular action. -/
theorem kepler_energy_eq_neg_div_sq_radialAction_add_abs (hm : 0 < m)
    (h₁ : 0 < r₁) (hlt : r₁ < r₂) (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    E = -(m * κ ^ 2) / (2 * (radialAction m (fun r => -κ / r) ℓ E r₁ r₂ + |ℓ|) ^ 2) := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · obtain ⟨rfl, rfl⟩ := kepler_energy_eq_zero_and_kappa_eq_zero hm rfl h₁ hlt hr₁ hr₂
    simp
  obtain ⟨hE, hκ0, -⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  rw [kepler_radialAction hm h₁ hlt hr₁ hr₂, sub_add_cancel, mul_pow,
    sq_sqrt (div_nonneg hm.le (by linarith))]
  field_simp

/-- **Kepler's third law.** Between two distinct turning points `0 < r₁ < r₂` of a Kepler orbit,
the radial period is `2π √(m / κ) a^(3/2)` for the semi-major axis
`a = (r₁ + r₂) / 2`. -/
theorem kepler_radialPeriod (hm : 0 < m) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    radialPeriod m (fun r => -κ / r) ℓ E r₁ r₂ =
      2 * π * √(m / κ) * ((r₁ + r₂) / 2) ^ (3 / 2 : ℝ) := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · obtain ⟨rfl, rfl⟩ := kepler_energy_eq_zero_and_kappa_eq_zero hm rfl h₁ hlt hr₁ hr₂
    simp [radialPeriod_def, absRadialMomentum_def]
  obtain ⟨hE, hκ0, hκ, hℓ2, -⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have ha : 0 < (r₁ + r₂) / 2 := by linarith
  have hint : ∫ r in r₁..r₂, m / absRadialMomentum m (fun r => -κ / r) ℓ E r =
      m / √(-2 * m * E) * ∫ r in r₁..r₂, r / √((r - r₁) * (r₂ - r)) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    rw [kepler_absRadialMomentum_eq hm hκ hℓ2 hE (h₁.trans_le hr.1), div_div_eq_mul_div,
      div_mul_div_comm]
  have hm' : m / √(-2 * m * E) = √(m / κ) * √((r₁ + r₂) / 2) := by
    have hs : r₁ + r₂ ≠ 0 := by linarith
    calc m / √(-2 * m * E) = √(m ^ 2) / √(-2 * m * E) := by rw [sqrt_sq hm.le]
      _ = √(m / κ * ((r₁ + r₂) / 2)) := by
        rw [← sqrt_div' _ (by nlinarith), hκ]
        congr 1
        field_simp
      _ = √(m / κ) * √((r₁ + r₂) / 2) := sqrt_mul (div_nonneg hm.le hκ0.le) _
  rw [radialPeriod_def, hint, integral_div_sqrt_mul_sub_mul_sub hlt,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add ha, rpow_one, ← sqrt_eq_rpow, hm']
  ring

/-- **The Kepler apsidal angle.** Between two distinct turning points `0 < r₁ < r₂` of a Kepler
orbit, the polar angle swept from pericentre to apocentre is `π sign ℓ`: the orbit closes after one
radial period, with no precession of its apsides. -/
theorem kepler_apsidalAngle (hm : 0 < m) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    apsidalAngle m (fun r => -κ / r) ℓ E r₁ r₂ = π * SignType.sign ℓ := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp [apsidalAngle_def]
  obtain ⟨hE, -, hκ, hℓ2, habs⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have hint : ∫ r in r₁..r₂, ℓ / (r ^ 2 * absRadialMomentum m (fun r => -κ / r) ℓ E r) =
      ℓ / √(-2 * m * E) * ∫ r in r₁..r₂, 1 / (r * √((r - r₁) * (r₂ - r))) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [kepler_absRadialMomentum_eq hm hκ hℓ2 hE hr0,
      show r ^ 2 * (√(-2 * m * E) * √((r - r₁) * (r₂ - r)) / r) =
        r * (√(-2 * m * E) * √((r - r₁) * (r₂ - r))) by field_simp]
    ring
  rw [apsidalAngle_def, hint, integral_one_div_mul_sqrt_mul_sub_mul_sub h₁ hlt]
  conv_lhs => rw [← sign_mul_abs ℓ, ← habs]
  have hc : 0 < √(-2 * m * E) := sqrt_pos.2 (by nlinarith)
  have : 0 < √(r₁ * r₂) := sqrt_pos.2 (mul_pos h₁ (h₁.trans hlt))
  generalize √(-2 * m * E) = c at hc ⊢
  field_simp

/-! ### The isotropic oscillator -/

/-- An isotropic-oscillator turning-point equation `2 m (E - m ν² r² / 2) = ℓ² / r²` with
`r ≠ 0`, with the denominators cleared. -/
private theorem isotropicOscillator_turningPoint_eq {r : ℝ} (hr : r ≠ 0)
    (h : 2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) = ℓ ^ 2 / r ^ 2) :
    2 * m * E * r ^ 2 - m ^ 2 * ν ^ 2 * r ^ 4 = ℓ ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hr)] at h
  rw [← h]; ring

/-- If `m E = 0`, then a nonzero turning point of an isotropic oscillator forces `ℓ = 0` and
`m ν = 0`. -/
private theorem isotropicOscillator_eq_zero_of_mul_eq_zero {r : ℝ} (hr : r ≠ 0) (hE : m * E = 0)
    (h : 2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) = ℓ ^ 2 / r ^ 2) : ℓ = 0 ∧ m * ν = 0 := by
  have h1 : -(m * ν * r) ^ 2 = ℓ ^ 2 / r ^ 2 := by
    rw [← h]; linear_combination (-2) * hE
  have h2 : 0 ≤ ℓ ^ 2 / r ^ 2 := by positivity
  have h3 : (m * ν * r) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  have h4 : ℓ ^ 2 / r ^ 2 = 0 := by linarith
  refine ⟨?_, ?_⟩
  · rcases div_eq_zero_iff.1 h4 with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) hr
  · exact (mul_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)).resolve_right hr

/-- **Vieta's formula for the isotropic oscillator, sum of squared turning points.** If `r₁, r₂`
are turning points of an isotropic oscillator with `m ≠ 0` and `r₁² ≠ r₂²`, then
`2 E = m ν² (r₁² + r₂²)`. -/
theorem isotropicOscillator_energy_eq (hm : m ≠ 0)
    (hne : r₁ ^ 2 ≠ r₂ ^ 2) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    2 * E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by
  by_cases h₁ : r₁ = 0
  · have h₂ : r₂ ≠ 0 := fun h => hne (by rw [h₁, h])
    have hE : E = 0 := by subst h₁; simpa [hm] using hr₁
    obtain ⟨-, hν⟩ := isotropicOscillator_eq_zero_of_mul_eq_zero h₂ (by rw [hE, mul_zero]) hr₂
    rw [hE, h₁, show m * ν ^ 2 = m * ν * ν by ring, hν]
    simp
  by_cases h₂ : r₂ = 0
  · have hE : E = 0 := by subst h₂; simpa [hm] using hr₂
    obtain ⟨-, hν⟩ := isotropicOscillator_eq_zero_of_mul_eq_zero h₁ (by rw [hE, mul_zero]) hr₁
    rw [hE, h₂, show m * ν ^ 2 = m * ν * ν by ring, hν]
    simp
  have hprod : (m * (r₂ ^ 2 - r₁ ^ 2)) * (2 * E - m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2)) = 0 := by
    linear_combination isotropicOscillator_turningPoint_eq h₂ hr₂ -
      isotropicOscillator_turningPoint_eq h₁ hr₁
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd h (mul_ne_zero hm (sub_ne_zero.2 hne.symm))
  · linarith

/-- **Vieta's formula for the isotropic oscillator, product of squared turning points.** If
`r₁, r₂` are turning points of an isotropic oscillator with `r₁² ≠ r₂²`, then
`ℓ² = (m ν r₁ r₂)²`. -/
theorem isotropicOscillator_sq_eq_sq_mul
    (hne : r₁ ^ 2 ≠ r₂ ^ 2) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    ℓ ^ 2 = (m * ν * (r₁ * r₂)) ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · by_cases h₁ : r₁ = 0
    · have h₂ : r₂ ≠ 0 := fun h => hne (by rw [h₁, h])
      obtain ⟨hℓ, -⟩ := isotropicOscillator_eq_zero_of_mul_eq_zero h₂ (zero_mul _) hr₂
      simp [hℓ]
    · obtain ⟨hℓ, -⟩ := isotropicOscillator_eq_zero_of_mul_eq_zero h₁ (zero_mul _) hr₁
      simp [hℓ]
  by_cases h₁ : r₁ = 0
  · have h₂ : r₂ ≠ 0 := fun h => hne (by rw [h₁, h])
    have hE : E = 0 := by subst h₁; simpa [hm] using hr₁
    obtain ⟨hℓ, -⟩ := isotropicOscillator_eq_zero_of_mul_eq_zero h₂ (by rw [hE, mul_zero]) hr₂
    simp [hℓ, h₁]
  by_cases h₂ : r₂ = 0
  · have hE : E = 0 := by subst h₂; simpa [hm] using hr₂
    obtain ⟨hℓ, -⟩ := isotropicOscillator_eq_zero_of_mul_eq_zero h₁ (by rw [hE, mul_zero]) hr₁
    simp [hℓ, h₂]
  linear_combination -isotropicOscillator_turningPoint_eq h₁ hr₁ +
    m * r₁ ^ 2 * isotropicOscillator_energy_eq hm hne hr₁ hr₂

/-- If `0 < r₁ < r₂` are turning points of an isotropic oscillator with `m > 0` and `ν ≥ 0`,
then `|ℓ| = m ν r₁ r₂`. -/
theorem isotropicOscillator_abs_eq_mul (hm : 0 < m) (hν : 0 ≤ ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    |ℓ| = m * ν * (r₁ * r₂) := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  rw [← sqrt_sq_eq_abs, isotropicOscillator_sq_eq_sq_mul
    (pow_lt_pow_left₀ hlt h₁.le two_ne_zero).ne hr₁ hr₂, sqrt_sq (by positivity)]

/-- The isotropic-oscillator turning-point facts used by the quadratures below, bundled
together. -/
private theorem isotropicOscillator_vieta (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    2 * E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) ∧ ℓ ^ 2 = (m * ν * (r₁ * r₂)) ^ 2 ∧
      |ℓ| = m * ν * (r₁ * r₂) :=
  have hne : r₁ ^ 2 ≠ r₂ ^ 2 := (pow_lt_pow_left₀ hlt h₁.le two_ne_zero).ne
  ⟨isotropicOscillator_energy_eq hm.ne' hne hr₁ hr₂, isotropicOscillator_sq_eq_sq_mul hne hr₁ hr₂,
    isotropicOscillator_abs_eq_mul hm hν.le h₁ hlt hr₁ hr₂⟩

/-- Between the turning points, the absolute radial momentum of the isotropic oscillator is
`|m ν| √((r² - r₁²) (r₂² - r²)) / r`. -/
private theorem isotropicOscillator_absRadialMomentum_eq
    (hE : 2 * E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2)) (hℓ2 : ℓ ^ 2 = (m * ν * (r₁ * r₂)) ^ 2)
    {r : ℝ} (hr : 0 < r) :
    absRadialMomentum m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r =
      |m * ν| * √((r ^ 2 - r₁ ^ 2) * (r₂ ^ 2 - r ^ 2)) / r := by
  have : 2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2 =
      (m * ν) ^ 2 * ((r ^ 2 - r₁ ^ 2) * (r₂ ^ 2 - r ^ 2)) / r ^ 2 := by
    rw [hℓ2, show E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) / 2 by linarith]
    field_simp
    ring
  rw [absRadialMomentum_def, this, sqrt_div' _ (by positivity), sqrt_mul (by positivity),
    sqrt_sq_eq_abs, sqrt_sq hr.le]

/-- **The radial action of the isotropic oscillator.** Between two distinct turning points
`0 < r₁ < r₂` of a particle of mass `m > 0` in the potential `m ν² r² / 2` with `ν > 0`, the
radial action `(1 / π) ∫_{r₁}^{r₂} √(2 m (E - m ν² r² / 2) - ℓ² / r²) dr` is
`(E / ν - |ℓ|) / 2`. -/
theorem isotropicOscillator_radialAction (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    radialAction m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂ = (E / ν - |ℓ|) / 2 := by
  obtain ⟨hE, hℓ2, habs⟩ := isotropicOscillator_vieta hm hν h₁ hlt hr₁ hr₂
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hint : ∫ r in r₁..r₂, absRadialMomentum m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r =
      m * ν / 2 * ∫ r in r₁..r₂,
        (fun u => √((u - r₁ ^ 2) * (r₂ ^ 2 - u)) / u) (r ^ 2) * (2 * r) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [isotropicOscillator_absRadialMomentum_eq hE hℓ2 hr0, abs_of_pos (mul_pos hm hν)]
    field_simp
  rw [radialAction_def, hint, intervalIntegral.integral_comp_sq_mul h₁.le h₂.le
      (fun u => √((u - r₁ ^ 2) * (r₂ ^ 2 - u)) / u),
    integral_sqrt_mul_sub_mul_sub_div (by positivity)
    (by nlinarith), ← mul_pow, sqrt_sq (by positivity), habs,
    show E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) / 2 by linarith]
  field_simp

/-- **The radial period of the isotropic oscillator.** Between two distinct turning points
`0 < r₁ < r₂` in the potential `m ν² r² / 2` with `ν > 0`, the radial period is `π / ν`, half the
period `2π / ν` of the oscillator. -/
theorem isotropicOscillator_radialPeriod (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    radialPeriod m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂ = π / ν := by
  obtain ⟨hE, hℓ2, -⟩ := isotropicOscillator_vieta hm hν h₁ hlt hr₁ hr₂
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hint : ∫ r in r₁..r₂, m / absRadialMomentum m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r =
      1 / (2 * ν) * ∫ r in r₁..r₂,
        (fun u => 1 / √((u - r₁ ^ 2) * (r₂ ^ 2 - u))) (r ^ 2) * (2 * r) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [isotropicOscillator_absRadialMomentum_eq hE hℓ2 hr0, abs_of_pos (mul_pos hm hν)]
    field_simp
  rw [radialPeriod_def, hint, intervalIntegral.integral_comp_sq_mul h₁.le h₂.le
      (fun u => 1 / √((u - r₁ ^ 2) * (r₂ ^ 2 - u))),
    integral_one_div_sqrt_mul_sub_mul_sub (pow_lt_pow_left₀ hlt h₁.le two_ne_zero)]
  field_simp

/-- **The apsidal angle of the isotropic oscillator.** Between two distinct turning points
`0 < r₁ < r₂` in the potential `m ν² r² / 2`, the polar angle swept from pericentre to apocentre
is `(π / 2) sign ℓ`: the orbit closes after two radial periods. -/
theorem isotropicOscillator_apsidalAngle (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    apsidalAngle m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂ = π / 2 * SignType.sign ℓ := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hne : r₁ ^ 2 ≠ r₂ ^ 2 := (pow_lt_pow_left₀ hlt h₁.le two_ne_zero).ne
  have hℓ2 := isotropicOscillator_sq_eq_sq_mul hne hr₁ hr₂
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp [apsidalAngle_def]
  have hmν : m * ν ≠ 0 := by
    intro h
    rw [h] at hℓ2
    exact hℓ (by simpa using hℓ2)
  have hE := isotropicOscillator_energy_eq (left_ne_zero_of_mul hmν) hne hr₁ hr₂
  have habs : |ℓ| = |m * ν| * (r₁ * r₂) := by
    rw [← sqrt_sq_eq_abs, hℓ2, sqrt_sq_eq_abs, abs_mul (m * ν) (r₁ * r₂),
      abs_of_pos (mul_pos h₁ h₂)]
  have hc : |m * ν| ≠ 0 := abs_ne_zero.2 hmν
  have hint : ∫ r in r₁..r₂,
      ℓ / (r ^ 2 * absRadialMomentum m (fun r => m * ν ^ 2 * r ^ 2 / 2) ℓ E r) =
      ℓ / (2 * |m * ν|) * ∫ r in r₁..r₂,
        (fun u => 1 / (u * √((u - r₁ ^ 2) * (r₂ ^ 2 - u)))) (r ^ 2) * (2 * r) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [isotropicOscillator_absRadialMomentum_eq hE hℓ2 hr0]
    field_simp
  rw [apsidalAngle_def, hint, intervalIntegral.integral_comp_sq_mul h₁.le h₂.le
      (fun u => 1 / (u * √((u - r₁ ^ 2) * (r₂ ^ 2 - u)))),
    integral_one_div_mul_sqrt_mul_sub_mul_sub
    (by positivity) (pow_lt_pow_left₀ hlt h₁.le two_ne_zero), ← mul_pow, sqrt_sq (by positivity)]
  conv_lhs => rw [← sign_mul_abs ℓ, habs]
  field_simp

end TauCeti
