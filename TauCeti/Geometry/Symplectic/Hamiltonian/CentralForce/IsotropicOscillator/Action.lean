/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Turning radii and action variables of the isotropic oscillator

A particle of mass `m > 0` with angular momentum `ℓ ≠ 0` in the isotropic oscillator potential
`m ν² r² / 2`, `ν > 0`, moves radially in the effective potential
`U_ℓ(r) = ℓ² / (2 m r²) + m ν² r² / 2`. Completing the square,

`U_ℓ(r) - ν |ℓ| = (m ν r² - |ℓ|)² / (2 m r²)`,

so the minimum value of `U_ℓ` is `ν |ℓ|`, attained at the circular radius `√(|ℓ| / (m ν))`.
At every energy `E ≥ ν |ℓ|` the turning-point equation `U_ℓ(r) = E` is a quadratic equation in
`r²` with the two positive roots `(E ∓ √(E² - ν² ℓ²)) / (m ν²)`. This file constructs the
corresponding turning radii (`TauCeti.isotropicOscillatorPeriapsisRadius`,
`TauCeti.isotropicOscillatorApoapsisRadius`), shows that they are the only positive turning
points and that the allowed radii are exactly the closed interval between them, and evaluates the
radial action on this whole energy domain:

`I_r = (E / ν - |ℓ|) / 2`,

including the circular endpoint `E = ν |ℓ|`, where both radii agree and `I_r = 0`
(`TauCeti.isotropicOscillator_radialAction_turningRadii`). The integral formula between given
turning points is `TauCeti.isotropicOscillator_radialAction`.

Inverting, the energy in the radial action `I_r` and the signed angular action `I_θ = ℓ` is the
linear function `H = ν (2 I_r + |I_θ|)` (`TauCeti.isotropicOscillatorActionHamiltonian`), which
does not depend on the mass. On each component `I_θ ≠ 0` its frequencies are `Ω_r = 2 ν` and
`Ω_θ = sign(I_θ) ν`, a signed resonance `2 : ±1`. They agree with the frequencies `2π / T_r`
and `2 Δθ / T_r` computed from the radial period `T_r` and the apsidal angle `Δθ`, the polar angle
swept in half a radial oscillation. By comparison, the Kepler frequencies in
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency` are in resonance `1 : ±1`.
As there, these are statements about the reduced energy curve and the energy function in action
variables; no action-angle chart on the phase space is constructed here.

## Main results

* `TauCeti.effectivePotential_isotropicOscillator_sub_min`,
  `TauCeti.effectivePotential_isotropicOscillator_min_le`: the minimum `ν |ℓ|` of the effective
  potential.
* `TauCeti.isotropicOscillatorPeriapsisRadius_nonneg`,
  `TauCeti.isotropicOscillatorApoapsisRadius_nonneg`,
  `TauCeti.isotropicOscillatorPeriapsisRadius_zero`: the turning radii are nonnegative, and for
  `ℓ = 0` the periapsis is the collision radius `0`.
* `TauCeti.isotropicOscillatorPeriapsisRadius_pos`,
  `TauCeti.isotropicOscillatorPeriapsisRadius_le_apoapsisRadius`,
  `TauCeti.isotropicOscillatorPeriapsisRadius_lt_apoapsisRadius`: the turning radii are
  positive for `ℓ ≠ 0`, ordered, and distinct above the circular energy.
* `TauCeti.effectivePotential_isotropicOscillator_eq_iff`,
  `TauCeti.effectivePotential_isotropicOscillator_le_iff`: the positive turning points and the
  allowed radii.
* `TauCeti.isotropicOscillator_radialAction_turningRadii`: `I_r = (E / ν - |ℓ|) / 2` on the
  closed energy domain `E ≥ ν |ℓ|`.
* `TauCeti.isotropicOscillatorActionHamiltonian_radialAction_turningRadii`: the energy is
  `ν (2 I_r + |ℓ|)`.
* `TauCeti.hasDerivAt_isotropicOscillatorActionHamiltonian_fst`,
  `TauCeti.deriv_isotropicOscillatorActionHamiltonian_snd`: the frequencies `Ω_r = 2 ν` and
  `Ω_θ = sign(I_θ) ν`.
* `TauCeti.two_mul_deriv_isotropicOscillatorActionHamiltonian_snd_eq_sign_mul`: the signed
  resonance `2 Ω_θ = sign(I_θ) Ω_r`.
* `TauCeti.deriv_isotropicOscillatorActionHamiltonian_fst_eq_div_radialPeriod`,
  `TauCeti.deriv_isotropicOscillatorActionHamiltonian_snd_eq_div_radialPeriod`: the frequencies
  agree with `2π / T_r` and `2 Δθ / T_r`.

The construction parallels the Kepler turning radii and frequencies of
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Basic` and
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Chapter 3 and Section 10.8.
-/

public section

noncomputable section

open Real Set

namespace TauCeti

/-! ### Turning radii -/

/-- The periapsis radius of an isotropic oscillator orbit, the smaller positive root of
`U_ℓ(r) = E`. Its physical domain is `m > 0`, `ν > 0`, `ℓ ≠ 0` and `ν |ℓ| ≤ E`. -/
def isotropicOscillatorPeriapsisRadius (m ν ℓ E : ℝ) : ℝ :=
  √((E - √(E ^ 2 - ν ^ 2 * ℓ ^ 2)) / (m * ν ^ 2))

/-- The apoapsis radius of an isotropic oscillator orbit, the larger positive root of
`U_ℓ(r) = E`, on the same energy domain as `isotropicOscillatorPeriapsisRadius`. At the circular
energy the two radii agree. -/
def isotropicOscillatorApoapsisRadius (m ν ℓ E : ℝ) : ℝ :=
  √((E + √(E ^ 2 - ν ^ 2 * ℓ ^ 2)) / (m * ν ^ 2))

/-- The explicit periapsis formula. -/
theorem isotropicOscillatorPeriapsisRadius_def (m ν ℓ E : ℝ) :
    isotropicOscillatorPeriapsisRadius m ν ℓ E =
      √((E - √(E ^ 2 - ν ^ 2 * ℓ ^ 2)) / (m * ν ^ 2)) := (rfl)

/-- The explicit apoapsis formula. -/
theorem isotropicOscillatorApoapsisRadius_def (m ν ℓ E : ℝ) :
    isotropicOscillatorApoapsisRadius m ν ℓ E =
      √((E + √(E ^ 2 - ν ^ 2 * ℓ ^ 2)) / (m * ν ^ 2)) := (rfl)

variable {m ν ℓ E r : ℝ}

/-- Completing the square in the effective potential of the isotropic oscillator about its
minimum value `ν |ℓ|`. -/
theorem effectivePotential_isotropicOscillator_sub_min (hm : m ≠ 0) (hr : r ≠ 0) :
    effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r - ν * |ℓ| =
      (m * ν * r ^ 2 - |ℓ|) ^ 2 / (2 * m * r ^ 2) := by
  rw [effectivePotential_apply, ← sq_abs ℓ]
  field_simp
  ring

/-- Every noncollision radius has effective energy at least `ν |ℓ|`. -/
theorem effectivePotential_isotropicOscillator_min_le (hm : 0 < m) (hr : r ≠ 0) :
    ν * |ℓ| ≤ effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r := by
  have h := effectivePotential_isotropicOscillator_sub_min (ν := ν) (ℓ := ℓ) hm.ne' hr
  have : 0 ≤ (m * ν * r ^ 2 - |ℓ|) ^ 2 / (2 * m * r ^ 2) := by positivity
  linarith

/-- The discriminant in the turning-radius formulas, written with the circular energy `ν |ℓ|`. -/
private theorem isotropicOscillator_discriminant_eq (ν ℓ E : ℝ) :
    E ^ 2 - ν ^ 2 * ℓ ^ 2 = E ^ 2 - (ν * |ℓ|) ^ 2 := by
  rw [mul_pow, sq_abs]

/-- The square root in the turning-radius formulas is real on the energy domain and at most `E`,
so both roots in `r²` are nonnegative. -/
private theorem isotropicOscillator_sqrt_discriminant_bounds (hν : 0 < ν) (hmin : ν * |ℓ| ≤ E) :
    0 ≤ E ^ 2 - ν ^ 2 * ℓ ^ 2 ∧ √(E ^ 2 - ν ^ 2 * ℓ ^ 2) ≤ E := by
  have hνℓ : 0 ≤ ν * |ℓ| := mul_nonneg hν.le (abs_nonneg ℓ)
  rw [isotropicOscillator_discriminant_eq]
  exact ⟨by nlinarith, (sqrt_le_left (hνℓ.trans hmin)).2 (by nlinarith)⟩

/-- For `ℓ ≠ 0` the square root in the turning-radius formulas is strictly less than `E`. -/
private theorem isotropicOscillator_sqrt_discriminant_lt (hν : 0 < ν) (hℓ : ℓ ≠ 0)
    (hmin : ν * |ℓ| ≤ E) : √(E ^ 2 - ν ^ 2 * ℓ ^ 2) < E := by
  have hνℓ : 0 < ν * |ℓ| := mul_pos hν (abs_pos.2 hℓ)
  rw [isotropicOscillator_discriminant_eq]
  exact (sqrt_lt' (hνℓ.trans_le hmin)).2 (by nlinarith)

/-- Above the circular energy the square root in the turning-radius formulas is positive. -/
private theorem isotropicOscillator_sqrt_discriminant_pos (hν : 0 ≤ ν) (hmin : ν * |ℓ| < E) :
    0 < √(E ^ 2 - ν ^ 2 * ℓ ^ 2) := by
  have hνℓ : 0 ≤ ν * |ℓ| := mul_nonneg hν (abs_nonneg ℓ)
  rw [isotropicOscillator_discriminant_eq]
  exact sqrt_pos.2 (by nlinarith)

/-- At the circular energy `ν |ℓ|` the discriminant in the turning-radius formulas vanishes. -/
private theorem isotropicOscillator_discriminant_circular (ν ℓ : ℝ) :
    (ν * |ℓ|) ^ 2 - ν ^ 2 * ℓ ^ 2 = 0 := by
  rw [isotropicOscillator_discriminant_eq, sub_self]

/-- The periapsis radius is nonnegative. -/
theorem isotropicOscillatorPeriapsisRadius_nonneg (m ν ℓ E : ℝ) :
    0 ≤ isotropicOscillatorPeriapsisRadius m ν ℓ E :=
  sqrt_nonneg _

/-- The apoapsis radius is nonnegative. -/
theorem isotropicOscillatorApoapsisRadius_nonneg (m ν ℓ E : ℝ) :
    0 ≤ isotropicOscillatorApoapsisRadius m ν ℓ E :=
  sqrt_nonneg _

/-- For zero angular momentum and nonnegative energy the periapsis radius is the collision
radius `0`. -/
theorem isotropicOscillatorPeriapsisRadius_zero (m ν : ℝ) (hE : 0 ≤ E) :
    isotropicOscillatorPeriapsisRadius m ν 0 E = 0 := by
  simp [isotropicOscillatorPeriapsisRadius_def, sqrt_sq hE]

/-- For nonzero angular momentum the periapsis radius is positive: the orbit avoids collision. -/
theorem isotropicOscillatorPeriapsisRadius_pos (hm : 0 < m) (hν : 0 < ν) (hℓ : ℓ ≠ 0)
    (hmin : ν * |ℓ| ≤ E) : 0 < isotropicOscillatorPeriapsisRadius m ν ℓ E := by
  have hs := isotropicOscillator_sqrt_discriminant_lt hν hℓ hmin
  rw [isotropicOscillatorPeriapsisRadius_def]
  exact sqrt_pos.2 (div_pos (sub_pos.2 hs) (by positivity))

/-- The periapsis radius is at most the apoapsis radius. -/
theorem isotropicOscillatorPeriapsisRadius_le_apoapsisRadius (hm : 0 ≤ m) :
    isotropicOscillatorPeriapsisRadius m ν ℓ E ≤ isotropicOscillatorApoapsisRadius m ν ℓ E := by
  rw [isotropicOscillatorPeriapsisRadius_def, isotropicOscillatorApoapsisRadius_def]
  exact sqrt_le_sqrt (div_le_div_of_nonneg_right
    (by linarith [sqrt_nonneg (E ^ 2 - ν ^ 2 * ℓ ^ 2)]) (by positivity))

/-- Above the circular energy the two turning radii are distinct. -/
theorem isotropicOscillatorPeriapsisRadius_lt_apoapsisRadius (hm : 0 < m) (hν : 0 < ν)
    (hmin : ν * |ℓ| < E) :
    isotropicOscillatorPeriapsisRadius m ν ℓ E < isotropicOscillatorApoapsisRadius m ν ℓ E := by
  have hνℓ : 0 ≤ ν * |ℓ| := mul_nonneg hν.le (abs_nonneg ℓ)
  have hd := isotropicOscillator_sqrt_discriminant_pos hν.le hmin
  have hden : 0 < m * ν ^ 2 := by positivity
  rw [isotropicOscillatorPeriapsisRadius_def, isotropicOscillatorApoapsisRadius_def,
    sqrt_lt_sqrt_iff_of_pos (div_pos (by linarith) hden), div_lt_div_iff_of_pos_right hden]
  linarith

/-- Vieta's formulas for the squares of the constructed turning radii, the roots in `r²` of
`(m ν)² r⁴ - 2 m E r² + ℓ² = 0`. -/
private theorem isotropicOscillator_turningRadii_vieta (hm : 0 < m) (hν : 0 < ν)
    (hmin : ν * |ℓ| ≤ E) :
    (isotropicOscillatorPeriapsisRadius m ν ℓ E ^ 2 +
        isotropicOscillatorApoapsisRadius m ν ℓ E ^ 2) * (m * ν ^ 2) = 2 * E ∧
      isotropicOscillatorPeriapsisRadius m ν ℓ E ^ 2 *
          isotropicOscillatorApoapsisRadius m ν ℓ E ^ 2 * (m * ν) ^ 2 = ℓ ^ 2 := by
  obtain ⟨hd, hs⟩ := isotropicOscillator_sqrt_discriminant_bounds hν hmin
  have hden : 0 < m * ν ^ 2 := by positivity
  have hs2 := sq_sqrt hd
  rw [isotropicOscillatorPeriapsisRadius_def, isotropicOscillatorApoapsisRadius_def,
    sq_sqrt (div_nonneg (by linarith) hden.le),
    sq_sqrt (div_nonneg (by linarith [sqrt_nonneg (E ^ 2 - ν ^ 2 * ℓ ^ 2)]) hden.le)]
  generalize √(E ^ 2 - ν ^ 2 * ℓ ^ 2) = s at hs2 ⊢
  constructor
  · field_simp
    ring
  · field_simp
    linear_combination -hs2

/-- Factoring the turning-point polynomial `(m ν)² r⁴ - 2 m E r² + ℓ²` by the squares of the two
turning radii. -/
private theorem isotropicOscillator_radialPolynomial_eq (hm : 0 < m) (hν : 0 < ν)
    (hmin : ν * |ℓ| ≤ E) (r : ℝ) :
    (m * ν) ^ 2 * r ^ 4 - 2 * m * E * r ^ 2 + ℓ ^ 2 =
      (m * ν) ^ 2 * ((r ^ 2 - isotropicOscillatorPeriapsisRadius m ν ℓ E ^ 2) *
        (r ^ 2 - isotropicOscillatorApoapsisRadius m ν ℓ E ^ 2)) := by
  obtain ⟨hsum, hprod⟩ := isotropicOscillator_turningRadii_vieta hm hν hmin
  linear_combination m * r ^ 2 * hsum - hprod

/-- The effective potential minus the energy, with the denominators cleared. -/
private theorem effectivePotential_isotropicOscillator_sub (hm : m ≠ 0) (hr : r ≠ 0) :
    effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r - E =
      ((m * ν) ^ 2 * r ^ 4 - 2 * m * E * r ^ 2 + ℓ ^ 2) / (2 * m * r ^ 2) := by
  rw [effectivePotential_apply]
  field_simp
  ring

/-- The effective potential minus the energy is a positive multiple of the quadratic in `r²`
factored by the squares of the turning radii. -/
private theorem effectivePotential_isotropicOscillator_sub_eq_mul (hm : 0 < m) (hν : 0 < ν)
    (hmin : ν * |ℓ| ≤ E) (hr : r ≠ 0) :
    effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r - E =
      (m * ν) ^ 2 / (2 * m * r ^ 2) *
        ((r ^ 2 - isotropicOscillatorPeriapsisRadius m ν ℓ E ^ 2) *
          (r ^ 2 - isotropicOscillatorApoapsisRadius m ν ℓ E ^ 2)) := by
  rw [effectivePotential_isotropicOscillator_sub hm.ne' hr,
    isotropicOscillator_radialPolynomial_eq hm hν hmin, mul_div_right_comm]

/-- The only positive turning points of the isotropic oscillator are its periapsis and
apoapsis. For `ℓ = 0` the periapsis radius is the collision radius `0`
(`isotropicOscillatorPeriapsisRadius_zero`), so the apoapsis is then the only positive turning
point. -/
theorem effectivePotential_isotropicOscillator_eq_iff (hm : 0 < m) (hν : 0 < ν)
    (hmin : ν * |ℓ| ≤ E) (hr : 0 < r) :
    effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r = E ↔
      r = isotropicOscillatorPeriapsisRadius m ν ℓ E ∨
        r = isotropicOscillatorApoapsisRadius m ν ℓ E := by
  have h₁ := isotropicOscillatorPeriapsisRadius_nonneg m ν ℓ E
  have h₂ := isotropicOscillatorApoapsisRadius_nonneg m ν ℓ E
  have hc : 0 < (m * ν) ^ 2 / (2 * m * r ^ 2) := by positivity
  -- Cancelling the positive factor, the turning-point equation says that `r²` is a root of the
  -- factored quadratic ...
  have key : effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r = E ↔
      (r ^ 2 - isotropicOscillatorPeriapsisRadius m ν ℓ E ^ 2) *
        (r ^ 2 - isotropicOscillatorApoapsisRadius m ν ℓ E ^ 2) = 0 := by
    rw [← sub_eq_zero, effectivePotential_isotropicOscillator_sub_eq_mul hm hν hmin hr.ne',
      mul_eq_zero_iff_left hc.ne']
  -- ... and taking nonnegative square roots identifies `r` with one of the turning radii.
  rw [key, mul_eq_zero, sub_eq_zero, sub_eq_zero, pow_left_inj₀ hr.le h₁ two_ne_zero,
    pow_left_inj₀ hr.le h₂ two_ne_zero]

/-- At an energy `E ≥ ν |ℓ|` the allowed positive radii of the isotropic oscillator form exactly
the closed interval between the turning radii. -/
theorem effectivePotential_isotropicOscillator_le_iff (hm : 0 < m) (hν : 0 < ν)
    (hmin : ν * |ℓ| ≤ E) (hr : 0 < r) :
    effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r ≤ E ↔
      r ∈ Icc (isotropicOscillatorPeriapsisRadius m ν ℓ E)
        (isotropicOscillatorApoapsisRadius m ν ℓ E) := by
  have h₁ := isotropicOscillatorPeriapsisRadius_nonneg m ν ℓ E
  have h₂ := isotropicOscillatorApoapsisRadius_nonneg m ν ℓ E
  have hle := isotropicOscillatorPeriapsisRadius_le_apoapsisRadius (ν := ν) (ℓ := ℓ) (E := E)
    hm.le
  have hc : 0 < (m * ν) ^ 2 / (2 * m * r ^ 2) := by positivity
  -- Cancelling the positive factor, the energy condition says that the factored quadratic is
  -- nonpositive at `r²`, that is, `r²` lies between its roots ...
  have key : effectivePotential m ℓ (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) r ≤ E ↔
      (r ^ 2 - isotropicOscillatorPeriapsisRadius m ν ℓ E ^ 2) *
        (r ^ 2 - isotropicOscillatorApoapsisRadius m ν ℓ E ^ 2) ≤ 0 := by
    rw [← sub_nonpos, effectivePotential_isotropicOscillator_sub_eq_mul hm hν hmin hr.ne']
    exact ⟨fun h ↦ nonpos_of_mul_nonpos_right h hc, mul_nonpos_of_nonneg_of_nonpos hc.le⟩
  -- ... and taking nonnegative square roots puts `r` between the turning radii.
  rw [key, sub_mul_sub_nonpos_iff _ (pow_le_pow_left₀ h₁ hle 2), mem_Icc,
    pow_le_pow_iff_left₀ h₁ hr.le two_ne_zero, pow_le_pow_iff_left₀ hr.le h₂ two_ne_zero]

/-- At the circular energy `ν |ℓ|` the radicand of both turning radii is `|ℓ| / (m ν)`. -/
private theorem isotropicOscillator_circular_div (m ν ℓ : ℝ) :
    ν * |ℓ| / (m * ν ^ 2) = |ℓ| / (m * ν) := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  · field_simp

/-- At the circular energy `ν |ℓ|` the periapsis is the circular radius `√(|ℓ| / (m ν))`. -/
@[simp]
theorem isotropicOscillatorPeriapsisRadius_circular :
    isotropicOscillatorPeriapsisRadius m ν ℓ (ν * |ℓ|) = √(|ℓ| / (m * ν)) := by
  rw [isotropicOscillatorPeriapsisRadius_def, isotropicOscillator_discriminant_circular, sqrt_zero,
    sub_zero, isotropicOscillator_circular_div]

/-- At the circular energy the apoapsis is the circular radius too. -/
@[simp]
theorem isotropicOscillatorApoapsisRadius_circular :
    isotropicOscillatorApoapsisRadius m ν ℓ (ν * |ℓ|) = √(|ℓ| / (m * ν)) := by
  rw [isotropicOscillatorApoapsisRadius_def, isotropicOscillator_discriminant_circular, sqrt_zero,
    add_zero, isotropicOscillator_circular_div]

/-- **The radial action of the isotropic oscillator on its whole energy domain.** For `m > 0`,
`ν > 0`, `ℓ ≠ 0` and `E ≥ ν |ℓ|`, the radial action between the constructed turning radii is
`(E / ν - |ℓ|) / 2`. At the circular energy `E = ν |ℓ|` both sides vanish. -/
theorem isotropicOscillator_radialAction_turningRadii (hm : 0 < m) (hν : 0 < ν) (hℓ : ℓ ≠ 0)
    (hmin : ν * |ℓ| ≤ E) :
    radialAction m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E
        (isotropicOscillatorPeriapsisRadius m ν ℓ E)
        (isotropicOscillatorApoapsisRadius m ν ℓ E) =
      (E / ν - |ℓ|) / 2 := by
  rcases hmin.eq_or_lt with rfl | hmin
  · rw [isotropicOscillatorPeriapsisRadius_circular, isotropicOscillatorApoapsisRadius_circular,
      radialAction_def]
    simp [hν.ne']
  have h₁ := isotropicOscillatorPeriapsisRadius_pos hm hν hℓ hmin.le
  have h₂ := h₁.trans (isotropicOscillatorPeriapsisRadius_lt_apoapsisRadius hm hν hmin)
  have hturn (r : ℝ) (hr : 0 < r)
      (h : r = isotropicOscillatorPeriapsisRadius m ν ℓ E ∨
        r = isotropicOscillatorApoapsisRadius m ν ℓ E) :
      2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) = ℓ ^ 2 / r ^ 2 := by
    have := (effectivePotential_isotropicOscillator_eq_iff hm hν hmin.le hr).2 h
    rw [effectivePotential_apply] at this
    field_simp at this ⊢
    linarith
  exact isotropicOscillator_radialAction hm hν h₁
    (isotropicOscillatorPeriapsisRadius_lt_apoapsisRadius hm hν hmin)
    (hturn _ h₁ (Or.inl rfl)) (hturn _ h₂ (Or.inr rfl))

/-! ### The energy in action variables and its frequencies -/

/-- The isotropic oscillator energy `ν (2 I_r + |I_θ|)` as a function of the radial action
`I.1` and the **signed** angular action `I.2`. Its physical action domain has `0 ≤ I.1` and
`I.2 ≠ 0`. -/
def isotropicOscillatorActionHamiltonian (ν : ℝ) (I : ℝ × ℝ) : ℝ :=
  ν * (2 * I.1 + |I.2|)

/-- The formula for the isotropic oscillator Hamiltonian in action variables. -/
theorem isotropicOscillatorActionHamiltonian_def (ν : ℝ) (I : ℝ × ℝ) :
    isotropicOscillatorActionHamiltonian ν I = ν * (2 * I.1 + |I.2|) := (rfl)

/-- **The isotropic oscillator energy in terms of the actions.** Between two distinct turning
points `0 < r₁ < r₂` of an isotropic oscillator orbit with `m > 0` and `ν > 0`,
`E = ν (2 I_r + |ℓ|)`, where `I_r` is the radial action and `|ℓ|` the angular action. -/
theorem isotropicOscillatorActionHamiltonian_radialAction {r₁ r₂ : ℝ} (hm : 0 < m) (hν : 0 < ν)
    (h₁ : 0 < r₁) (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    isotropicOscillatorActionHamiltonian ν
      (radialAction m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂, ℓ) = E := by
  rw [isotropicOscillatorActionHamiltonian_def, isotropicOscillator_radialAction hm hν h₁ hlt hr₁
    hr₂]
  field_simp
  ring

/-- The energy is `ν (2 I_r + |ℓ|)` on the whole energy domain `E ≥ ν |ℓ|`, including the
circular endpoint, with `I_r` taken between the constructed turning radii. -/
theorem isotropicOscillatorActionHamiltonian_radialAction_turningRadii (hm : 0 < m) (hν : 0 < ν)
    (hℓ : ℓ ≠ 0) (hmin : ν * |ℓ| ≤ E) :
    isotropicOscillatorActionHamiltonian ν
      (radialAction m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E
        (isotropicOscillatorPeriapsisRadius m ν ℓ E)
        (isotropicOscillatorApoapsisRadius m ν ℓ E), ℓ) = E := by
  rw [isotropicOscillatorActionHamiltonian_def,
    isotropicOscillator_radialAction_turningRadii hm hν hℓ hmin]
  field_simp
  ring

/-- The action Hamiltonian is smooth away from zero angular action. -/
theorem contDiffAt_isotropicOscillatorActionHamiltonian (ν : ℝ) {I : ℝ × ℝ} {k : ℕ∞}
    (hℓ : I.2 ≠ 0) : ContDiffAt ℝ k (isotropicOscillatorActionHamiltonian ν) I :=
  contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_fst).add (contDiffAt_snd.abs hℓ))

/-- The full differential of the isotropic oscillator energy in action variables. The angular
coefficient retains the sign factor from the angular action. -/
theorem hasFDerivAt_isotropicOscillatorActionHamiltonian (ν : ℝ) {I : ℝ × ℝ} (hℓ : I.2 ≠ 0) :
    HasFDerivAt (isotropicOscillatorActionHamiltonian ν)
      (ν • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (SignType.sign I.2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) I :=
  (((hasFDerivAt_fst.const_smul (2 : ℝ)).add (hasFDerivAt_snd.abs hℓ)).const_smul
    ν).congr_of_eventuallyEq (.of_forall fun _ ↦ by simp [isotropicOscillatorActionHamiltonian_def])

/-- The radial frequency is `2 ν`, for every angular action. -/
theorem hasDerivAt_isotropicOscillatorActionHamiltonian_fst (ν ℓ J : ℝ) :
    HasDerivAt (fun r ↦ isotropicOscillatorActionHamiltonian ν (r, ℓ)) (2 * ν) J :=
  ((((hasDerivAt_id J).const_mul 2).add_const |ℓ|).const_mul ν).congr_deriv (by ring)

/-- The angular frequency is `sign(ℓ) ν` on each component `ℓ ≠ 0`. -/
theorem hasDerivAt_isotropicOscillatorActionHamiltonian_snd (ν J : ℝ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    HasDerivAt (fun l ↦ isotropicOscillatorActionHamiltonian ν (J, l))
      ((SignType.sign ℓ : ℝ) * ν) ℓ :=
  (((hasDerivAt_abs hℓ).const_add (2 * J)).const_mul ν).congr_deriv (by ring)

/-- The angular frequency is `sign(ℓ) ν`. At `ℓ = 0`, where the energy is not differentiable in
the angular action, both sides are `0`. -/
theorem deriv_isotropicOscillatorActionHamiltonian_snd (ν J ℓ : ℝ) :
    deriv (fun l ↦ isotropicOscillatorActionHamiltonian ν (J, l)) ℓ =
      (SignType.sign ℓ : ℝ) * ν := by
  simp only [isotropicOscillatorActionHamiltonian_def, deriv_const_mul_field', deriv_const_add',
    deriv_abs]
  ring

/-- **The signed isotropic oscillator resonance**: `2 Ω_θ = sign(ℓ) Ω_r`. -/
theorem two_mul_deriv_isotropicOscillatorActionHamiltonian_snd_eq_sign_mul (ν J ℓ : ℝ) :
    2 * deriv (fun l ↦ isotropicOscillatorActionHamiltonian ν (J, l)) ℓ =
      (SignType.sign ℓ : ℝ) * deriv (fun r ↦ isotropicOscillatorActionHamiltonian ν (r, ℓ)) J := by
  rw [deriv_isotropicOscillatorActionHamiltonian_snd,
    (hasDerivAt_isotropicOscillatorActionHamiltonian_fst ν ℓ J).deriv]
  ring

/-- The radial frequency agrees with the angular frequency `2π / T_r` of the radial oscillation,
where `T_r` is the radial period quadrature. -/
theorem deriv_isotropicOscillatorActionHamiltonian_fst_eq_div_radialPeriod {r₁ r₂ : ℝ}
    (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    deriv (fun J ↦ isotropicOscillatorActionHamiltonian ν (J, ℓ))
        (radialAction m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂) =
      2 * π / radialPeriod m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂ := by
  rw [(hasDerivAt_isotropicOscillatorActionHamiltonian_fst ν ℓ _).deriv,
    isotropicOscillator_radialPeriod hm hν h₁ hlt hr₁ hr₂]
  field_simp

/-- The signed angular frequency is the total polar angle swept in one radial period divided by
that period. `apsidalAngle` describes only half of the oscillation. -/
theorem deriv_isotropicOscillatorActionHamiltonian_snd_eq_div_radialPeriod {r₁ r₂ : ℝ}
    (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    deriv (fun l ↦ isotropicOscillatorActionHamiltonian ν
        (radialAction m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂, l)) ℓ =
      2 * apsidalAngle m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂ /
        radialPeriod m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) ℓ E r₁ r₂ := by
  rw [deriv_isotropicOscillatorActionHamiltonian_snd,
    isotropicOscillator_radialPeriod hm hν h₁ hlt hr₁ hr₂,
    isotropicOscillator_apsidalAngle h₁ hlt hr₁ hr₂]
  field_simp

end TauCeti
