/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Motion
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.RotationAngle
import TauCeti.Analysis.InnerProductSpace.Euclidean.VerticalRotation
import TauCeti.Analysis.ODE.ScalarLinear
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The first return of the spherical pendulum

The phase space of the spherical pendulum is `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` inside
`ℝ³ × ℝ³`, with energy `H(q, p) = ‖p‖² / 2 + q₃` and vertical angular momentum
`J(q, p) = q₁ p₂ - q₂ p₁`. The Hamiltonian flow of `J`, the **rotation flow**, rotates positions
and momenta about the vertical axis with unit angular velocity. This file shows that, starting
from the lower turning point of the height, one oscillation of the height under the energy flow
moves the pendulum exactly as the rotation flow does in the time `Θ(h, j)`, the rotation angle
(`TauCeti.sphericalPendulumRotationAngle`):

`φ_H^T(x) = φ_J^Θ(x)`,

where `T = T(h, j)` is the period of the height (`TauCeti.sphericalPendulumPeriod`). This
**first-return identity** is the input for the rotation number of the pendulum's Liouville tori
and for its Hamiltonian monodromy around the focus–focus value `(1, 0)`.

* **The azimuth equation.** Write the horizontal position as the complex number `q₁ + q₂ i`. On the
  phase space `(1 - q₃²) (p₁ + p₂ i) = (-q₃ p₃ + J i) (q₁ + q₂ i)`, which says that the horizontal
  direction `(q₁ + q₂ i) / √(1 - q₃²)`, a point of the unit circle, turns with angular velocity
  `J / (1 - q₃²)`. So along a motion off the poles it turns by `∫ j dt / (1 - q₃²)`
  (`TauCeti.div_sqrt_eq_exp_integral_mul_I_mul_of_isMIntegralCurveOn_sphericalPendulum`).
* **The rotation integral.** Changing variables from time to height, `dt = dz / |p₃|`, as for the
  period, the angle swept during one oscillation of the height is
  `2 ∫_{z₋}^{z₊} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²)) = Θ(h, j)`
  (`TauCeti.integral_div_one_sub_sq_eq_sphericalPendulumRotationAngle_of_isMIntegralCurveOn`).
* **The first return.** At a turning point `p₃ = 0`, so the point of the phase space is determined
  by its height, its horizontal position and `J`. After one oscillation the height and `J` are
  back, and the horizontal position has been rotated by `Θ(h, j)`; the rotation flow does the same
  in the time `Θ(h, j)`
  (`TauCeti.horizontal_eq_exp_mul_and_apply_two_eq_of_isMIntegralCurveOn_angularMomentum`,
  `TauCeti.apply_add_sphericalPendulumPeriod_eq_apply_sphericalPendulumRotationAngle`).

The motions here are integral curves on intervals of times, and no completeness of the flows is
used. The identity is stated for a motion starting at the lower turning point; it is not proved
here for other initial points of the same orbit.

## Main declarations

* `TauCeti.horizontal_eq_exp_mul_and_apply_two_eq_of_isMIntegralCurveOn_angularMomentum`:
  the rotation flow rotates positions and momenta about the vertical axis with unit angular
  velocity, multiplying their horizontal coordinates `x₁ + x₂ i` by `exp ((b - a) i)`
  (via `TauCeti.isIntegralCurveOn_angularMomentum_of_isMIntegralCurveOn`, its motions in `ℝ³ × ℝ³`).
* `TauCeti.div_sqrt_eq_exp_integral_mul_I_mul_of_isMIntegralCurveOn_sphericalPendulum`: the
  horizontal direction turns by `∫ j dt / (1 - q₃²)`.
* `TauCeti.integral_div_one_sub_sq_eq_sphericalPendulumRotationAngle_of_isMIntegralCurveOn`: over
  one oscillation of the height this angle is the rotation angle `Θ(h, j)`.
* `TauCeti.apply_add_sphericalPendulumPeriod_eq_apply_sphericalPendulumRotationAngle`: the
  first-return identity `φ_H^T(x) = φ_J^Θ(x)`.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum, its rotation number and monodromy).
* K. Efstathiou, A. Giacobbe, P. Mardešić and D. Sugny, *Rotation forms and local Hamiltonian
  monodromy*, arXiv:1608.01579, Section III (the first-return map of the spherical pendulum).
-/

public section

open Complex Set
open scoped InnerProductSpace

namespace TauCeti

/-- On the phase space the horizontal momentum is determined by the position, the vertical
momentum `p₃` and the vertical angular momentum `J`: in the horizontal coordinates `q₁ + q₂ i` and
`p₁ + p₂ i`, `(1 - q₃²) (p₁ + p₂ i) = (-q₃ p₃ + J i) (q₁ + q₂ i)`. -/
private theorem one_sub_sq_mul_horizontal_snd
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    ((1 - x.1 2 ^ 2 : ℝ) : ℂ) * ((x.2 0 : ℂ) + x.2 1 * I) =
      ((-(x.1 2 * x.2 2) : ℝ) + ((sphericalPendulumEnergyMomentum x).2 : ℂ) * I) *
        ((x.1 0 : ℂ) + x.1 1 * I) := by
  obtain ⟨hq, hqp⟩ := sum_sq_eq_one_and_sum_mul_eq_zero_of_mem_sphericalPendulumPhaseSpace hx
  obtain ⟨q, p⟩ := x
  have hqc : (q 0 : ℂ) ^ 2 + (q 1 : ℂ) ^ 2 + (q 2 : ℂ) ^ 2 = 1 := by exact_mod_cast hq
  have hqpc : (q 0 : ℂ) * p 0 + (q 1 : ℂ) * p 1 + (q 2 : ℂ) * p 2 = 0 := by exact_mod_cast hqp
  simp only [sphericalPendulumEnergyMomentum_apply, ofReal_sub, ofReal_one, ofReal_pow, ofReal_mul,
    ofReal_neg]
  -- With `Q = q₁ + q₂ i`, `P = p₁ + p₂ i` and `J = q₁ p₂ - q₂ p₁`, the difference of the two sides
  -- is `-P (‖q‖² - 1) + Q ⟪q, p⟫ - J q₂ (i² + 1)`.
  linear_combination (-((p 0 : ℂ) + p 1 * I)) * hqc + ((q 0 : ℂ) + q 1 * I) * hqpc -
    ((q 0 : ℂ) * p 1 - q 1 * p 0) * q 1 * I_sq

/-- The motions of the rotation flow of the spherical pendulum, the integral curves of the
Hamiltonian vector field of the vertical angular momentum `J` on the phase space, solve
`q' = ⟪q, e₁⟫ e₂ - ⟪q, e₂⟫ e₁`, `p' = ⟪p, e₁⟫ e₂ - ⟪p, e₂⟫ e₁` in `ℝ³ × ℝ³`. -/
theorem isIntegralCurveOn_angularMomentum_of_isMIntegralCurveOn
    {β : ℝ → sphericalPendulumPhaseSpace} {s : Set ℝ}
    (hβ : IsMIntegralCurveOn β (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
        (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) s) :
    IsIntegralCurveOn (fun t ↦ (β t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      (fun _ ↦ (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).hamiltonianVectorField
        (angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1))) s :=
  TauCeti.isMIntegralCurveOn_iff_isIntegralCurveOn.1 <|
    hβ.map_of_mfderiv_eq (f := Subtype.val)
      (W := fun x ↦ (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).hamiltonianVectorField
        (angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)) x)
      (fun t _ ↦ (isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
        (β t)).mdifferentiableAt (by simp))
      fun t _ ↦ mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_angularMomentum (β t)

/-- **The rotation flow of the spherical pendulum.** Along a motion `β` of the Hamiltonian vector
field of the vertical angular momentum on a preconnected set of times, between times `a` and `b`
the position and the momentum are rotated about the vertical axis by the angle `b - a`: their
horizontal coordinates are multiplied by `exp ((b - a) i)` and their vertical components are
unchanged. -/
theorem horizontal_eq_exp_mul_and_apply_two_eq_of_isMIntegralCurveOn_angularMomentum
    {β : ℝ → sphericalPendulumPhaseSpace} {s : Set ℝ} (hs : IsPreconnected s)
    (hβ : IsMIntegralCurveOn β (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
        (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) s) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) :
    ((((β b : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 0 : ℂ) +
        (β b : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 1 * I =
      exp (((b - a : ℝ) : ℂ) * I) *
        (((β a : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 0 : ℂ) +
          (β a : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 1 * I)) ∧
      (β b : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        (β a : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2) ∧
    ((((β b : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 0 : ℂ) +
        (β b : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 1 * I =
      exp (((b - a : ℝ) : ℂ) * I) *
        (((β a : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 0 : ℂ) +
          (β a : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 1 * I)) ∧
      (β b : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 =
        (β a : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2) := by
  have hx := isIntegralCurveOn_angularMomentum_of_isMIntegralCurveOn hβ
  refine ⟨hs.ofReal_apply_add_ofReal_apply_mul_I_eq_exp_mul_and_apply_two_eq
      (v := fun t ↦ (β t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1)
      (fun t ht ↦ ?_) ha hb,
    hs.ofReal_apply_add_ofReal_apply_mul_I_eq_exp_mul_and_apply_two_eq
      (v := fun t ↦ (β t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2)
      (fun t ht ↦ ?_) ha hb⟩
  · simpa [Function.comp_def, stdSymplecticForm_hamiltonianVectorField_angularMomentum] using
      (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  · simpa [Function.comp_def, stdSymplecticForm_hamiltonianVectorField_angularMomentum] using
      (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)

/-- Along a motion of the spherical pendulum, at a time `t` off the poles, the horizontal direction
`(q₁ + q₂ i) / √(1 - q₃²)` turns with angular velocity `J / (1 - q₃²)`: its derivative at `t` is
its value times `J i / (1 - q₃²)`. -/
private theorem hasDerivWithinAt_div_sqrt_of_isMIntegralCurveOn
    {γ : ℝ → sphericalPendulumPhaseSpace} {s : Set ℝ} {t : ℝ}
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) s) (ht : t ∈ s)
    (hz : (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 < 1) :
    HasDerivWithinAt (fun t ↦
      (((γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 0 : ℂ) +
        (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 1 * I) /
        (√(1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) : ℂ))
      (((((sphericalPendulumEnergyMomentum (γ t)).2 /
          (1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) : ℝ) : ℂ) * I) •
        ((((γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 0 : ℂ) +
          (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 1 * I) /
          (√(1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) : ℂ)))
      s t := by
  have hz1 : 0 < 1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 :=
    sub_pos.2 hz
  have hq := ((ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivWithinAt t
    (isIntegralCurveOn_sphericalPendulumVectorField hγ t ht)).ofReal_apply_add_ofReal_apply_mul_I
      0 1
  have hr := ((((hasDerivWithinAt_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum hγ
    ht).pow 2).const_sub 1).sqrt hz1.ne').ofReal_comp
  have hρ0 := (Real.sqrt_pos.2 hz1).ne'
  refine (hq.div hr (ofReal_ne_zero.2 hρ0)).congr_deriv ?_
  have key := one_sub_sq_mul_horizontal_snd (γ t).property
  have hρ := Real.sq_sqrt hz1.le
  simp only [Function.comp_apply, ContinuousLinearMap.coe_fst', Pi.pow_apply,
    sphericalPendulumVectorField_def, smul_eq_mul] at key ⊢
  generalize (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) = y at key hρ hρ0 ⊢
  generalize √(1 - y.1 2 ^ 2) = ρ at hρ hρ0 ⊢
  have hρc : (ρ : ℂ) ^ 2 = 1 - (y.1 2 : ℂ) ^ 2 := by exact_mod_cast hρ
  have hρρ : (ρ : ℂ) * (ρ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (ofReal_ne_zero.2 hρ0)
  push_cast at key ⊢
  rw [← hρc] at key ⊢
  -- With `Q = q₁ + q₂ i` and `P = p₁ + p₂ i`, the difference of the two sides is
  -- `ρ⁻³ (ρ² P - (-q₃ p₃ + J i) Q) - P ρ ρ⁻² (ρ ρ⁻¹ - 1)`, which vanishes by `key` and `ρ ρ⁻¹ = 1`.
  linear_combination (ρ : ℂ)⁻¹ ^ 3 * key -
    ((y.2 0 : ℂ) + y.2 1 * I) * ρ * (ρ : ℂ)⁻¹ ^ 2 * hρρ

/-- **The azimuth of the spherical pendulum turns with angular velocity `J / (1 - q₃²)`.** Let a
motion of the spherical pendulum on `[t₁, t₂]` have vertical angular momentum `j` and stay off the
poles, `q₃² < 1`. Then its horizontal direction `(q₁ + q₂ i) / √(1 - q₃²)`, a point of the unit
circle, turns by the angle `∫_{t₁}^{t₂} j dt / (1 - q₃²)`:

`(q₁ + q₂ i)(t₂) / √(1 - q₃(t₂)²) =`
`exp (i ∫_{t₁}^{t₂} j dt / (1 - q₃(t)²)) · (q₁ + q₂ i)(t₁) / √(1 - q₃(t₁)²)`. -/
theorem div_sqrt_eq_exp_integral_mul_I_mul_of_isMIntegralCurveOn_sphericalPendulum
    {γ : ℝ → sphericalPendulumPhaseSpace} {t₁ t₂ j : ℝ} (ht : t₁ ≤ t₂)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) (Icc t₁ t₂))
    (hj : (sphericalPendulumEnergyMomentum (γ t₁)).2 = j)
    (hz : ∀ t ∈ Icc t₁ t₂,
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 < 1) :
    (((γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 0 : ℂ) +
        (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 1 * I) /
        (√(1 - (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) : ℂ) =
      exp (((∫ t in t₁..t₂,
          j / (1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) : ℝ) : ℂ) *
          I) *
        ((((γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 0 : ℂ) +
          (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 1 * I) /
          (√(1 - (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) : ℂ)) := by
  have hJ (t : ℝ) (ht' : t ∈ Icc t₁ t₂) : (sphericalPendulumEnergyMomentum (γ t)).2 = j :=
    (congrArg Prod.snd (sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn
      isPreconnected_Icc hγ (left_mem_Icc.2 ht) ht')).trans hj
  set x : ℝ → EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) := fun t ↦ γ t
  -- The angular velocity `j / (1 - q₃²)`, extended continuously to all times by clamping.
  set c : ℝ → ℝ := fun u ↦ max t₁ (min t₂ u)
  have hc (u : ℝ) : c u ∈ Icc t₁ t₂ := ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
  have hcu (u : ℝ) (hu : u ∈ Icc t₁ t₂) : c u = u := by simp [c, hu.1, hu.2]
  set ω : ℝ → ℝ := fun u ↦ j / (1 - (x (c u)).1 2 ^ 2)
  have hzc : ContinuousOn (fun t ↦ (x t).1 2) (Icc t₁ t₂) := fun t ht' ↦
    (hasDerivWithinAt_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum hγ
      ht').continuousWithinAt
  have hωc : Continuous ω :=
    continuous_const.div (continuous_const.sub ((hzc.comp_continuous (by fun_prop) hc).pow 2))
      fun u ↦ (sub_pos.2 (hz _ (hc u))).ne'
  set A : ℝ → ℝ := fun t ↦ ∫ u in t₁..t, ω u
  have hA₂ : A t₂ = ∫ t in t₁..t₂, j / (1 - (x t).1 2 ^ 2) :=
    intervalIntegral.integral_congr fun u hu ↦ by
      rw [uIcc_of_le ht] at hu
      simp only [ω, hcu u hu]
  have hA (t : ℝ) (ht' : t ∈ Icc t₁ t₂) : HasDerivAt A ((sphericalPendulumEnergyMomentum
      (γ t)).2 / (1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2)) t := by
    convert (hωc.integral_hasStrictDerivAt t₁ t).hasDerivAt using 1
    simp only [ω, hcu t ht', hJ t ht', x]
  -- The horizontal direction turns with angular velocity `A'`, so it is rotated by `A t₂ - A t₁`.
  have h := isPreconnected_Icc.eq_exp_sub_smul_of_hasDerivWithinAt (A := fun t ↦ (A t : ℂ) * I)
    (fun t ht' ↦ ((hA t ht').ofReal_comp.mul_const I).hasDerivWithinAt)
    (fun t ht' ↦ hasDerivWithinAt_div_sqrt_of_isMIntegralCurveOn hγ ht' (hz t ht'))
    (left_mem_Icc.2 ht) (right_mem_Icc.2 ht)
  rwa [smul_eq_mul, ← sub_mul, ← ofReal_sub, hA₂, show A t₁ = 0 from intervalIntegral.integral_same,
    sub_zero] at h

/-- Along a motion of the spherical pendulum on a preconnected set of times, with nonzero vertical
angular momentum at one time, the pendulum stays off the poles: `q₃² < 1`. -/
private theorem sq_lt_one_of_isMIntegralCurveOn {γ : ℝ → sphericalPendulumPhaseSpace} {s : Set ℝ}
    (hs : IsPreconnected s)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hj : (sphericalPendulumEnergyMomentum (γ t₀)).2 ≠ 0) {t : ℝ} (ht : t ∈ s) :
    (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 < 1 := by
  have hI := apply_two_mem_Ioo_of_snd_sphericalPendulumEnergyMomentum_ne_zero (γ t).property
    (by rwa [sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn hs hγ ht₀ ht])
  nlinarith [hI.1, hI.2]

/-- **The rotation integral of the spherical pendulum.** Above the curve of relative equilibria,
let a motion of the spherical pendulum with energy `h` and vertical angular momentum `j` start at
the lower turning point `z₋` at time `t₁`, reach the upper turning point `z₊` at time `t₂` and
return to `z₋` at time `t₃`, with its height strictly between the turning points at all other
times. Then the angle `∫_{t₁}^{t₃} j dt / (1 - q₃²)` swept by its azimuth is the rotation angle
`Θ(h, j)`. -/
theorem integral_div_one_sub_sq_eq_sphericalPendulumRotationAngle_of_isMIntegralCurveOn
    {γ : ℝ → sphericalPendulumPhaseSpace} {h j z₀ t₁ t₂ t₃ : ℝ} (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h)
    (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) (Icc t₁ t₃))
    (hF : sphericalPendulumEnergyMomentum (γ t₁) = (h, j))
    (h₁ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j)
    (h₂ : (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumUpperTurningPoint h j)
    (h₃ : (γ t₃ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j)
    (hmem : ∀ t ∈ Ioo t₁ t₂ ∪ Ioo t₂ t₃,
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈
        Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j)) :
    ∫ t in t₁..t₃, j / (1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2) =
      sphericalPendulumRotationAngle h j := by
  have hpos := fun z ↦ two_mul_sub_mul_one_sub_sq_sub_sq_pos (z := z) hj hz₀ hV
  have hcont : ContinuousOn (fun t ↦ j /
      (1 - (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2)) (Icc t₁ t₃) :=
    continuousOn_const.div (continuousOn_const.sub (ContinuousOn.pow (fun t ht ↦
      (hasDerivWithinAt_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum hγ
        ht).continuousWithinAt) 2)) fun t ht ↦ (sub_pos.2 (sq_lt_one_of_isMIntegralCurveOn
          isPreconnected_Icc hγ (left_mem_Icc.2 (ht₁₂.trans ht₂₃)) (by rw [hF]; exact hj) ht)).ne'
  -- Each half of the oscillation sweeps `∫_{z₋}^{z₊} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`.
  have hup := integral_comp_eq_integral_div_sqrt_of_isMIntegralCurveOn_sphericalPendulum ht₁₂
    (hγ.mono (Icc_subset_Icc_right ht₂₃)) hF hpos (Or.inl ⟨h₁, h₂⟩)
    (fun t ht ↦ hmem t (Or.inl ht)) fun z ↦ j / (1 - z ^ 2)
  have hdown := integral_comp_eq_integral_div_sqrt_of_isMIntegralCurveOn_sphericalPendulum ht₂₃
    (hγ.mono (Icc_subset_Icc_left ht₁₂)) ((sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn
      isPreconnected_Icc hγ (left_mem_Icc.2 (ht₁₂.trans ht₂₃)) ⟨ht₁₂, ht₂₃⟩).trans hF) hpos
    (Or.inr ⟨h₂, h₃⟩) (fun t ht ↦ hmem t (Or.inr ht)) fun z ↦ j / (1 - z ^ 2)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hcont.mono (Icc_subset_Icc_right ht₂₃)).intervalIntegrable_of_Icc ht₁₂)
    ((hcont.mono (Icc_subset_Icc_left ht₁₂)).intervalIntegrable_of_Icc ht₂₃), hup, hdown,
    sphericalPendulumRotationAngle_eq_integral hj hz₀ hV]
  simp only [div_div]
  ring

/-- At the lower turning point the vertical momentum vanishes, so the horizontal momentum is
determined by the horizontal position: on the fibre over `(h, j)` above the curve of relative
equilibria, two points at the height `z₋` whose horizontal positions differ by a factor `c` also
have horizontal momenta differing by `c`. -/
private theorem horizontal_snd_eq_mul_of_apply_two_eq_sphericalPendulumLowerTurningPoint
    {h j z₀ : ℝ} (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h)
    {x y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) (hy : y ∈ sphericalPendulumPhaseSpace)
    (hFx : sphericalPendulumEnergyMomentum x = (h, j))
    (hFy : sphericalPendulumEnergyMomentum y = (h, j))
    (hzx : x.1 2 = sphericalPendulumLowerTurningPoint h j)
    (hzy : y.1 2 = sphericalPendulumLowerTurningPoint h j) {c : ℂ}
    (hq : (y.1 0 : ℂ) + y.1 1 * I = c * (x.1 0 + x.1 1 * I)) :
    (y.2 0 : ℂ) + y.2 1 * I = c * (x.2 0 + x.2 1 * I) ∧ y.2 2 = x.2 2 := by
  have hp (w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (hw : w ∈ sphericalPendulumPhaseSpace) (hFw : sphericalPendulumEnergyMomentum w = (h, j))
      (hzw : w.1 2 = sphericalPendulumLowerTurningPoint h j) : w.2 2 = 0 := by
    have h2 := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace hw
    rw [hFw, hzw, two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV] at h2
    simpa using h2
  have ha := neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hs : ((1 - sphericalPendulumLowerTurningPoint h j ^ 2 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (sub_pos.2 (by nlinarith)).ne'
  have keyx := one_sub_sq_mul_horizontal_snd hx
  have keyy := one_sub_sq_mul_horizontal_snd hy
  rw [hFx, hzx, hp x hx hFx hzx] at keyx
  rw [hFy, hzy, hp y hy hFy hzy, hq] at keyy
  refine ⟨mul_left_cancel₀ hs ?_, (hp y hy hFy hzy).trans (hp x hx hFx hzx).symm⟩
  linear_combination keyy - c * keyx

/-- **The first return of the spherical pendulum.** Above the curve of relative equilibria, let a
motion `γ` of the spherical pendulum with energy `h` and vertical angular momentum `j` start at the
lower turning point `z₋` at time `t₁`, reach the upper turning point `z₊` at time `t₂` and return to
`z₋` at time `t₃`, with its height strictly between the turning points at all other times, so that
`t₃ - t₁` is the period `T(h, j)` of the height. Let `β` be a motion of the rotation flow, the
Hamiltonian flow of the vertical angular momentum `J`, through the same initial point, defined for
the times between `0` and the rotation angle `Θ(h, j)`. Then after one period the pendulum is where
the rotation flow takes it in the time `Θ(h, j)`:

`φ_H^T(x) = φ_J^Θ(x)`.

In other words, during one oscillation of the height the azimuth advances by `Θ(h, j)`, while
the height and the vertical momentum return to their initial values. -/
theorem apply_add_sphericalPendulumPeriod_eq_apply_sphericalPendulumRotationAngle
    {γ β : ℝ → sphericalPendulumPhaseSpace} {h j z₀ t₁ t₂ t₃ : ℝ} (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h)
    (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) (Icc t₁ t₃))
    (hF : sphericalPendulumEnergyMomentum (γ t₁) = (h, j))
    (h₁ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j)
    (h₂ : (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumUpperTurningPoint h j)
    (h₃ : (γ t₃ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j)
    (hmem : ∀ t ∈ Ioo t₁ t₂ ∪ Ioo t₂ t₃,
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈
        Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j))
    (hβ : IsMIntegralCurveOn β (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
        (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      (uIcc 0 (sphericalPendulumRotationAngle h j)))
    (hβ₀ : β 0 = γ t₁) :
    γ (t₁ + sphericalPendulumPeriod h j) = β (sphericalPendulumRotationAngle h j) := by
  rw [← sub_eq_sphericalPendulumPeriod_of_isMIntegralCurveOn hj hz₀ hV ht₁₂ ht₂₃ hγ hF h₁ h₂ h₃
    hmem, add_sub_cancel]
  have ht₁₃ := ht₁₂.trans ht₂₃
  have hz := fun t (ht : t ∈ Icc t₁ t₃) ↦ sq_lt_one_of_isMIntegralCurveOn isPreconnected_Icc hγ
    (left_mem_Icc.2 ht₁₃) (by rw [hF]; exact hj) ht
  -- The horizontal position is rotated by `Θ`.
  have hQ := div_sqrt_eq_exp_integral_mul_I_mul_of_isMIntegralCurveOn_sphericalPendulum ht₁₃ hγ
    (congrArg Prod.snd hF) hz
  have hρ : (√(1 - sphericalPendulumLowerTurningPoint h j ^ 2) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 (sub_pos.2 (h₁ ▸ hz t₁ (left_mem_Icc.2 ht₁₃)))).ne'
  rw [integral_div_one_sub_sq_eq_sphericalPendulumRotationAngle_of_isMIntegralCurveOn hj hz₀ hV
    ht₁₂ ht₂₃ hγ hF h₁ h₂ h₃ hmem, h₁, h₃, ← mul_div_assoc, div_left_inj₀ hρ] at hQ
  -- So is the momentum, since both points are at the lower turning point.
  obtain ⟨hP, hP₂⟩ := horizontal_snd_eq_mul_of_apply_two_eq_sphericalPendulumLowerTurningPoint hj
    hz₀ hV (γ t₁).property (γ t₃).property hF
    ((sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn
      isPreconnected_Icc hγ (left_mem_Icc.2 ht₁₃) (right_mem_Icc.2 ht₁₃)).trans hF) h₁ h₃ hQ
  -- The rotation flow rotates the initial point by `Θ` as well.
  obtain ⟨⟨hβq, hβq₂⟩, hβp, hβp₂⟩ :=
    horizontal_eq_exp_mul_and_apply_two_eq_of_isMIntegralCurveOn_angularMomentum
      isPreconnected_uIcc hβ left_mem_uIcc right_mem_uIcc
  simp only [hβ₀, sub_zero] at hβq hβq₂ hβp hβp₂
  have hq := hQ.trans hβq.symm
  have hp := hP.trans hβp.symm
  apply Subtype.ext
  refine Prod.ext (PiLp.ext fun i ↦ ?_) (PiLp.ext fun i ↦ ?_) <;> fin_cases i
  · simpa using congrArg re hq
  · simpa using congrArg im hq
  · exact h₃.trans (h₁.symm.trans hβq₂.symm)
  · simpa using congrArg re hp
  · simpa using congrArg im hp
  · exact hP₂.trans hβp₂.symm

end TauCeti
