/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Action–angle coordinates of the harmonic oscillator

A harmonic oscillator of mass `m > 0` and angular frequency `ν > 0` has phase space the
standard symplectic plane `ℝ × ℝ` of positions `q` and momenta `p`, with
`ω₀ = dq ∧ dp`, and Hamiltonian

`H(q, p) = p² / (2m) + m ν² q² / 2`

(`TauCeti.oscillatorHamiltonian`, defined with Hamilton's equations `q' = p / m`, `p' = -m ν² q`
in `TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic`).

Its action–angle parametrization (`TauCeti.oscillatorActionAngle`) is

`(θ, I) ↦ (√(2I / (m ν)) sin θ, √(2 m ν I) cos θ)`.

For `I > 0` this is a symplectic change of coordinates in which the oscillator becomes a uniform
rotation of the angle:

* it pulls `H` back to `ν I`, so `I` is the action `E / ν` of an orbit of energy `E`;
* its derivative carries the standard form `dθ ∧ dI` to `dq ∧ dp`, where `θ` plays the role of
  the position and `I` that of the momentum, so `ω₀ = dθ ∧ dI` in these coordinates;
* it carries the vector field `ν ∂_θ` to the Hamiltonian vector field of `H`, so
  `t ↦ (θ + ν t, I)` parametrizes an integral curve of Hamilton's equations through the point
  with coordinates `(θ, I)`.

The parametrization is `2π`-periodic in `θ`. Conversely, every point of the plane has action
`TauCeti.oscillatorAction m ν x = H x / ν` and angle `TauCeti.oscillatorAngle m ν x`, a point of
`Real.Angle = ℝ / 2πℤ`, and is the image of every lift of its angle together with its action. Off
the origin, the action and the angle determine the point, so the parametrization identifies
`ℝ × (0, ∞)` modulo `2πℤ` in the angle with the punctured plane.

Every orbit of positive energy is periodic, with period lattice `(2π / ν) ℤ`, independent of the
energy: the integral curve through `(θ, I)` returns to its starting point at time `t` exactly when
`t` is an integer multiple of `2π / ν`. Its action is the classical loop integral
`I = (1 / 2π) ∮ p dq` over one period.

## Main definitions

* `TauCeti.oscillatorActionAngle m ν`: the action–angle parametrization.
* `TauCeti.oscillatorAction m ν`, `TauCeti.oscillatorAngle m ν`: the action and angle of a point.

## Main results

* `TauCeti.oscillatorHamiltonian_oscillatorActionAngle`: `H` is `ν I` in action–angle coordinates.
* `TauCeti.stdSymplecticForm_fderiv_oscillatorActionAngle`: the parametrization is symplectic.
* `TauCeti.fderiv_oscillatorActionAngle_apply_frequency`: the Hamiltonian vector field is `ν ∂_θ`.
* `TauCeti.hasDerivAt_oscillatorActionAngle`: `t ↦ (θ + ν t, I)` solves Hamilton's equations.
* `TauCeti.oscillatorActionAngle_eq_oscillatorActionAngle_iff`: off the origin, a point determines
  its action and its angle modulo `2π`.
* `TauCeti.oscillatorActionAngle_oscillatorAction`: every point is the image of its angle and its
  action.
* `TauCeti.oscillatorActionAngle_add_eq_self_iff`: the period lattice is `(2π / ν) ℤ`.
* `TauCeti.integral_oscillatorActionAngle_snd_mul_deriv_fst`: `∮ p dq = 2π I` over one period.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, §50 (action–angle variables of the harmonic oscillator).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §18.
-/

public section

noncomputable section

namespace TauCeti

open Real ContinuousLinearMap

variable {m ν : ℝ}

/-! ### The action–angle parametrization -/

/-- The **action–angle parametrization** `(θ, I) ↦ (√(2I / (m ν)) sin θ, √(2 m ν I) cos θ)` of
the phase plane of the harmonic oscillator of mass `m` and angular frequency `ν`. It is written
as `(√(2I) sin θ / √(m ν), √(m ν) √(2I) cos θ)`. -/
def oscillatorActionAngle (m ν : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (√(2 * y.2) / √(m * ν) * Real.sin y.1, √(m * ν) * √(2 * y.2) * Real.cos y.1)

theorem oscillatorActionAngle_apply (m ν : ℝ) (y : ℝ × ℝ) :
    oscillatorActionAngle m ν y =
      (√(2 * y.2) / √(m * ν) * Real.sin y.1, √(m * ν) * √(2 * y.2) * Real.cos y.1) :=
  (rfl)

/-- The parametrization only depends on the angle modulo `2π`. -/
theorem oscillatorActionAngle_eq_of_coe_eq {θ θ' : ℝ} (h : (θ : Real.Angle) = θ') (I : ℝ) :
    oscillatorActionAngle m ν (θ, I) = oscillatorActionAngle m ν (θ', I) := by
  have hs : Real.sin θ = Real.sin θ' := by rw [← Real.Angle.sin_coe, h, Real.Angle.sin_coe]
  have hc : Real.cos θ = Real.cos θ' := by rw [← Real.Angle.cos_coe, h, Real.Angle.cos_coe]
  simp [oscillatorActionAngle_apply, hs, hc]

/-- In action–angle coordinates the energy is `ν I`. -/
theorem oscillatorHamiltonian_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν) {y : ℝ × ℝ}
    (hI : 0 ≤ y.2) : oscillatorHamiltonian m ν (oscillatorActionAngle m ν y) = ν * y.2 := by
  have hc : √(m * ν) ^ 2 = m * ν := sq_sqrt (by positivity)
  have hr : √(2 * y.2) ^ 2 = 2 * y.2 := sq_sqrt (by positivity)
  have hc0 : √(m * ν) ≠ 0 := by positivity
  rw [oscillatorHamiltonian_apply, oscillatorActionAngle_apply]
  field_simp
  rw [hc, hr]
  linear_combination 2 * m * ν * y.2 * (m * ν) * Real.sin_sq_add_cos_sq y.1 +
    2 * y.2 * Real.cos y.1 ^ 2 * (√(m * ν) ^ 2 + m * ν) * hc

/-- The derivative of the action–angle parametrization at a point of positive action. Writing
`r = √(2I)` and `c = √(m ν)`, it sends `(δθ, δI)` to
`(δθ r cos θ / c + δI sin θ / (r c), -δθ c r sin θ + δI c cos θ / r)`. -/
theorem hasFDerivAt_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν) {y : ℝ × ℝ} (hI : 0 < y.2) :
    HasFDerivAt (oscillatorActionAngle m ν)
      (((√(2 * y.2) * Real.cos y.1 / √(m * ν)) • fst ℝ ℝ ℝ +
          (Real.sin y.1 / (√(2 * y.2) * √(m * ν))) • snd ℝ ℝ ℝ).prod
        ((-(√(m * ν) * √(2 * y.2) * Real.sin y.1)) • fst ℝ ℝ ℝ +
          (√(m * ν) * Real.cos y.1 / √(2 * y.2)) • snd ℝ ℝ ℝ)) y := by
  have hr0 : √(2 * y.2) ≠ 0 := by positivity
  have hc0 : √(m * ν) ≠ 0 := by positivity
  have hsqrt : HasFDerivAt (fun z : ℝ × ℝ ↦ √(2 * z.2))
      ((1 / (2 * √(2 * y.2))) • ((2 : ℝ) • snd ℝ ℝ ℝ)) y :=
    ((hasFDerivAt_snd (p := y)).const_mul (2 : ℝ)).sqrt (mul_pos two_pos hI).ne'
  have hsin := (Real.hasDerivAt_sin y.1).comp_hasFDerivAt y (hasFDerivAt_fst (𝕜 := ℝ) (p := y))
  have hcos := (Real.hasDerivAt_cos y.1).comp_hasFDerivAt y (hasFDerivAt_fst (𝕜 := ℝ) (p := y))
  have h := ((hsqrt.mul_const (√(m * ν))⁻¹).mul hsin).prodMk ((hsqrt.const_mul √(m * ν)).mul hcos)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (.of_forall fun z ↦ ?_)
  · ext <;> simp <;> field_simp
  · simp [oscillatorActionAngle_apply, div_eq_mul_inv]

/-- **The action–angle parametrization is symplectic**: at every point of positive action its
derivative pulls the standard form `dq ∧ dp` back to the standard form `dθ ∧ dI`. -/
theorem stdSymplecticForm_fderiv_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν) {y : ℝ × ℝ}
    (hI : 0 < y.2) (u v : ℝ × ℝ) :
    stdSymplecticForm (fderiv ℝ (oscillatorActionAngle m ν) y u)
        (fderiv ℝ (oscillatorActionAngle m ν) y v) =
      stdSymplecticForm u v := by
  have hr0 : √(2 * y.2) ≠ 0 := by positivity
  have hc0 : √(m * ν) ≠ 0 := by positivity
  rw [(hasFDerivAt_oscillatorActionAngle hm hν hI).fderiv]
  simp only [stdSymplecticForm_apply, RCLike.inner_apply, RCLike.conj_to_real, prod_apply,
    add_apply, smul_apply, coe_fst', coe_snd', smul_eq_mul]
  field_simp
  linear_combination (u.1 * v.2 - u.2 * v.1) * √(2 * y.2) ^ 2 * Real.sin_sq_add_cos_sq y.1

/-- **The Hamiltonian vector field is `ν ∂_θ`**: at a point of positive action, the derivative of
the parametrization sends `(ν, 0)` to the Hamiltonian vector field of the energy. -/
theorem fderiv_oscillatorActionAngle_apply_frequency (hm : 0 < m) (hν : 0 < ν) {y : ℝ × ℝ}
    (hI : 0 < y.2) :
    fderiv ℝ (oscillatorActionAngle m ν) y (ν, 0) =
      (stdSymplecticForm (V := ℝ)).hamiltonianVectorField (oscillatorHamiltonian m ν)
        (oscillatorActionAngle m ν y) := by
  have hc : √(m * ν) ^ 2 = m * ν := sq_sqrt (by positivity)
  have hc0 : √(m * ν) ≠ 0 := by positivity
  rw [(hasFDerivAt_oscillatorActionAngle hm hν hI).fderiv,
    stdSymplecticForm_hamiltonianVectorField_oscillatorHamiltonian, oscillatorActionAngle_apply]
  ext
  · simp
    field_simp
    linear_combination -Real.cos y.1 * hc
  · simp
    field_simp
    linear_combination Real.sin y.1 * hc

/-- **Uniform rotation of the angle solves Hamilton's equations**: for `I ≥ 0`, the curve
`t ↦ (θ + ν t, I)` in action–angle coordinates is an integral curve of the Hamiltonian vector
field of the energy. For `I = 0` it is the constant curve at the equilibrium at the origin. -/
theorem hasDerivAt_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν) (θ : ℝ) {I : ℝ} (hI : 0 ≤ I)
    (t : ℝ) :
    HasDerivAt (fun s ↦ oscillatorActionAngle m ν (θ + ν * s, I))
      ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField (oscillatorHamiltonian m ν)
        (oscillatorActionAngle m ν (θ + ν * t, I))) t := by
  rcases hI.eq_or_lt with rfl | hI
  · have h0 (s : ℝ) : oscillatorActionAngle m ν (s, 0) = 0 := by
      simp [oscillatorActionAngle_apply]
    simp only [h0, stdSymplecticForm_hamiltonianVectorField_oscillatorHamiltonian, Prod.fst_zero,
      Prod.snd_zero, zero_div, mul_zero, neg_zero, Prod.mk_zero_zero]
    exact hasDerivAt_const t 0
  have hcurve : HasDerivAt (fun s : ℝ ↦ (θ + ν * s, I)) (ν, 0) t := by
    simpa only [mul_one] using
      (((hasDerivAt_id' t).const_mul ν).const_add θ).prodMk (hasDerivAt_const t I)
  have hψ := hasFDerivAt_oscillatorActionAngle hm hν (y := (θ + ν * t, I)) hI
  rw [← fderiv_oscillatorActionAngle_apply_frequency hm hν (y := (θ + ν * t, I)) hI, hψ.fderiv]
  exact hψ.comp_hasDerivAt t hcurve

/-! ### Action and angle of a point -/

/-- The **action** `H / ν` of a point of the phase plane of the harmonic oscillator. -/
def oscillatorAction (m ν : ℝ) (x : ℝ × ℝ) : ℝ :=
  oscillatorHamiltonian m ν x / ν

theorem oscillatorAction_apply (m ν : ℝ) (x : ℝ × ℝ) :
    oscillatorAction m ν x = oscillatorHamiltonian m ν x / ν :=
  (rfl)

/-- The complex number `p / √(m ν) + i √(m ν) q` whose modulus and argument are `√(2I)` and the
angle of `(q, p)`. -/
private def oscillatorComplex (m ν : ℝ) (x : ℝ × ℝ) : ℂ :=
  ⟨x.2 / √(m * ν), √(m * ν) * x.1⟩

/-- The **angle** of a point of the phase plane of the harmonic oscillator, a point of
`Real.Angle = ℝ / 2πℤ`: the argument of `p / √(m ν) + i √(m ν) q`. -/
def oscillatorAngle (m ν : ℝ) (x : ℝ × ℝ) : Real.Angle :=
  Complex.arg (oscillatorComplex m ν x)

theorem oscillatorAngle_apply (m ν : ℝ) (x : ℝ × ℝ) :
    oscillatorAngle m ν x = (Complex.arg ⟨x.2 / √(m * ν), √(m * ν) * x.1⟩ : Real.Angle) :=
  (rfl)

/-- The angle of the origin is `0`. -/
@[simp]
theorem oscillatorAngle_zero (m ν : ℝ) : oscillatorAngle m ν 0 = 0 := by
  have h : oscillatorComplex m ν 0 = 0 :=
    Complex.ext (by simp [oscillatorComplex]) (by simp [oscillatorComplex])
  rw [oscillatorAngle, h, Complex.arg_zero, Real.Angle.coe_zero]

private theorem norm_oscillatorComplex (hm : 0 < m) (hν : 0 < ν) (x : ℝ × ℝ) :
    ‖oscillatorComplex m ν x‖ = √(2 * oscillatorAction m ν x) := by
  have hc : √(m * ν) ^ 2 = m * ν := sq_sqrt (by positivity)
  have hc0 : √(m * ν) ≠ 0 := by positivity
  rw [Complex.norm_def, Complex.normSq_apply, oscillatorComplex, oscillatorAction_apply,
    oscillatorHamiltonian_apply]
  congr 1
  field_simp
  linear_combination (√(m * ν) ^ 2 * m * ν * x.1 ^ 2 - x.2 ^ 2) * hc

/-- The action is nonnegative. -/
theorem oscillatorAction_nonneg (hm : 0 < m) (hν : 0 < ν) (x : ℝ × ℝ) :
    0 ≤ oscillatorAction m ν x := by
  rw [oscillatorAction_apply, oscillatorHamiltonian_apply]
  positivity

/-- The action of the point with action–angle coordinates `(θ, I)` is `I`. -/
@[simp]
theorem oscillatorAction_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν) {y : ℝ × ℝ}
    (hI : 0 ≤ y.2) : oscillatorAction m ν (oscillatorActionAngle m ν y) = y.2 := by
  rw [oscillatorAction_apply, oscillatorHamiltonian_oscillatorActionAngle hm hν hI,
    mul_div_cancel_left₀ _ hν.ne']

/-- The angle of the point with action–angle coordinates `(θ, I)`, `I > 0`, is `θ` modulo `2π`. -/
@[simp]
theorem oscillatorAngle_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν) {y : ℝ × ℝ}
    (hI : 0 < y.2) : oscillatorAngle m ν (oscillatorActionAngle m ν y) = y.1 := by
  have hc0 : √(m * ν) ≠ 0 := by positivity
  have h : oscillatorComplex m ν (oscillatorActionAngle m ν y) =
      (√(2 * y.2) : ℝ) * (Real.Angle.cos y.1 + Real.Angle.sin y.1 * Complex.I) := by
    apply Complex.ext <;>
      simp [oscillatorComplex, oscillatorActionAngle_apply, Real.Angle.cos_coe,
        Real.Angle.sin_coe, Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> field_simp
  rw [oscillatorAngle, h, Complex.arg_mul_cos_add_sin_mul_I_coe_angle (by positivity)]

/-- **Every point is the image of its action and angle**: for every lift `θ` of the angle of `x`,
the point with action–angle coordinates `(θ, H x / ν)` is `x`. This includes the origin, whose
action is `0`. -/
theorem oscillatorActionAngle_oscillatorAction (hm : 0 < m) (hν : 0 < ν) {x : ℝ × ℝ} {θ : ℝ}
    (hθ : (θ : Real.Angle) = oscillatorAngle m ν x) :
    oscillatorActionAngle m ν (θ, oscillatorAction m ν x) = x := by
  have hc0 : √(m * ν) ≠ 0 := by positivity
  have hcos : Real.cos θ = Real.cos (Complex.arg (oscillatorComplex m ν x)) := by
    rw [← Real.Angle.cos_coe, hθ, oscillatorAngle, Real.Angle.cos_coe]
  have hsin : Real.sin θ = Real.sin (Complex.arg (oscillatorComplex m ν x)) := by
    rw [← Real.Angle.sin_coe, hθ, oscillatorAngle, Real.Angle.sin_coe]
  have hre := Complex.norm_mul_cos_arg (oscillatorComplex m ν x)
  have him := Complex.norm_mul_sin_arg (oscillatorComplex m ν x)
  rw [norm_oscillatorComplex hm hν] at hre him
  rw [oscillatorActionAngle_apply, hcos, hsin, mul_assoc, hre, div_mul_eq_mul_div, him]
  ext <;> simp [oscillatorComplex] <;> field_simp

/-- **Off the origin, a point determines its action and its angle.** Two points of positive
action have the same image exactly when their actions agree and their angles agree modulo
`2π`. -/
theorem oscillatorActionAngle_eq_oscillatorActionAngle_iff (hm : 0 < m) (hν : 0 < ν)
    {y y' : ℝ × ℝ} (hI : 0 < y.2) (hI' : 0 < y'.2) :
    oscillatorActionAngle m ν y = oscillatorActionAngle m ν y' ↔
      y.2 = y'.2 ∧ (y.1 : Real.Angle) = y'.1 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₂, h₁⟩ ↦ ?_⟩
  · rw [← oscillatorAction_oscillatorActionAngle hm hν hI.le, h,
      oscillatorAction_oscillatorActionAngle hm hν hI'.le]
  · rw [← oscillatorAngle_oscillatorActionAngle hm hν hI, h,
      oscillatorAngle_oscillatorActionAngle hm hν hI']
  · rw [← Prod.mk.eta (p := y), ← Prod.mk.eta (p := y'), h₂,
      oscillatorActionAngle_eq_of_coe_eq h₁]

/-- The points of positive action are exactly the points off the origin. -/
theorem oscillatorAction_pos_iff (hm : 0 < m) (hν : 0 < ν) {x : ℝ × ℝ} :
    0 < oscillatorAction m ν x ↔ x ≠ 0 := by
  constructor
  · rintro h rfl
    simp [oscillatorAction_apply, oscillatorHamiltonian_apply] at h
  · intro h
    have hx : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
      by_contra! h'
      exact h (Prod.ext h'.1 h'.2)
    rw [oscillatorAction_apply, oscillatorHamiltonian_apply]
    rcases hx with hx | hx <;> positivity

/-! ### The period lattice and the action integral -/

/-- **The period lattice of the harmonic oscillator** is `(2π / ν) ℤ`: the integral curve
`t ↦ (θ + ν t, I)` of Hamilton's equations (`TauCeti.hasDerivAt_oscillatorActionAngle`), `I > 0`, is
back at its starting point at time `t` exactly when `t` is an integer multiple of `2π / ν`. The
period does not depend on the energy. -/
theorem oscillatorActionAngle_add_eq_self_iff (hm : 0 < m) (hν : 0 < ν) (θ : ℝ) {I : ℝ}
    (hI : 0 < I) (t : ℝ) :
    oscillatorActionAngle m ν (θ + ν * t, I) = oscillatorActionAngle m ν (θ, I) ↔
      t ∈ AddSubgroup.zmultiples (2 * π / ν) := by
  rw [oscillatorActionAngle_eq_oscillatorActionAngle_iff hm hν hI hI, Real.Angle.coe_add,
    add_eq_left, Real.Angle.coe_eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  simp only [true_and, zsmul_eq_mul]
  refine exists_congr fun n ↦ ?_
  rw [mul_div_assoc', div_eq_iff hν.ne', mul_comm t]

/-- **The action as a loop integral**: over one period of the orbit of action `I ≥ 0`,
parametrized by the angle, the integral `∮ p dq` of the Liouville form is `2π I`. -/
theorem integral_oscillatorActionAngle_snd_mul_deriv_fst (hm : 0 < m) (hν : 0 < ν) {I : ℝ}
    (hI : 0 ≤ I) :
    ∫ θ in (0 : ℝ)..2 * π, (oscillatorActionAngle m ν (θ, I)).2 *
        deriv (fun θ ↦ (oscillatorActionAngle m ν (θ, I)).1) θ =
      2 * π * I := by
  have hc0 : √(m * ν) ≠ 0 := by positivity
  have hr : √(2 * I) ^ 2 = 2 * I := sq_sqrt (by positivity)
  have hfst : (fun θ ↦ (oscillatorActionAngle m ν (θ, I)).1) =
      fun θ ↦ √(2 * I) / √(m * ν) * Real.sin θ := by
    ext θ
    simp [oscillatorActionAngle_apply]
  have hderiv (θ : ℝ) : deriv (fun θ ↦ (oscillatorActionAngle m ν (θ, I)).1) θ =
      √(2 * I) / √(m * ν) * Real.cos θ := by
    rw [hfst]
    exact ((Real.hasDerivAt_sin θ).const_mul _).deriv
  have hint (θ : ℝ) : (oscillatorActionAngle m ν (θ, I)).2 *
      deriv (fun θ ↦ (oscillatorActionAngle m ν (θ, I)).1) θ = 2 * I * Real.cos θ ^ 2 := by
    rw [hderiv, oscillatorActionAngle_apply]
    field_simp
    rw [hr]
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul, integral_cos_sq]
  simp
  ring

end TauCeti
