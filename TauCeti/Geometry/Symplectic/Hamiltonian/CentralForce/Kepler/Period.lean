/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Collision
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Kepler's equation and the period of bound Kepler motions

A particle of mass `m > 0` in a finite-dimensional real inner product space `V`, moving in the
attractive Kepler potential `-κ / r`, `κ > 0`, follows Hamilton's equations `q' = p / m`,
`p' = -(κ / ‖q‖³) q` for the energy `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖`. This file shows that every
motion of negative energy `H = -κ / (2a)`, `a > 0`, which is defined for all time without
colliding with the centre, is periodic with period

`T = 2π √(m / κ) a^(3/2)`

(`TauCeti.periodic_of_forall_hasDerivAt_kepler`). This is Kepler's third law for the actual
motion: the quadrature `TauCeti.kepler_radialPeriod` computes the same number as an integral
between turning radii, whereas here the motion itself returns to its initial state. By
`TauCeti.maximalIntegralCurveInterval_hamiltonianVectorField_kepler_eq_univ_iff`, the motions
defined for all time are exactly those of nonzero angular momentum.

The proof constructs the **eccentric anomaly** `ψ` of the motion. With `r = ‖q‖`, `s = ⟪q, p⟫`
and `c = √(m κ a)`, the complex number `z = (a - r) + i a s / c` satisfies, by Hamilton's equations
and conservation of energy, the linear equation `z' = i (c / (m a r)) z`. So
`z(t) = ρ e^(i ψ(t))` for the angle `ψ` with `ψ' = c / (m a r)`, where `ρ = |z(0)|`. Writing
`e = ρ / a`, this says

`r = a (1 - e cos ψ)`,  `⟪q, p⟫ = c e sin ψ`.

The number `e` is the eccentricity `‖A‖ / (m κ)` of the orbit, for the Runge–Lenz vector `A`; it
is less than one because a global noncolliding motion in the attractive Kepler potential has
nonzero angular momentum (`TauCeti.sq_sub_inner_sq_ne_zero_of_hasDerivAt`). Differentiating gives
**Kepler's equation**

`ψ - e sin ψ = n t + c₀`, with mean motion `n = √(κ / (m a³))`.

The vectors `P = (a / r) cos ψ q - sin ψ p / (m n)` and
`Q = (a / r) sin ψ q + (cos ψ - e) p / (m n)` are constant along the motion, and recover it:

`q = (cos ψ - e) P + sin ψ Q`,  `p = (m n / (1 - e cos ψ)) (cos ψ Q - sin ψ P)`

(`TauCeti.exists_eccentricAnomaly_of_forall_hasDerivAt_kepler`). The map `x ↦ x - e sin x` is
strictly increasing and commutes with the translation by `2π`, so Kepler's equation forces
`ψ(t + 2π / n) = ψ(t) + 2π`, and the motion has period `2π / n = 2π √(m / κ) a^(3/2)`. Nothing here
uses a plane or polar coordinates: the motion is periodic in every dimension.

## Main results

* `TauCeti.exists_eccentricAnomaly_of_forall_hasDerivAt_kepler`: the eccentric anomaly, Kepler's
  equation and the parametrization of a bound Kepler motion by it.
* `TauCeti.periodic_of_forall_hasDerivAt_kepler`: bound noncolliding Kepler motions are periodic,
  with period `2π √(m / κ) a^(3/2)` for the energy `-κ / (2a)`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.8 (Kepler's equation and the eccentric anomaly).
-/

public section

noncomputable section

open Real Set
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m κ a : ℝ}

/-! ### Newton's equations of the Kepler problem -/

section Newton

variable {q p : ℝ → V}

/-- Along a Kepler motion the distance to the centre has derivative `r' = ⟪q, p⟫ / (m r)`. -/
private theorem hasDerivAt_norm_kepler (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (h0 : ∀ t, q t ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ ‖q t‖) (⟪q t, p t⟫_ℝ / (m * ‖q t‖)) t := by
  refine ((hasFDerivAt_norm_of_ne (h0 t)).comp_hasDerivAt t (hq' t)).congr_deriv ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, real_inner_smul_right,
    smul_eq_mul]
  field_simp

/-- Along a Kepler motion the pairing `⟪q, p⟫` has derivative `‖p‖² / m - κ / r`. -/
private theorem hasDerivAt_inner_kepler (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (t : ℝ) :
    HasDerivAt (fun t ↦ ⟪q t, p t⟫_ℝ) (‖p t‖ ^ 2 / m - κ / ‖q t‖) t := by
  have hr : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 (h0 t)
  refine ((hq' t).inner ℝ (hp' t)).congr_deriv ?_
  simp only [inner_neg_right, real_inner_smul_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- The energy equation `‖p‖² / (2m) - κ / r = -κ / (2a)`, solved for `‖p‖²`. -/
private theorem eq_of_kepler_energy {X r : ℝ} (hm : m ≠ 0)
    (h : X / (2 * m) - κ / r = -κ / (2 * a)) : X = m * (2 * κ / r - κ / a) := by
  have h' : X / (2 * m) = κ / r - κ / (2 * a) := by linear_combination h
  rw [div_eq_iff (mul_ne_zero two_ne_zero hm)] at h'
  rw [h']
  ring

end Newton

/-! ### The eccentric anomaly -/

section Anomaly

variable {q p : ℝ → V} {c : ℝ}

/-- The complex number `z = (a - r) + i a ⟪q, p⟫ / c` of a Kepler motion of energy `-κ / (2a)`
satisfies `z' = i (c / (m a r)) z` when `c² = m κ a`. -/
private theorem hasDerivAt_phasor_kepler (hm : 0 < m) (ha : 0 < a) (hc0 : 0 < c)
    (hc : c ^ 2 = m * κ * a) (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (hE : ∀ t, ‖p t‖ ^ 2 / (2 * m) - κ / ‖q t‖ = -κ / (2 * a)) (t : ℝ) :
    HasDerivAt (fun t ↦ ((a - ‖q t‖ : ℝ) : ℂ) + ((a * ⟪q t, p t⟫_ℝ / c : ℝ) : ℂ) * Complex.I)
      (Complex.I * ((c / (m * a * ‖q t‖) : ℝ) : ℂ) *
        (((a - ‖q t‖ : ℝ) : ℂ) + ((a * ⟪q t, p t⟫_ℝ / c : ℝ) : ℂ) * Complex.I)) t := by
  have hr : 0 < ‖q t‖ := norm_pos_iff.2 (h0 t)
  have h1 := ((hasDerivAt_norm_kepler hq' h0 t).const_sub a).ofReal_comp
  have h2 := ((((hasDerivAt_inner_kepler hq' hp' h0 t).const_mul a).div_const c).ofReal_comp
    ).mul_const Complex.I
  refine (h1.add h2).congr_deriv ?_
  have hp2 := eq_of_kepler_energy hm.ne' (hE t)
  -- Multiplying `x + i y` by `i f` gives `-f y + i f x`; compare real and imaginary parts.
  have hmul (f x y : ℝ) : Complex.I * (f : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((-(f * y) : ℝ) : ℂ) + ((f * x : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hmul]
  congr 2
  · field_simp
  · rw [Complex.ofReal_inj, hp2]
    field_simp
    linear_combination (‖q t‖ - a) * hc

/-- **The eccentric anomaly of a Kepler motion.** Along a Kepler motion of energy `-κ / (2a)`
defined for all time, there are `ρ ≥ 0` and an angle `ψ` with `ψ' = c / (m a r)` such that
`a - r = ρ cos ψ` and `a ⟪q, p⟫ / c = ρ sin ψ`, where `c² = m κ a`. -/
private theorem exists_anomaly_kepler (hm : 0 < m) (ha : 0 < a) (hc0 : 0 < c)
    (hc : c ^ 2 = m * κ * a) (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (hE : ∀ t, ‖p t‖ ^ 2 / (2 * m) - κ / ‖q t‖ = -κ / (2 * a)) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ ψ : ℝ → ℝ, (∀ t, HasDerivAt ψ (c / (m * a * ‖q t‖)) t) ∧
      ∀ t, a - ‖q t‖ = ρ * cos (ψ t) ∧ a * ⟪q t, p t⟫_ℝ / c = ρ * sin (ψ t) := by
  set z : ℝ → ℂ := fun t ↦ ((a - ‖q t‖ : ℝ) : ℂ) + ((a * ⟪q t, p t⟫_ℝ / c : ℝ) : ℂ) * Complex.I
  have hz := hasDerivAt_phasor_kepler hm ha hc0 hc hq' hp' h0 hE
  have hcont : Continuous fun t ↦ c / (m * a * ‖q t‖) :=
    continuous_iff_continuousAt.2 fun t ↦ continuousAt_const.div
      (continuousAt_const.mul (hasDerivAt_norm_kepler hq' h0 t).continuousAt)
      (mul_ne_zero (mul_pos hm ha).ne' (norm_ne_zero_iff.2 (h0 t)))
  set ψ : ℝ → ℝ := fun t ↦ Complex.arg (z 0) + ∫ u in (0 : ℝ)..t, c / (m * a * ‖q u‖)
  have hψ (t : ℝ) : HasDerivAt ψ (c / (m * a * ‖q t‖)) t :=
    ((hcont.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _
  -- The rotated phasor `z e^(-iψ)` has zero derivative, so it is constant.
  have hw (t : ℝ) : HasDerivAt (fun t ↦ z t * Complex.exp (-(ψ t : ℂ) * Complex.I)) 0 t := by
    refine ((hz t).mul ((((hψ t).ofReal_comp).neg.mul_const Complex.I).cexp)).congr_deriv ?_
    ring
  have hconst (t : ℝ) : z t * Complex.exp (-(ψ t : ℂ) * Complex.I) = ‖z 0‖ := by
    rw [is_const_of_hasDerivAt_zero hw t 0]
    calc z 0 * Complex.exp (-(ψ 0 : ℂ) * Complex.I)
        = ‖z 0‖ * Complex.exp ((z 0).arg * Complex.I) * Complex.exp (-(ψ 0 : ℂ) * Complex.I) := by
          rw [Complex.norm_mul_exp_arg_mul_I]
      _ = ‖z 0‖ := by
          rw [mul_assoc, ← Complex.exp_add]
          simp [ψ]
  refine ⟨‖z 0‖, norm_nonneg _, ψ, hψ, fun t ↦ ?_⟩
  have hzt : z t = ‖z 0‖ * Complex.exp ((ψ t : ℂ) * Complex.I) := by
    rw [← hconst t, mul_assoc, ← Complex.exp_add]
    simp
  have hre := congrArg Complex.re hzt
  have him := congrArg Complex.im hzt
  simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im] at hre him
  constructor <;> linarith


variable {ρ : ℝ} {ψ : ℝ → ℝ}

/-- The vector `P = (a / r) cos ψ q - (a² / c) sin ψ p` is constant along a Kepler motion with
eccentric anomaly `ψ`, where `κ = c² / (m a)`. -/
private theorem hasDerivAt_frame_fst_kepler (hm : 0 < m) (ha : 0 < a) (hc0 : 0 < c)
    (hκ : κ = c ^ 2 / (m * a)) (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (hψ : ∀ t, HasDerivAt ψ (c / (m * a * ‖q t‖)) t)
    (hr : ∀ t, ‖q t‖ = a - ρ * cos (ψ t)) (hs : ∀ t, ⟪q t, p t⟫_ℝ = c * ρ * sin (ψ t) / a)
    (t : ℝ) :
    HasDerivAt (fun t ↦ (a * ‖q t‖⁻¹ * cos (ψ t)) • q t - (a ^ 2 / c * sin (ψ t)) • p t) 0 t := by
  have hr0 : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 (h0 t)
  have h1 := ((((hasDerivAt_norm_kepler hq' h0 t).inv hr0).const_mul a).mul
    (hψ t).cos).smul (hq' t)
  have h2 := (((hψ t).sin).const_mul (a ^ 2 / c)).smul (hp' t)
  refine (h1.sub h2).congr_deriv ?_
  -- Compare the coefficients of `p` and of `q`.
  match_scalars
  · simp only [Pi.inv_apply, Pi.mul_apply]
    field_simp
    ring
  · simp only [hs, hκ, Pi.inv_apply]
    rw [hr] at hr0 ⊢
    field_simp
    ring

/-- The vector `Q = (a / r) sin ψ q + (a² / c) (cos ψ - ρ / a) p` is constant along a Kepler
motion with eccentric anomaly `ψ`, where `κ = c² / (m a)`. -/
private theorem hasDerivAt_frame_snd_kepler (hm : 0 < m) (ha : 0 < a) (hc0 : 0 < c)
    (hκ : κ = c ^ 2 / (m * a)) (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (hψ : ∀ t, HasDerivAt ψ (c / (m * a * ‖q t‖)) t)
    (hr : ∀ t, ‖q t‖ = a - ρ * cos (ψ t)) (hs : ∀ t, ⟪q t, p t⟫_ℝ = c * ρ * sin (ψ t) / a)
    (t : ℝ) :
    HasDerivAt (fun t ↦ (a * ‖q t‖⁻¹ * sin (ψ t)) • q t + (a ^ 2 / c * (cos (ψ t) - ρ / a)) • p t)
      0 t := by
  have hr0 : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 (h0 t)
  have h1 := ((((hasDerivAt_norm_kepler hq' h0 t).inv hr0).const_mul a).mul
    (hψ t).sin).smul (hq' t)
  have h2 := ((((hψ t).cos).sub_const (ρ / a)).const_mul (a ^ 2 / c)).smul (hp' t)
  refine (h1.add h2).congr_deriv ?_
  -- Compare the coefficients of `p` and of `q`.
  match_scalars
  · simp only [Pi.inv_apply, Pi.mul_apply]
    field_simp
    ring
  · simp only [hs, hκ, Pi.inv_apply]
    rw [hr] at hr0 ⊢
    field_simp
    linear_combination (-(c * ρ)) * sin_sq_add_cos_sq (ψ t)

omit [InnerProductSpace ℝ V] in
/-- **Kepler's equation.** Along a Kepler motion with eccentric anomaly `ψ`, the function
`ψ - (ρ / a) sin ψ` has the constant derivative `c / (m a²)`, so it is affine in time. -/
private theorem keplerEquation_kepler (hm : 0 < m) (ha : 0 < a) (h0 : ∀ t, q t ≠ 0)
    (hψ : ∀ t, HasDerivAt ψ (c / (m * a * ‖q t‖)) t) (hr : ∀ t, ‖q t‖ = a - ρ * cos (ψ t))
    (t : ℝ) :
    ψ t - ρ / a * sin (ψ t) = c / (m * a ^ 2) * t + (ψ 0 - ρ / a * sin (ψ 0)) := by
  have hd (t : ℝ) :
      HasDerivAt (fun t ↦ ψ t - ρ / a * sin (ψ t) - c / (m * a ^ 2) * t) 0 t := by
    have hr0 : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 (h0 t)
    refine (((hψ t).sub (((hψ t).sin).const_mul (ρ / a))).sub
      ((hasDerivAt_id' t).const_mul _)).congr_deriv ?_
    rw [hr] at hr0 ⊢
    field_simp
    ring
  have := is_const_of_hasDerivAt_zero hd t 0
  simp only [mul_zero, sub_zero] at this
  linarith

/-- **The eccentricity.** If `a - r = ρ cos ψ` and `a ⟪q, p⟫ / c = ρ sin ψ` at time `0`, for
`c² = m κ a` and energy `-κ / (2a)`, then `(ρ / a)² = 1 - ℓ² / (m κ a)` for the squared angular
momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`. -/
private theorem sq_div_eq_kepler (hm : 0 < m) (hκ : 0 < κ) (ha : 0 < a) (hc0 : 0 < c)
    (hc : c ^ 2 = m * κ * a) (h0 : q 0 ≠ 0)
    (hE : ‖p 0‖ ^ 2 / (2 * m) - κ / ‖q 0‖ = -κ / (2 * a))
    (hr : a - ‖q 0‖ = ρ * cos (ψ 0)) (hs : a * ⟪q 0, p 0⟫_ℝ / c = ρ * sin (ψ 0)) :
    (ρ / a) ^ 2 = 1 - (‖q 0‖ ^ 2 * ‖p 0‖ ^ 2 - ⟪q 0, p 0⟫_ℝ ^ 2) / (m * κ * a) := by
  have hp2 := eq_of_kepler_energy hm.ne' hE
  have hr0 : ‖q 0‖ ≠ 0 := norm_ne_zero_iff.2 h0
  -- `ρ² = (a - r)² + (a ⟪q, p⟫ / c)²`.
  have hρ : ρ ^ 2 = (a - ‖q 0‖) ^ 2 + (a * ⟪q 0, p 0⟫_ℝ / c) ^ 2 := by
    rw [hr, hs]
    linear_combination (-ρ ^ 2) * cos_sq_add_sin_sq (ψ 0)
  rw [div_pow, hρ, hp2]
  field_simp
  linear_combination (-(a * ⟪q 0, p 0⟫_ℝ ^ 2)) * hc

/-- **The motion in terms of its eccentric anomaly.** Along a Kepler motion with eccentric
anomaly `ψ`, there are constant vectors `P` and `Q` with `q = (cos ψ - ρ / a) P + sin ψ Q` and
`p = (c / (a² (1 - (ρ / a) cos ψ))) (cos ψ Q - sin ψ P)`. -/
private theorem exists_eq_smul_add_smul_kepler (hm : 0 < m) (ha : 0 < a) (hc0 : 0 < c)
    (hκ : κ = c ^ 2 / (m * a)) (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (hψ : ∀ t, HasDerivAt ψ (c / (m * a * ‖q t‖)) t)
    (hr : ∀ t, ‖q t‖ = a - ρ * cos (ψ t)) (hs : ∀ t, ⟪q t, p t⟫_ℝ = c * ρ * sin (ψ t) / a) :
    ∃ P Q : V, ∀ t, q t = (cos (ψ t) - ρ / a) • P + sin (ψ t) • Q ∧
      p t = (c / (a ^ 2 * (1 - ρ / a * cos (ψ t)))) • (cos (ψ t) • Q - sin (ψ t) • P) := by
  have hP (t : ℝ) := is_const_of_hasDerivAt_zero
    (hasDerivAt_frame_fst_kepler hm ha hc0 hκ hq' hp' h0 hψ hr hs) t 0
  have hQ (t : ℝ) := is_const_of_hasDerivAt_zero
    (hasDerivAt_frame_snd_kepler hm ha hc0 hκ hq' hp' h0 hψ hr hs) t 0
  refine ⟨(a * ‖q 0‖⁻¹ * cos (ψ 0)) • q 0 - (a ^ 2 / c * sin (ψ 0)) • p 0,
    (a * ‖q 0‖⁻¹ * sin (ψ 0)) • q 0 + (a ^ 2 / c * (cos (ψ 0) - ρ / a)) • p 0,
    fun t ↦ ⟨?_, ?_⟩⟩
  -- Compare the coefficients of `q` and of `p`, using `r = a - ρ cos ψ`.
  all_goals
    rw [← hP t, ← hQ t]
    have hr0 : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 (h0 t)
    have h2 : a - ρ * cos (ψ t) ≠ 0 := hr t ▸ hr0
    match_scalars
  · field_simp
    linear_combination hr t - a * sin_sq_add_cos_sq (ψ t)
  · ring
  · field_simp
    linear_combination (-a) * sin_sq_add_cos_sq (ψ t)
  · ring

end Anomaly

/-! ### Bound Kepler motions -/

section Bound

variable {q p : ℝ → V}

/-- **The eccentric anomaly in Newtonian form.** Let `(q, p)` solve Newton's equations
`q' = p / m`, `p' = -(κ / r³) q` of the Kepler problem, avoiding the centre, with energy
`-κ / (2a)` and nonzero angular momentum at time `0`. Then there are `0 ≤ e < 1` with
`e² = 1 - ℓ² / (m κ a)`, an angle `ψ`, constants `c₀`, `P`, `Q` such that Kepler's equation
`ψ - e sin ψ = n t + c₀` holds with `n = √(κ / (m a³))`, and the motion is parametrized by `ψ`. -/
private theorem exists_eccentricAnomaly_kepler (hm : 0 < m) (hκ : 0 < κ) (ha : 0 < a)
    (hq' : ∀ t, HasDerivAt q (m⁻¹ • p t) t)
    (hp' : ∀ t, HasDerivAt p (-((κ / ‖q t‖ ^ 2 / ‖q t‖) • q t)) t) (h0 : ∀ t, q t ≠ 0)
    (hE : ∀ t, ‖p t‖ ^ 2 / (2 * m) - κ / ‖q t‖ = -κ / (2 * a))
    (hℓ : 0 < ‖q 0‖ ^ 2 * ‖p 0‖ ^ 2 - ⟪q 0, p 0⟫_ℝ ^ 2) :
    ∃ e : ℝ, 0 ≤ e ∧ e < 1 ∧ e ^ 2 = 1 - (‖q 0‖ ^ 2 * ‖p 0‖ ^ 2 - ⟪q 0, p 0⟫_ℝ ^ 2) / (m * κ * a) ∧
      ∃ ψ : ℝ → ℝ, ∃ c₀ : ℝ, ∃ P Q : V, ∀ t,
        ψ t - e * sin (ψ t) = √(κ / (m * a ^ 3)) * t + c₀ ∧
        ‖q t‖ = a * (1 - e * cos (ψ t)) ∧
        q t = (cos (ψ t) - e) • P + sin (ψ t) • Q ∧
        p t = (m * √(κ / (m * a ^ 3)) / (1 - e * cos (ψ t))) • (cos (ψ t) • Q - sin (ψ t) • P) := by
  -- `c = √(m κ a)`, written as `m a² n` for the mean motion `n = √(κ / (m a³))`.
  set n := √(κ / (m * a ^ 3)) with hn
  have hn0 : 0 < n := sqrt_pos.2 (by positivity)
  set c := m * a ^ 2 * n with hcdef
  have hc0 : 0 < c := by positivity
  have hc : c ^ 2 = m * κ * a := by
    rw [hcdef, mul_pow, hn, sq_sqrt (by positivity)]
    field_simp
  have hκc : κ = c ^ 2 / (m * a) := by
    rw [hc]
    field_simp
  obtain ⟨ρ, hρ0, ψ, hψ, hrel⟩ := exists_anomaly_kepler hm ha hc0 hc hq' hp' h0 hE
  have hr (t : ℝ) : ‖q t‖ = a - ρ * cos (ψ t) := by linarith [(hrel t).1]
  have hs (t : ℝ) : ⟪q t, p t⟫_ℝ = c * ρ * sin (ψ t) / a := by
    have := (hrel t).2
    rw [div_eq_iff hc0.ne'] at this
    rw [eq_div_iff ha.ne']
    linear_combination this
  have he2 := sq_div_eq_kepler hm hκ ha hc0 hc (h0 0) (hE 0) (hrel 0).1 (hrel 0).2
  have he0 : 0 ≤ ρ / a := div_nonneg hρ0 ha.le
  -- The eccentricity is less than one, since the angular momentum does not vanish.
  have he1 : ρ / a < 1 := by
    refine (sq_lt_one_iff₀ he0).1 ?_
    rw [he2]
    have : 0 < (‖q 0‖ ^ 2 * ‖p 0‖ ^ 2 - ⟪q 0, p 0⟫_ℝ ^ 2) / (m * κ * a) := by positivity
    linarith
  obtain ⟨P, Q, hPQ⟩ := exists_eq_smul_add_smul_kepler hm ha hc0 hκc hq' hp' h0 hψ hr hs
  refine ⟨ρ / a, he0, he1, he2, ψ, ψ 0 - ρ / a * sin (ψ 0), P, Q, fun t ↦
    ⟨?_, ?_, (hPQ t).1, ?_⟩⟩
  · rw [keplerEquation_kepler hm ha h0 hψ hr t, hcdef]
    field_simp
  · rw [hr]
    field_simp
  · rw [(hPQ t).2, hcdef]
    congr 1
    field_simp

end Bound

/-! ### Hamiltonian Kepler motions -/

section Hamiltonian

variable [FiniteDimensional ℝ V] {γ : ℝ → V × V}

/-- A Kepler motion of energy `-κ / (2a)` which is defined for all time and avoids the
centre solves Newton's equations `q' = p / m`, `p' = -(κ / r³) q`, conserves its energy, and has
nonzero angular momentum. -/
private theorem kepler_newton (hm : 0 < m) (hκ : 0 < κ)
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m fun r ↦ -κ / r) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0) = -κ / (2 * a)) :
    (∀ t, HasDerivAt (fun t ↦ (γ t).1) (m⁻¹ • (γ t).2) t) ∧
      (∀ t, HasDerivAt (fun t ↦ (γ t).2)
        (-((κ / ‖(γ t).1‖ ^ 2 / ‖(γ t).1‖) • (γ t).1)) t) ∧
      (∀ t, ‖(γ t).2‖ ^ 2 / (2 * m) - κ / ‖(γ t).1‖ = -κ / (2 * a)) ∧
      0 < ‖(γ 0).1‖ ^ 2 * ‖(γ 0).2‖ ^ 2 - ⟪(γ 0).1, (γ 0).2⟫_ℝ ^ 2 := by
  have hU (t : ℝ) := hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 (hq t))
  have hγ' (t : ℝ) := stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian (m := m)
    (hU t) (hq t) ▸ hγ t
  -- The energy is conserved.
  have hEt (t : ℝ) : centralForceHamiltonian m (fun r ↦ -κ / r) (γ t) = -κ / (2 * a) :=
    ((stdSymplecticForm (V := V)).apply_eq_of_hasDerivWithinAt_hamiltonianVectorField
      isPreconnected_univ (fun t _ ↦ (hγ t).hasDerivWithinAt)
      (fun t _ ↦ (hasFDerivAt_centralForceHamiltonian (m := m) (hU t) (hq t)).differentiableAt)
      (mem_univ 0) (mem_univ t)).trans hE
  refine ⟨fun t ↦ (hγ' t).fst, fun t ↦ (hγ' t).snd, fun t ↦ ?_, ?_⟩
  · have := hEt t
    rw [← Prod.mk.eta (p := γ t), centralForceHamiltonian_apply] at this
    linear_combination this
  -- A global noncolliding motion in the attractive Kepler potential has nonzero angular momentum.
  have hattr (t : ℝ) : 0 < deriv (fun r ↦ -κ / r) ‖(γ t).1‖ := by
    rw [(hU t).deriv]
    exact div_pos hκ (pow_pos (norm_pos_iff.2 (hq t)) 2)
  refine lt_of_le_of_ne ?_ (sq_sub_inner_sq_ne_zero_of_hasDerivAt hm hγ hq
    (fun t ↦ (hU t).differentiableAt) hattr 0).symm
  have := real_inner_mul_inner_self_le (γ 0).1 (γ 0).2
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  linear_combination this

/-- **Kepler's equation.** Let `m, κ, a > 0` and let `γ = (q, p)` be a motion of the Kepler
problem, a solution of Hamilton's equations for `H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` defined for all
time and avoiding the centre, with energy `-κ / (2a)`. Let `e = ‖A‖ / (m κ)` be its eccentricity,
for the Runge–Lenz vector `A` of `γ 0`, and let `n = √(κ / (m a³))` be its mean motion. Then
`0 ≤ e < 1`, and there are an **eccentric anomaly** `ψ : ℝ → ℝ`, a constant `c₀` and vectors
`P`, `Q` such that at every time `t`:

* `ψ - e sin ψ = n t + c₀`;
* `‖q‖ = a (1 - e cos ψ)`;
* `q = (cos ψ - e) P + sin ψ Q`;
* `p = (m n / (1 - e cos ψ)) (cos ψ Q - sin ψ P)`. -/
theorem exists_eccentricAnomaly_of_forall_hasDerivAt_kepler (hm : 0 < m) (hκ : 0 < κ)
    (ha : 0 < a)
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m fun r ↦ -κ / r) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0) = -κ / (2 * a)) {e : ℝ}
    (he : ‖rungeLenz m κ (γ 0)‖ = m * κ * e) :
    0 ≤ e ∧ e < 1 ∧ ∃ ψ : ℝ → ℝ, ∃ c₀ : ℝ, ∃ P Q : V, ∀ t,
      ψ t - e * sin (ψ t) = √(κ / (m * a ^ 3)) * t + c₀ ∧
      ‖(γ t).1‖ = a * (1 - e * cos (ψ t)) ∧
      (γ t).1 = (cos (ψ t) - e) • P + sin (ψ t) • Q ∧
      (γ t).2 = (m * √(κ / (m * a ^ 3)) / (1 - e * cos (ψ t))) •
        (cos (ψ t) • Q - sin (ψ t) • P) := by
  obtain ⟨hq', hp', hE', hℓ⟩ := kepler_newton hm hκ hγ hq hE
  obtain ⟨e', he'0, he'1, he'2, h⟩ := exists_eccentricAnomaly_kepler hm hκ ha hq' hp' hq hE' hℓ
  -- Both `e` and `e'` are nonnegative, with `(m κ e)² = ‖A‖² = (m κ e')²`.
  have hA := norm_rungeLenz_sq hm.ne' κ (hq 0)
  rw [hE, he] at hA
  have hmκ : 0 < m * κ := mul_pos hm hκ
  have he0 : 0 ≤ e := by
    have := he ▸ norm_nonneg (rungeLenz m κ (γ 0))
    exact nonneg_of_mul_nonneg_right (by linarith) hmκ
  have hee : e = e' := by
    refine (pow_left_inj₀ he0 he'0 two_ne_zero).1 ?_
    rw [he'2]
    have : (m * κ) ^ 2 * e ^ 2 = (m * κ) ^ 2 * (1 -
        (‖(γ 0).1‖ ^ 2 * ‖(γ 0).2‖ ^ 2 - ⟪(γ 0).1, (γ 0).2⟫_ℝ ^ 2) / (m * κ * a)) := by
      rw [← mul_pow, hA]
      field_simp
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hmκ.ne') this
  subst hee
  exact ⟨he0, he'1, h⟩

/-- **Bound Kepler motions are periodic (Kepler's third law).** Let `m, κ, a > 0` and let `γ` be a
motion of the Kepler problem, a solution of Hamilton's equations for
`H(q, p) = ‖p‖² / (2m) - κ / ‖q‖` defined for all time and avoiding the centre, with energy
`-κ / (2a)`. Then `γ` is periodic with period `2π √(m / κ) a^(3/2)`. -/
theorem periodic_of_forall_hasDerivAt_kepler (hm : 0 < m) (hκ : 0 < κ) (ha : 0 < a)
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m fun r ↦ -κ / r) (γ t)) t)
    (hq : ∀ t, (γ t).1 ≠ 0)
    (hE : centralForceHamiltonian m (fun r ↦ -κ / r) (γ 0) = -κ / (2 * a)) :
    Function.Periodic γ (2 * π * √(m / κ) * a ^ (3 / 2 : ℝ)) := by
  obtain ⟨hq', hp', hE', hℓ⟩ := kepler_newton hm hκ hγ hq hE
  obtain ⟨e, he0, he1, -, ψ, c₀, P, Q, h⟩ :=
    exists_eccentricAnomaly_kepler hm hκ ha hq' hp' hq hE' hℓ
  set n := √(κ / (m * a ^ 3))
  set T := 2 * π * √(m / κ) * a ^ (3 / 2 : ℝ)
  -- The mean motion `n` advances by `2π` over the period: `n T = 2π`.
  have hnT : n * T = 2 * π := by
    have h32 : a ^ (3 / 2 : ℝ) = √(a ^ 3) := by
      rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul ha.le]
      norm_num
    have hT : √(κ / (m * a ^ 3)) * (√(m / κ) * a ^ (3 / 2 : ℝ)) = 1 := by
      rw [h32, ← mul_assoc, ← sqrt_mul (by positivity), ← sqrt_mul (by positivity), sqrt_eq_one]
      field_simp
    linear_combination (2 * π) * hT
  -- `x ↦ x - e sin x` is strictly increasing, since `e < 1`.
  have hmono : StrictMono fun x ↦ x - e * sin x := by
    refine strictMono_of_deriv_pos fun x ↦ ?_
    have hd : HasDerivAt (fun x ↦ x - e * sin x) (1 - e * cos x) x :=
      (hasDerivAt_id' x).sub ((hasDerivAt_sin x).const_mul e)
    rw [hd.deriv]
    nlinarith [neg_one_le_cos x, cos_le_one x]
  have hψ (t : ℝ) : ψ (t + T) = ψ t + 2 * π := by
    refine hmono.injective ?_
    simp only [sin_add_two_pi]
    linear_combination (h (t + T)).1 - (h t).1 + hnT
  intro t
  ext
  · rw [(h (t + T)).2.2.1, (h t).2.2.1, hψ, cos_add_two_pi, sin_add_two_pi]
  · rw [(h (t + T)).2.2.2, (h t).2.2.2, hψ, cos_add_two_pi, sin_add_two_pi]

end Hamiltonian

end TauCeti
