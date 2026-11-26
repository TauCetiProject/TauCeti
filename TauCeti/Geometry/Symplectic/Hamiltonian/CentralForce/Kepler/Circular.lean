/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Stability

/-!
# The circular Kepler orbits are stable and elliptic

A particle of mass `m` with angular momentum `ℓ ≠ 0` in the Kepler potential `-κ / r` moves
radially according to the reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + V_ℓ(r)`, with the
effective potential

`V_ℓ(r) = ℓ² / (2 m r²) - κ / r`.

Its derivative is `V_ℓ'(r) = κ / r² - ℓ² / (m r³)`
(`TauCeti.hasDerivAt_effectivePotential_kepler`), which for `κ ≠ 0` vanishes at a radius
`r ≠ 0` exactly at the circular radius `r₀ = ℓ² / (m κ)`
(`TauCeti.deriv_effectivePotential_kepler_eq_zero_iff`). The second derivative is
`V_ℓ''(r) = 3 ℓ² / (m r⁴) - 2 κ / r³` (`TauCeti.hasDerivAt_deriv_effectivePotential_kepler`), and at
the circular radius

`V_ℓ''(r₀) = m³ κ⁴ / ℓ⁶ > 0`

(`TauCeti.hasDerivAt_deriv_effectivePotential_kepler_circular`). So `r₀` is a nondegenerate minimum
of `V_ℓ`, and the general theory of circular orbits of central forces in
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Stability` applies.

* **Stability.** For `m, κ > 0` the circular orbit `(r₀, 0)` is a Lyapunov stable equilibrium of
  the reduced system: radial motions starting near it stay near it at all times
  (`TauCeti.eventually_forall_mem_kepler_circular`). The Kepler potential is smooth off `r = 0`,
  so no differentiability hypothesis on the motions is needed.
* **Ellipticity.** The linearization `A` of the reduced Hamiltonian vector field at `(r₀, p_r)`
  satisfies `A² = -ν²` with `ν = m κ² / |ℓ|³`
  (`TauCeti.fderiv_hamiltonianVectorField_kepler_circular_comp_self`), so `A` has no real
  eigenvalue (`TauCeti.not_hasEigenvalue_fderiv_hamiltonianVectorField_kepler_circular`): the
  circular orbit is an elliptic equilibrium, with linearized eigenvalues `± i ν`.

The linearized frequency `ν` is the radial frequency of the Kepler problem in action–angle
variables. The Kepler energy in the radial action `I_r` and the angular action `ℓ` is
`H = -m κ² / (2 (I_r + |ℓ|)²)`, the circular orbit has `I_r = 0`, and its radial frequency
`Ω_r = ∂H/∂I_r` at `I_r = 0` is `m κ² / |ℓ|³ = ν`
(`TauCeti.deriv_keplerActionHamiltonian_fst_zero`). Hence `A² = -Ω_r²`
(`TauCeti.fderiv_hamiltonianVectorField_kepler_circular_comp_self_eq_neg_sq_deriv`): the small
radial oscillations about the circular orbit have the frequency of the nearby Kepler ellipses.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 25.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Sections 3.6 and 3.7.
-/

public section

namespace TauCeti

open Filter Set Topology

variable {m κ ℓ r : ℝ}

/-! ### Derivatives of the Kepler effective potential -/

/-- Away from `r = 0`, the derivative of the Kepler effective potential
`V_ℓ(r) = ℓ² / (2 m r²) - κ / r` is `V_ℓ'(r) = κ / r² - ℓ² / (m r³)`. -/
theorem hasDerivAt_effectivePotential_kepler (hr : r ≠ 0) :
    HasDerivAt (effectivePotential m ℓ fun r ↦ -κ / r) (κ / r ^ 2 - ℓ ^ 2 / (m * r ^ 3)) r :=
  hasDerivAt_effectivePotential (hasDerivAt_kepler_potential κ hr) hr

/-- **The critical point of the Kepler effective potential.** For `κ ≠ 0`, a radius `r ≠ 0` is a
critical point of the effective potential exactly when it is the circular radius `ℓ² / (m κ)`.
For `m = 0` both sides are false: the effective potential is `-κ / r`, and `ℓ² / (m κ) = 0`. -/
theorem deriv_effectivePotential_kepler_eq_zero_iff (hκ : κ ≠ 0) (hr : r ≠ 0) :
    deriv (effectivePotential m ℓ fun r ↦ -κ / r) r = 0 ↔ r = ℓ ^ 2 / (m * κ) := by
  rw [(hasDerivAt_effectivePotential_kepler hr).deriv, sub_eq_zero]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hκ, hr]
  rw [eq_div_iff (mul_ne_zero hm hκ)]
  constructor <;> intro h
  · field_simp at h
    linear_combination h
  · field_simp
    linear_combination h

/-- Away from `r = 0`, the second derivative of the Kepler effective potential is
`V_ℓ''(r) = 3 ℓ² / (m r⁴) - 2 κ / r³`. -/
theorem hasDerivAt_deriv_effectivePotential_kepler (hr : r ≠ 0) :
    HasDerivAt (deriv (effectivePotential m ℓ fun r ↦ -κ / r))
      (3 * ℓ ^ 2 / (m * r ^ 4) - 2 * κ / r ^ 3) r := by
  -- Near `r`, the derivative is the closed formula of `hasDerivAt_effectivePotential_kepler`.
  have hfun : (fun s ↦ κ * (s ^ 2)⁻¹ - ℓ ^ 2 / m * (s ^ 3)⁻¹) =ᶠ[𝓝 r]
      deriv (effectivePotential m ℓ fun r ↦ -κ / r) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    rw [(hasDerivAt_effectivePotential_kepler hs).deriv]
    ring
  refine (((((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).const_mul κ).sub
    (((hasDerivAt_pow 3 r).inv (pow_ne_zero 3 hr)).const_mul (ℓ ^ 2 / m))).congr_of_eventuallyEq
      hfun.symm).congr_deriv ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [div_zero, zero_mul, sub_zero]
    field_simp
    ring
  · field_simp
    ring

/-- **The circular Kepler orbit is a nondegenerate minimum.** For `m, κ, ℓ ≠ 0`, the second
derivative of the Kepler effective potential at the circular radius `r₀ = ℓ² / (m κ)` is
`V_ℓ''(r₀) = m³ κ⁴ / ℓ⁶`, which is positive. -/
theorem hasDerivAt_deriv_effectivePotential_kepler_circular (hm : m ≠ 0) (hκ : κ ≠ 0)
    (hℓ : ℓ ≠ 0) :
    HasDerivAt (deriv (effectivePotential m ℓ fun r ↦ -κ / r)) (m ^ 3 * κ ^ 4 / ℓ ^ 6)
      (ℓ ^ 2 / (m * κ)) := by
  refine (hasDerivAt_deriv_effectivePotential_kepler (by positivity)).congr_deriv ?_
  field_simp
  ring

/-! ### Stability of the circular orbit -/

/-- Near a radius `r ≠ 0`, the Kepler potential `-κ / r` is differentiable. -/
private theorem eventually_differentiableAt_kepler_potential (hr : r ≠ 0) :
    ∀ᶠ s in 𝓝 r, DifferentiableAt ℝ (fun r ↦ -κ / r) s :=
  (eventually_ne_nhds hr).mono fun _ hs ↦ (hasDerivAt_kepler_potential κ hs).differentiableAt

/-- **The circular Kepler orbits are stable.** For a positive mass `m`, an attractive coupling
`κ > 0` and angular momentum `ℓ ≠ 0`, the circular orbit `(ℓ² / (m κ), 0)` of the reduced Kepler
system is Lyapunov stable: for every neighbourhood `W` of it, every radial motion `γ` passing close
enough to it stays in `W` at all times of its open preconnected time interval `T`. The radial
motions are the integral curves in the half-plane `r > 0` of the reduced Hamiltonian vector
field. -/
theorem eventually_forall_mem_kepler_circular (hm : 0 < m) (hκ : 0 < κ) (hℓ : ℓ ≠ 0)
    {W : Set (ℝ × ℝ)} (hW : W ∈ 𝓝 ((ℓ ^ 2 / (m * κ), 0) : ℝ × ℝ)) :
    ∀ᶠ y in 𝓝 ((ℓ ^ 2 / (m * κ), 0) : ℝ × ℝ), ∀ (γ : ℝ → ℝ × ℝ) (T : Set ℝ), IsOpen T →
      IsPreconnected T →
      (∀ t ∈ T, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ fun r ↦ -κ / r)) (γ t)) t) →
      (∀ t ∈ T, 0 < (γ t).1) → ∀ t₀ ∈ T, γ t₀ = y → ∀ t ∈ T, γ t ∈ W := by
  have hr₀ : 0 < ℓ ^ 2 / (m * κ) := by positivity
  filter_upwards [eventually_forall_mem_of_deriv_effectivePotential_eq_zero_of_pos hm hr₀
    (eventually_differentiableAt_kepler_potential hr₀.ne')
    ((deriv_effectivePotential_kepler_eq_zero_iff hκ.ne' hr₀.ne').2 rfl)
    (hasDerivAt_deriv_effectivePotential_kepler_circular hm.ne' hκ.ne' hℓ) (by positivity) hW]
    with y hy γ T hT hT' hγ hpos
  exact hy γ T hT hT' hγ hpos fun t ht ↦
    (hasDerivAt_kepler_potential κ (hpos t ht).ne').differentiableAt

/-! ### The linearization at the circular orbit -/

/-- **The linearization at the circular Kepler orbit.** Let `m κ > 0` and `ℓ ≠ 0`, so that the
circular radius `r₀ = ℓ² / (m κ)` is positive. At every point `(r₀, p_r)`, the derivative `A` of
the reduced Hamiltonian vector field satisfies `A² = -ν²` with `ν = m κ² / |ℓ|³`. -/
theorem fderiv_hamiltonianVectorField_kepler_circular_comp_self (hmκ : 0 < m * κ) (hℓ : ℓ ≠ 0)
    (p_r : ℝ) :
    (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ fun r ↦ -κ / r)))
          (ℓ ^ 2 / (m * κ), p_r)).comp
      (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ fun r ↦ -κ / r)))
          (ℓ ^ 2 / (m * κ), p_r)) =
      -(m * κ ^ 2 / |ℓ| ^ 3) ^ 2 • ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  have hm : m ≠ 0 := left_ne_zero_of_mul hmκ.ne'
  have hκ : κ ≠ 0 := right_ne_zero_of_mul hmκ.ne'
  have hr₀ : 0 < ℓ ^ 2 / (m * κ) := div_pos (by positivity) hmκ
  rw [fderiv_hamiltonianVectorField_centralForceHamiltonian_effectivePotential_comp_self hr₀
    (eventually_differentiableAt_kepler_potential hr₀.ne')
    (hasDerivAt_deriv_effectivePotential_kepler_circular hm hκ hℓ) p_r]
  congr 2
  rw [div_pow, ← pow_mul, Even.pow_abs ⟨3, rfl⟩]
  field_simp

/-- **The circular Kepler orbit is elliptic.** Let `m κ > 0` and `ℓ ≠ 0`. The linearization of the
reduced Hamiltonian vector field at `(ℓ² / (m κ), p_r)` has no real eigenvalue: its square is
`-(m κ² / |ℓ|³)²`, so its complex eigenvalues are `± i m κ² / |ℓ|³`. -/
theorem not_hasEigenvalue_fderiv_hamiltonianVectorField_kepler_circular (hmκ : 0 < m * κ)
    (hℓ : ℓ ≠ 0) (p_r μ : ℝ) :
    ¬ Module.End.HasEigenvalue (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ fun r ↦ -κ / r)))
          (ℓ ^ 2 / (m * κ), p_r) : Module.End ℝ (ℝ × ℝ)) μ := by
  have hm : m ≠ 0 := left_ne_zero_of_mul hmκ.ne'
  have hκ : κ ≠ 0 := right_ne_zero_of_mul hmκ.ne'
  have hr₀ : 0 < ℓ ^ 2 / (m * κ) := div_pos (by positivity) hmκ
  refine not_hasEigenvalue_fderiv_hamiltonianVectorField_centralForceHamiltonian_effectivePotential
    hr₀ (eventually_differentiableAt_kepler_potential hr₀.ne')
    (hasDerivAt_deriv_effectivePotential_kepler_circular hm hκ hℓ) ?_ p_r μ
  -- `m³ κ⁴ / ℓ⁶ / m = (m κ²)² / ℓ⁶` is positive since `m κ ≠ 0`.
  have : m ^ 3 * κ ^ 4 / ℓ ^ 6 / m = (m * κ ^ 2) ^ 2 / ℓ ^ 6 := by
    field_simp
  rw [this]
  positivity

/-! ### Comparison with the action–angle frequency -/

/-- **The radial frequency of the circular Kepler orbit.** For `ℓ ≠ 0`, the derivative of the
Kepler energy `H = -m κ² / (2 (I_r + |ℓ|)²)` in the radial action at the circular orbit `I_r = 0`
is `Ω_r = m κ² / |ℓ|³`. -/
theorem deriv_keplerActionHamiltonian_fst_zero (m κ : ℝ) (hℓ : ℓ ≠ 0) :
    deriv (fun r ↦ keplerActionHamiltonian m κ (r, ℓ)) 0 = m * κ ^ 2 / |ℓ| ^ 3 := by
  rw [(hasDerivAt_keplerActionHamiltonian_fst m κ ℓ (by simpa using hℓ)).deriv, zero_add]

/-- **The linearized frequency is the action–angle radial frequency.** Let `m κ > 0` and `ℓ ≠ 0`.
The linearization `A` of the reduced Hamiltonian vector field at the circular orbit satisfies
`A² = -Ω_r²`, where `Ω_r` is the radial frequency `∂H/∂I_r` at `I_r = 0` of the Kepler energy in
action variables. -/
theorem fderiv_hamiltonianVectorField_kepler_circular_comp_self_eq_neg_sq_deriv
    (hmκ : 0 < m * κ) (hℓ : ℓ ≠ 0) (p_r : ℝ) :
    (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ fun r ↦ -κ / r)))
          (ℓ ^ 2 / (m * κ), p_r)).comp
      (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ fun r ↦ -κ / r)))
          (ℓ ^ 2 / (m * κ), p_r)) =
      -(deriv (fun r ↦ keplerActionHamiltonian m κ (r, ℓ)) 0) ^ 2 •
        ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [deriv_keplerActionHamiltonian_fst_zero m κ hℓ,
    fderiv_hamiltonianVectorField_kepler_circular_comp_self hmκ hℓ p_r]

end TauCeti
