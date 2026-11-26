/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Basic
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

`V_ℓ''(r₀) = m³ κ⁴ / ℓ⁶`

(`TauCeti.hasDerivAt_deriv_effectivePotential_kepler_circular`). These derivatives are computed in
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Basic`. For `m > 0` the value
`V_ℓ''(r₀)` is positive, so `r₀` is a nondegenerate minimum of `V_ℓ`, and the general theory of
circular orbits of central forces in
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
(`TauCeti.deriv_keplerActionHamiltonian_fst_zero`, in
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Kepler.Frequency`). Hence `A² = -Ω_r²`
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

/-! ### Stability of the circular orbit -/

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
    (eventually_differentiableAt_kepler_potential κ hr₀.ne')
    ((deriv_effectivePotential_kepler_eq_zero_iff hκ.ne' hr₀.ne').2 rfl)
    (hasDerivAt_deriv_effectivePotential_kepler_circular hm.ne' hκ.ne' hℓ) (by positivity) hW]
    with y hy γ T hT hT' hγ hpos
  exact hy γ T hT hT' hγ hpos fun t ht ↦ differentiableAt_kepler_potential κ (hpos t ht).ne'

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
    (eventually_differentiableAt_kepler_potential κ hr₀.ne')
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
    hr₀ (eventually_differentiableAt_kepler_potential κ hr₀.ne')
    (hasDerivAt_deriv_effectivePotential_kepler_circular hm hκ hℓ) ?_ p_r μ
  -- `m³ κ⁴ / ℓ⁶ / m = (m κ²)² / ℓ⁶` is positive since `m κ ≠ 0`.
  have : m ^ 3 * κ ^ 4 / ℓ ^ 6 / m = (m * κ ^ 2) ^ 2 / ℓ ^ 6 := by
    field_simp
  rw [this]
  positivity

/-! ### Comparison with the action–angle frequency -/

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
