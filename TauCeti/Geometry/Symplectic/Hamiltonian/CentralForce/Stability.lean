/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Hamiltonian.Stability
public import TauCeti.Analysis.Calculus.DerivativeTest
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Stability of the circular orbits of a central force

A particle of mass `m` with angular momentum `ℓ` in a central potential `U` moves radially
according to the reduced Hamiltonian

`H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`, with `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`,

on the half-plane `r > 0` of `ℝ × ℝ` with its standard symplectic form
(`TauCeti.centralForceHamiltonian m (TauCeti.effectivePotential m ℓ U)`). Its equilibria are the
points `(r₀, 0)` with `r₀` a critical point of the effective potential `U_ℓ`
(`stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_effectivePotential_eq_zero_iff`):
the circular orbits of radius `r₀`. This file classifies them at the extrema of `U_ℓ`.

* **Minima are Lyapunov stable.** For `m > 0`, a strict local minimum `r₀ > 0` of `U_ℓ` makes
  `(r₀, 0)` a strict local minimum of the conserved energy `H_ℓ`
  (`TauCeti.eventually_centralForceHamiltonian_effectivePotential_lt`), so radial motions starting
  near `(r₀, 0)` stay near it at all times at which they are defined
  (`TauCeti.eventually_forall_mem_of_strictLocalMin_effectivePotential`). This holds in particular
  at a nondegenerate minimum, `U_ℓ'(r₀) = 0 < U_ℓ''(r₀)`
  (`TauCeti.eventually_forall_mem_of_deriv_effectivePotential_eq_zero_of_pos`).
* **The linearization.** At every point `(r₀, p_r)` with `r₀ > 0`, the derivative of the reduced
  Hamiltonian vector field `X(r, p_r) = (p_r / m, -U_ℓ'(r))` is
  `A(δr, δp) = (δp / m, -U_ℓ''(r₀) δr)`
  (`TauCeti.hasFDerivAt_hamiltonianVectorField_effectivePotential`),
  and `A² = -(U_ℓ''(r₀) / m)`.
* **Minima are elliptic.** If `U_ℓ''(r₀) / m = ν² > 0`, as at a nondegenerate minimum for
  `m > 0`, then `A² = -ν²` and `A` has no real eigenvalue: its complex eigenvalues are `± i ν`.
* **Maxima are hyperbolic.** If `U_ℓ''(r₀) / m = -κ² < 0`, as at a nondegenerate maximum for
  `m > 0`, then `A` has the real eigenvalues `κ` and `-κ`, with eigenvectors `(1, ± m κ)`.

## Main results

* `TauCeti.eventually_forall_mem_of_strictLocalMin_effectivePotential`: Lyapunov stability of the
  circular orbit at a strict minimum of the effective potential.
* `TauCeti.eventually_forall_mem_of_deriv_effectivePotential_eq_zero_of_pos`: the same at a
  nondegenerate minimum.
* `TauCeti.not_hasEigenvalue_fderiv_hamiltonianVectorField_effectivePotential`: at a
  nondegenerate minimum the linearization has no real eigenvalue.
* `TauCeti.hasEigenvector_fderiv_hamiltonianVectorField_effectivePotential`: at a nondegenerate
  maximum the linearization has the real eigenvalues `± √(-U_ℓ''(r₀) / m)`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 25.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.6 (stability of circular orbits).
-/

public section

namespace TauCeti

open Filter Set Topology

variable {m ℓ : ℝ} {U : ℝ → ℝ}

/-! ### The energy near a minimum of the effective potential -/

/-- **The energy at a minimum of the effective potential.** For a positive mass, if `r₀ > 0` is a
strict local minimum of the effective potential `U_ℓ`, then `(r₀, 0)` is a strict local minimum of
the reduced Hamiltonian `H_ℓ(r, p_r) = p_r² / (2m) + U_ℓ(r)`. -/
theorem eventually_centralForceHamiltonian_effectivePotential_lt (hm : 0 < m) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hmin : ∀ᶠ r in 𝓝[≠] r₀, effectivePotential m ℓ U r₀ < effectivePotential m ℓ U r) :
    ∀ᶠ y in 𝓝[≠] ((r₀, 0) : ℝ × ℝ),
      centralForceHamiltonian m (effectivePotential m ℓ U) (r₀, 0) <
        centralForceHamiltonian m (effectivePotential m ℓ U) y := by
  rw [eventually_nhdsWithin_iff] at hmin ⊢
  have hfst := (continuous_fst.tendsto ((r₀, 0) : ℝ × ℝ)).eventually
    ((eventually_gt_nhds hr₀).and hmin)
  filter_upwards [hfst] with ⟨r, p⟩ ⟨hr, hUr⟩ hne
  simp only [centralForceHamiltonian_effectivePotential_apply hr₀.le,
    centralForceHamiltonian_effectivePotential_apply hr.le, zero_pow two_ne_zero, zero_div,
    zero_add]
  have hp : 0 ≤ p ^ 2 / (2 * m) := by positivity
  rcases eq_or_ne r r₀ with rfl | hrr₀
  · -- On the fibre `r = r₀` the kinetic term `p_r² / (2m)` is positive off `p_r = 0`.
    have hp0 : p ≠ 0 := fun h ↦ hne (by simp [h])
    have : 0 < p ^ 2 / (2 * m) := by positivity
    linarith
  · have := hUr hrr₀
    simp only [effectivePotential_apply] at this
    linarith

/-! ### Lyapunov stability of the circular orbits at minima -/

/-- **Circular orbits at a minimum of the effective potential are stable.** Let `m > 0`, and let
`r₀ > 0` be a strict local minimum of the effective potential `U_ℓ`, with `U` continuous near `r₀`.
For every neighbourhood `W` of the equilibrium `(r₀, 0)` of the reduced system, every radial
motion `γ` passing close enough to `(r₀, 0)` stays in `W` at all times of its open preconnected
time interval `T`. The radial motions are the integral curves in the half-plane `r > 0` of the
reduced Hamiltonian vector field, along which `U` is differentiable. -/
theorem eventually_forall_mem_of_strictLocalMin_effectivePotential (hm : 0 < m) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hU : ∀ᶠ r in 𝓝 r₀, ContinuousAt U r)
    (hmin : ∀ᶠ r in 𝓝[≠] r₀, effectivePotential m ℓ U r₀ < effectivePotential m ℓ U r)
    {W : Set (ℝ × ℝ)} (hW : W ∈ 𝓝 ((r₀, 0) : ℝ × ℝ)) :
    ∀ᶠ y in 𝓝 ((r₀, 0) : ℝ × ℝ), ∀ (γ : ℝ → ℝ × ℝ) (T : Set ℝ), IsOpen T → IsPreconnected T →
      (∀ t ∈ T, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t) →
      (∀ t ∈ T, 0 < (γ t).1) → (∀ t ∈ T, DifferentiableAt ℝ U (γ t).1) →
      ∀ t₀ ∈ T, γ t₀ = y → ∀ t ∈ T, γ t ∈ W := by
  -- The reduced Hamiltonian is continuous near `(r₀, 0)`.
  have hcont : ∀ᶠ y in 𝓝 ((r₀, 0) : ℝ × ℝ),
      ContinuousAt (centralForceHamiltonian m (effectivePotential m ℓ U)) y := by
    have hfst := (continuous_fst.tendsto ((r₀, 0) : ℝ × ℝ)).eventually
      ((eventually_gt_nhds hr₀).and hU)
    filter_upwards [hfst] with y ⟨hy, hUy⟩
    have hUℓ : effectivePotential m ℓ U = fun r ↦ ℓ ^ 2 / (2 * m * r ^ 2) + U r :=
      funext (effectivePotential_apply m ℓ U)
    have hV : ContinuousAt (effectivePotential m ℓ U) ‖y.1‖ := by
      rw [Real.norm_of_nonneg hy.le, hUℓ]
      exact (continuousAt_const.div (by fun_prop) (by positivity)).add hUy
    have hH : centralForceHamiltonian m (effectivePotential m ℓ U) =
        fun y : ℝ × ℝ ↦ ‖y.2‖ ^ 2 / (2 * m) + effectivePotential m ℓ U ‖y.1‖ :=
      funext fun y ↦ centralForceHamiltonian_apply m _ y.1 y.2
    rw [hH]
    exact ((continuous_snd.norm.pow 2).continuousAt.div_const _).add
      (hV.comp (f := fun x : ℝ × ℝ ↦ ‖x.1‖) continuous_fst.norm.continuousAt)
  filter_upwards [(stdSymplecticForm (V := ℝ)).eventually_forall_mem_of_strictLocalMin hcont
    (fun y (hy : ContinuousAt _ y) ↦ hy.continuousWithinAt)
    (eventually_centralForceHamiltonian_effectivePotential_lt hm hr₀ hmin) hW]
    with y hy γ T hT hT' hγ hpos hUγ
  -- The energy is differentiable along the motion, which avoids `r = 0`.
  exact hy γ T hT hT' hγ fun t ht ↦
    differentiableAt_centralForceHamiltonian_effectivePotential (hpos t ht) (hUγ t ht) (γ t).2

/-- **Circular orbits at a nondegenerate minimum of the effective potential are stable.** Let
`m > 0`, `r₀ > 0`, and let `U` be differentiable near `r₀`, with `U_ℓ'(r₀) = 0` and
`U_ℓ''(r₀) = a > 0`. For every neighbourhood `W` of the equilibrium `(r₀, 0)` of the reduced
system, every radial motion passing close enough to `(r₀, 0)` stays in `W` at all times. -/
theorem eventually_forall_mem_of_deriv_effectivePotential_eq_zero_of_pos (hm : 0 < m) {r₀ a : ℝ}
    (hr₀ : 0 < r₀) (hU : ∀ᶠ r in 𝓝 r₀, DifferentiableAt ℝ U r)
    (hd : deriv (effectivePotential m ℓ U) r₀ = 0)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (ha₀ : 0 < a)
    {W : Set (ℝ × ℝ)} (hW : W ∈ 𝓝 ((r₀, 0) : ℝ × ℝ)) :
    ∀ᶠ y in 𝓝 ((r₀, 0) : ℝ × ℝ), ∀ (γ : ℝ → ℝ × ℝ) (T : Set ℝ), IsOpen T → IsPreconnected T →
      (∀ t ∈ T, HasDerivAt γ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)) (γ t)) t) →
      (∀ t ∈ T, 0 < (γ t).1) → (∀ t ∈ T, DifferentiableAt ℝ U (γ t).1) →
      ∀ t₀ ∈ T, γ t₀ = y → ∀ t ∈ T, γ t ∈ W := by
  have hV : ContinuousAt (effectivePotential m ℓ U) r₀ :=
    (hasDerivAt_effectivePotential hU.self_of_nhds.hasDerivAt hr₀.ne').continuousAt
  exact eventually_forall_mem_of_strictLocalMin_effectivePotential hm hr₀
    (hU.mono fun r hr ↦ hr.continuousAt)
    (eventually_lt_of_deriv_deriv_pos (by rwa [ha.deriv]) hd hV) hW

/-! ### The linearization at the circular orbits -/

/-- **The linearized radial equations.** Let `r₀ > 0`, with `U` differentiable near `r₀` and
`U_ℓ'` differentiable at `r₀` with derivative `a = U_ℓ''(r₀)`. At every point `(r₀, p_r)`, the
reduced Hamiltonian vector field `X(r, p_r) = (p_r / m, -U_ℓ'(r))` has derivative
`(δr, δp) ↦ (δp / m, -a δr)`. -/
theorem hasFDerivAt_hamiltonianVectorField_effectivePotential
    {r₀ a : ℝ} (hr₀ : 0 < r₀) (hU : ∀ᶠ r in 𝓝 r₀, DifferentiableAt ℝ U r)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (p_r : ℝ) :
    HasFDerivAt ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U)))
      ((m⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-(a • ContinuousLinearMap.fst ℝ ℝ ℝ)))
      (r₀, p_r) := by
  have hV : HasFDerivAt (fun y : ℝ × ℝ ↦ deriv (effectivePotential m ℓ U) y.1)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ) (r₀, p_r) :=
    ha.comp_hasFDerivAt (f := Prod.fst) (r₀, p_r) hasFDerivAt_fst
  have hX := ((hasFDerivAt_snd (p := ((r₀, p_r) : ℝ × ℝ))).const_mul m⁻¹).prodMk hV.neg
  refine hX.congr_of_eventuallyEq ?_
  -- Near `(r₀, p_r)`, Hamilton's equations read `r' = p_r / m`, `p_r' = -U_ℓ'(r)`.
  filter_upwards [(continuous_fst.tendsto ((r₀, p_r) : ℝ × ℝ)).eventually
    ((eventually_gt_nhds hr₀).and hU)] with ⟨r, p⟩ ⟨hr, hUr⟩
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian_effectivePotential
    hUr.hasDerivAt hr]
  simp only [Pi.neg_apply]
  rw [(hasDerivAt_effectivePotential hUr.hasDerivAt hr.ne').deriv]
  ext
  · simp [div_eq_inv_mul]
  · simp

/-- At a point `(r₀, p_r)` with `r₀ > 0`, the derivative `A` of the reduced Hamiltonian vector
field satisfies `A² = -(U_ℓ''(r₀) / m)`. -/
theorem fderiv_hamiltonianVectorField_effectivePotential_comp_self
    {r₀ a : ℝ} (hr₀ : 0 < r₀) (hU : ∀ᶠ r in 𝓝 r₀, DifferentiableAt ℝ U r)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (p_r : ℝ) :
    (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U))) (r₀, p_r)).comp
      (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U))) (r₀, p_r)) =
      -(a / m) • ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [(hasFDerivAt_hamiltonianVectorField_effectivePotential
    hr₀ hU ha p_r).fderiv]
  ext <;> simp <;> ring

/-- **Circular orbits at a nondegenerate minimum are elliptic.** If `U_ℓ''(r₀) / m > 0`, the
linearization of the reduced Hamiltonian vector field at `(r₀, p_r)` has no real eigenvalue. Its
square is `-(U_ℓ''(r₀) / m)`, so its complex eigenvalues are `± i √(U_ℓ''(r₀) / m)`. When `r₀` is
a critical point of `U_ℓ`, `(r₀, 0)` is an equilibrium of the reduced system, and this says that
it is an elliptic equilibrium. -/
theorem not_hasEigenvalue_fderiv_hamiltonianVectorField_effectivePotential
    {r₀ a : ℝ} (hr₀ : 0 < r₀) (hU : ∀ᶠ r in 𝓝 r₀, DifferentiableAt ℝ U r)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (ham : 0 < a / m) (p_r μ : ℝ) :
    ¬ Module.End.HasEigenvalue (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U))) (r₀, p_r) :
          Module.End ℝ (ℝ × ℝ)) μ := by
  intro hμ
  obtain ⟨⟨x, y⟩, hv⟩ := hμ.exists_hasEigenvector
  have hm : m ≠ 0 := by rintro rfl; simp at ham
  have h := hv.apply_eq_smul
  rw [ContinuousLinearMap.coe_coe,
    (hasFDerivAt_hamiltonianVectorField_effectivePotential
      hr₀ hU ha p_r).fderiv] at h
  simp only [ContinuousLinearMap.prod_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', smul_eq_mul, neg_apply,
    Prod.smul_mk, Prod.mk.injEq] at h
  -- The components give `x (a / m + μ²) = 0`, and `a / m + μ² > 0`.
  have hx : x * (a / m + μ ^ 2) = 0 := by
    linear_combination (-μ) * h.1 + (-1 / m) * h.2
  have hx0 : x = 0 := by
    rcases mul_eq_zero.1 hx with hx | hx
    · exact hx
    · nlinarith [sq_nonneg μ]
  have hy0 : y = 0 := by
    have := h.1
    rw [hx0, mul_zero, mul_eq_zero] at this
    exact this.resolve_left (inv_ne_zero hm)
  exact hv.2 (by simp [hx0, hy0])

/-- **Circular orbits at a nondegenerate maximum are hyperbolic.** If `U_ℓ''(r₀) / m < 0`, the
linearization of the reduced Hamiltonian vector field at `(r₀, p_r)` has the real eigenvalue
`κ = √(-U_ℓ''(r₀) / m)`, with eigenvector `(1, m κ)`, and the real eigenvalue `-κ`, with
eigenvector `(1, -m κ)`. When `r₀` is a critical point of `U_ℓ`, `(r₀, 0)` is an equilibrium of the
reduced system, and this says that it is a hyperbolic equilibrium. -/
theorem hasEigenvector_fderiv_hamiltonianVectorField_effectivePotential
    {r₀ a : ℝ} (hr₀ : 0 < r₀) (hU : ∀ᶠ r in 𝓝 r₀, DifferentiableAt ℝ U r)
    (ha : HasDerivAt (deriv (effectivePotential m ℓ U)) a r₀) (ham : a / m < 0) (p_r : ℝ)
    {κ : ℝ} (hκ : κ = √(-(a / m)) ∨ κ = -√(-(a / m))) :
    Module.End.HasEigenvector (fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
        (centralForceHamiltonian m (effectivePotential m ℓ U))) (r₀, p_r) :
          Module.End ℝ (ℝ × ℝ)) κ (1, m * κ) := by
  have hm : m ≠ 0 := by rintro rfl; simp at ham
  have hκ2 : κ ^ 2 = -(a / m) := by
    rcases hκ with rfl | rfl <;> simp [Real.sq_sqrt (neg_nonneg.2 ham.le)]
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
    (hasFDerivAt_hamiltonianVectorField_effectivePotential
      hr₀ hU ha p_r).fderiv]
  refine ⟨?_, by simp⟩
  ext
  · simp [hm]
  · simp only [ContinuousLinearMap.prod_apply, neg_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one, Prod.smul_mk]
    field_simp at hκ2
    linear_combination -hκ2

end TauCeti
