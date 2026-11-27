/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Rotations along the complex lines of an almost complex structure

An almost complex structure `J` on a real vector space `V` makes each plane spanned by a nonzero
vector `x` and `J x` a complex line, on which `cos θ • x + sin θ • J x` is the multiple of `x` by
`e^{iθ}`. This file treats the rotations `t ↦ cos (θ t) x + sin (θ t) J x` as the flow of the
linear vector field `θ J`:

* the rotation solves the linear differential equation `γ' = θ J γ`
  (`TauCeti.AlmostComplexStructure.hasDerivAt_cos_smul_add_sin_smul`), and on a
  finite-dimensional space every solution is the rotation of its initial value
  (`TauCeti.AlmostComplexStructure.eq_cos_smul_add_sin_smul_of_hasDerivAt`);
* for `x ≠ 0`, the rotation has period `T` exactly when `θ T` is an integer multiple of `2π`
  (`TauCeti.AlmostComplexStructure.periodic_cos_smul_add_sin_smul_iff`), since `x` and `J x` are
  linearly independent (`TauCeti.AlmostComplexStructure.linearIndependent_pair`).

These rotations are the Hamiltonian flows of the quadratic Hamiltonians `a ‖x‖²` on a symplectic
vector space with a compatible complex structure, and the Reeb flow of its unit sphere.
-/

public section

open Function Real

namespace TauCeti.AlmostComplexStructure

variable {V : Type*}

section Periodic

variable [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)

/-- **Periods of a rotation.** For `x ≠ 0`, the rotation `t ↦ cos (θ t) x + sin (θ t) J x` along
the complex line through `x` has period `T` exactly when `θ T` is an integer multiple of `2 π`:
the vectors `x` and `J x` are linearly independent, so the rotation returns to `x` only when
`cos (θ T) = 1`. -/
theorem periodic_cos_smul_add_sin_smul_iff {x : V} (hx : x ≠ 0) (θ T : ℝ) :
    Periodic (fun t ↦ cos (θ * t) • x + sin (θ * t) • J x) T ↔
      ∃ k : ℤ, θ * T = k * (2 * π) := by
  constructor
  · intro h
    -- At time `0` the period gives `(cos (θ T) - 1) x + sin (θ T) J x = 0`.
    have h0 := h 0
    simp only [zero_add, mul_zero, cos_zero, sin_zero, one_smul, zero_smul, add_zero] at h0
    have hlin : (cos (θ * T) - 1) • x + sin (θ * T) • J x = 0 :=
      calc (cos (θ * T) - 1) • x + sin (θ * T) • J x
          = (cos (θ * T) • x + sin (θ * T) • J x) - x := by module
        _ = 0 := by rw [h0, sub_self]
    have hc := LinearIndependent.pair_iff.1 (J.linearIndependent_pair hx) _ _ hlin
    obtain ⟨k, hk⟩ := (cos_eq_one_iff _).1 (sub_eq_zero.1 hc.1)
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩ t
    simp only [mul_add, hk, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

end Periodic

section Derivative

variable [NormedAddCommGroup V] [NormedSpace ℝ V] (J : AlmostComplexStructure V)

/-- **A rotation solves `γ' = θ J γ`.** The rotation `t ↦ cos (θ t) x + sin (θ t) J x` along the
complex line through `x` is a solution of the linear differential equation `γ' = θ J γ`. -/
theorem hasDerivAt_cos_smul_add_sin_smul (θ : ℝ) (x : V) (t : ℝ) :
    HasDerivAt (fun t ↦ cos (θ * t) • x + sin (θ * t) • J x)
      (θ • J (cos (θ * t) • x + sin (θ * t) • J x)) t := by
  have hθ : HasDerivAt (fun t ↦ θ * t) θ t := by simpa using (hasDerivAt_id t).const_mul θ
  have h := ((hθ.cos).smul_const x).add ((hθ.sin).smul_const (J x))
  convert h using 1
  rw [J.apply_add, J.apply_smul, J.apply_smul, J.apply_apply]
  module

/-- **The solutions of `γ' = θ J γ` are rotations.** On a finite-dimensional space, a curve
solving the linear differential equation `γ' = θ J γ` is the rotation
`t ↦ cos (θ t) γ(0) + sin (θ t) J γ(0)` of its initial value along the complex line through it. -/
theorem eq_cos_smul_add_sin_smul_of_hasDerivAt [FiniteDimensional ℝ V] {θ : ℝ} {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (θ • J (γ t)) t) (t : ℝ) :
    γ t = cos (θ * t) • γ 0 + sin (θ * t) • J (γ 0) := by
  -- Both curves solve the equation of the Lipschitz linear field `θ J`.
  set L : V →L[ℝ] V := θ • LinearMap.toContinuousLinearMap J.toLinearMap
  have hL (y : V) : L y = θ • J y := by simp [L, LinearMap.coe_toContinuousLinearMap']
  have h := ODE_solution_unique_univ (v := fun _ ↦ ⇑L) (s := fun _ ↦ Set.univ) (t₀ := 0)
    (fun _ ↦ L.lipschitzWith.lipschitzOnWith) (fun t ↦ ⟨by simpa only [hL] using hγ t, trivial⟩)
    (fun t ↦ ⟨by simpa only [hL] using J.hasDerivAt_cos_smul_add_sin_smul θ (γ 0) t, trivial⟩)
    (by simp)
  exact congrFun h t

end Derivative

end TauCeti.AlmostComplexStructure
