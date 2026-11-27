/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Coefficientwise continuous linear isomorphism for multivariate power series

Bundles `MvPowerSeries.coeff` as `MvPowerSeries.WithPiTopology.continuousLinearEquivPi :
MvPowerSeries σ S ≃L[R] ((σ →₀ ℕ) → S)` under `open scoped MvPowerSeries.WithPiTopology`.
-/

public section

namespace MvPowerSeries.WithPiTopology

open scoped MvPowerSeries.WithPiTopology

variable (σ R S : Type*) [Semiring R] [Semiring S] [Module R S] [TopologicalSpace S]

/-- With the product topology on coefficients (`open scoped MvPowerSeries.WithPiTopology`),
`MvPowerSeries σ S` is continuously `R`-linearly isomorphic to `(σ →₀ ℕ) → S` via
`MvPowerSeries.coeff`. -/
def continuousLinearEquivPi : MvPowerSeries σ S ≃L[R] ((σ →₀ ℕ) → S) where
  toFun f d := MvPowerSeries.coeff d f
  map_add' f g := by ext d; simp
  -- `MvPowerSeries σ S` is definitionally `(σ →₀ ℕ) → S` with pointwise scalar multiplication,
  -- so `map_smul'` holds by `rfl`, `invFun` is the identity map, and `(c : MvPowerSeries σ S)`
  -- converts a coefficient function to a power series in `right_inv` and `continuous_invFun`.
  map_smul' r f := by ext d; rfl
  invFun c := c
  left_inv f := MvPowerSeries.ext fun d ↦ MvPowerSeries.coeff_apply f d
  right_inv c := funext fun d ↦ MvPowerSeries.coeff_apply c d
  continuous_toFun := continuous_pi (continuous_coeff S)
  continuous_invFun := continuous_iff_continuousAt.mpr fun x ↦
    (tendsto_iff_coeff_tendsto _ _ _).mpr fun d ↦ by
      rw [MvPowerSeries.coeff_apply (x : MvPowerSeries σ S) d]
      exact (continuous_apply d).continuousAt.tendsto.congr
        fun c ↦ (MvPowerSeries.coeff_apply (c : MvPowerSeries σ S) d).symm

@[simp, grind =]
theorem continuousLinearEquivPi_apply (f : MvPowerSeries σ S) (d : σ →₀ ℕ) :
    continuousLinearEquivPi σ R S f d = MvPowerSeries.coeff d f :=
  (rfl)

@[simp, grind =]
theorem coeff_continuousLinearEquivPi_symm (c : (σ →₀ ℕ) → S) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((continuousLinearEquivPi σ R S).symm c) = c d := by
  rw [← continuousLinearEquivPi_apply σ R S, ContinuousLinearEquiv.apply_symm_apply]

@[simp, grind =]
theorem constantCoeff_continuousLinearEquivPi_symm (c : (σ →₀ ℕ) → S) :
    MvPowerSeries.constantCoeff ((continuousLinearEquivPi σ R S).symm c) = c 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_continuousLinearEquivPi_symm]

end MvPowerSeries.WithPiTopology
