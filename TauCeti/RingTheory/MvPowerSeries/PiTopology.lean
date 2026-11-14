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

With `MvPowerSeries.WithPiTopology`, the coefficient map identifies `MvPowerSeries σ R` with the
product module `(σ →₀ ℕ) → R` as a topological `R`-module (`continuousLinearEquivPi`).
-/

public section

namespace MvPowerSeries.WithPiTopology

open scoped MvPowerSeries.WithPiTopology

variable (σ R : Type*) [Semiring R] [TopologicalSpace R]

/-- With the product topology on coefficients, `MvPowerSeries σ R` is continuously `R`-linearly
isomorphic to `(σ →₀ ℕ) → R` via `MvPowerSeries.coeff`. -/
def continuousLinearEquivPi : MvPowerSeries σ R ≃L[R] ((σ →₀ ℕ) → R) where
  toFun f d := MvPowerSeries.coeff d f
  map_add' f g := by ext d; simp
  map_smul' r f := by ext d; simp
  invFun c := c
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (continuous_coeff R)
  continuous_invFun := continuous_iff_continuousAt.mpr fun _ ↦
    (tendsto_iff_coeff_tendsto _ _ _).mpr fun d ↦ (continuous_apply d).continuousAt

@[simp]
theorem continuousLinearEquivPi_apply (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    continuousLinearEquivPi σ R f d = MvPowerSeries.coeff d f :=
  (rfl)

@[simp]
theorem continuousLinearEquivPi_symm_coeff (c : (σ →₀ ℕ) → R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((continuousLinearEquivPi σ R).symm c) = c d :=
  (rfl)

end MvPowerSeries.WithPiTopology
