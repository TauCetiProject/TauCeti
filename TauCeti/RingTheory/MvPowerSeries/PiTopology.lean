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
def continuousLinearEquivPi : MvPowerSeries σ S ≃L[R] ((σ →₀ ℕ) → S) :=
  ContinuousLinearEquiv.refl R ((σ →₀ ℕ) → S)

@[simp, grind =]
theorem continuousLinearEquivPi_apply (f : MvPowerSeries σ S) (d : σ →₀ ℕ) :
    continuousLinearEquivPi σ R S f d = MvPowerSeries.coeff d f :=
  (congr_fun (ContinuousLinearEquiv.refl_apply R ((σ →₀ ℕ) → S) f) d).trans
    (MvPowerSeries.coeff_apply f d).symm

@[simp, grind =]
theorem coeff_continuousLinearEquivPi_symm (c : (σ →₀ ℕ) → S) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((continuousLinearEquivPi σ R S).symm c) = c d := by
  rw [← continuousLinearEquivPi_apply σ R S, ContinuousLinearEquiv.apply_symm_apply]

@[simp, grind =]
theorem constantCoeff_continuousLinearEquivPi_symm (c : (σ →₀ ℕ) → S) :
    MvPowerSeries.constantCoeff ((continuousLinearEquivPi σ R S).symm c) = c 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_continuousLinearEquivPi_symm]

end MvPowerSeries.WithPiTopology
