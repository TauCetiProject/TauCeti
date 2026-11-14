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

Mathlib's `MvPowerSeries.WithPiTopology` equips `MvPowerSeries σ S` with the topology of pointwise
convergence of coefficients inherited from `(σ →₀ ℕ) → S` (activated via
`open scoped MvPowerSeries.WithPiTopology`), without bundling the topological linear isomorphism
with the coordinate product. For any scalar semiring `R` acting linearly on `S`, this file bundles
`MvPowerSeries.coeff` as `MvPowerSeries.WithPiTopology.continuousLinearEquivPi :
MvPowerSeries σ S ≃L[R] ((σ →₀ ℕ) → S)` so that product-module properties such as
`TauCeti.IsCompactModule` and `TauCeti.IsProfiniteFlat` transfer directly from `(σ →₀ ℕ) → S` to
`MvPowerSeries σ S`.
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
  map_smul' r f := by
    ext d
    simp only [MvPowerSeries.coeff_apply, Pi.smul_apply]
    -- `Module R (MvPowerSeries σ S)` is inherited from `Module R ((σ →₀ ℕ) → S)`.
    rfl
  -- Unlike `PowerSeries.mk`, `MvPowerSeries σ S` is `(σ →₀ ℕ) → S` with no `mk` constructor.
  invFun c := c
  left_inv f := MvPowerSeries.ext fun d ↦ MvPowerSeries.coeff_apply f d
  right_inv c := funext fun d ↦ MvPowerSeries.coeff_apply c d
  continuous_toFun := continuous_pi (continuous_coeff S)
  continuous_invFun := continuous_iff_continuousAt.mpr fun _ ↦
    (tendsto_iff_coeff_tendsto _ _ _).mpr fun d ↦ (continuous_apply d).continuousAt

@[simp]
theorem continuousLinearEquivPi_apply (f : MvPowerSeries σ S) (d : σ →₀ ℕ) :
    continuousLinearEquivPi σ R S f d = MvPowerSeries.coeff d f :=
  (rfl)

@[simp]
theorem coeff_continuousLinearEquivPi_symm (c : (σ →₀ ℕ) → S) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((continuousLinearEquivPi σ R S).symm c) = c d :=
  MvPowerSeries.coeff_apply c d

@[simp]
theorem constantCoeff_continuousLinearEquivPi_symm (c : (σ →₀ ℕ) → S) :
    MvPowerSeries.constantCoeff ((continuousLinearEquivPi σ R S).symm c) = c 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_continuousLinearEquivPi_symm]

end MvPowerSeries.WithPiTopology
