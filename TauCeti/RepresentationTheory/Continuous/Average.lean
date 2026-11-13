/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.RepresentationTheory.Continuous.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Equivariance of averages along a continuous representation

Left invariance of a measure makes averaging along a representation equivariant: for a
continuous representation `σ` of a group `G` on a real normed space `F` and any map `c` from a
`G`-space to `F`, the average `y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ` intertwines the action with `σ`
whenever `μ` is left-invariant. Neither compactness of `G` nor integrability of the integrand is
needed. With normalized Haar measure on a compact group this is the Bochner average that
linearizes a compact group action at a fixed point.

## Main results

* `ContRepresentation.integral_apply_inv_smul_smul`: equivariance of the integral average
  `y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ`.
-/

public section

open MeasureTheory

namespace ContRepresentation

/-- **Equivariance of the integral Bochner average.** For a left-invariant measure `μ` on `G`, a
continuous representation `σ` and any map `c : X → F` from a `G`-space, the average
`y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ` intertwines the action on `X` with `σ`. -/
theorem integral_apply_inv_smul_smul {G X F : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [MulAction G X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (σ : ContRepresentation ℝ G F) (c : X → F) (h : G)
    (y : X) : ∫ g, σ g (c (g⁻¹ • h • y)) ∂μ = σ h (∫ g, σ g (c (g⁻¹ • y)) ∂μ) := by
  let L : F ≃L[ℝ] F := ContinuousLinearEquiv.equivOfInverse' (σ h) (σ h⁻¹) (comp_inv_self σ h)
    (by simpa using comp_inv_self σ h⁻¹)
  calc ∫ g, σ g (c (g⁻¹ • h • y)) ∂μ = ∫ g, σ (h * g) (c ((h * g)⁻¹ • h • y)) ∂μ :=
        (integral_mul_left_eq_self (fun g ↦ σ g (c (g⁻¹ • h • y))) h).symm
    _ = ∫ g, L (σ g (c (g⁻¹ • y))) ∂μ := by
        congr 1
        ext g
        simp [L, mul_inv_rev, mul_smul, map_mul]
    _ = σ h (∫ g, σ g (c (g⁻¹ • y)) ∂μ) := L.integral_comp_comm _

end ContRepresentation
