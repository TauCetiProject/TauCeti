/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import TauCeti.MeasureTheory.Group.Convolution.Support

/-!
# Norm estimates for convolution-type integrals over a group

If a compactly supported continuous function `F : C_c(G, E₃)` on a topological group `G` is
dominated pointwise in norm by the scalar convolution `s ↦ ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ` of
compactly supported continuous functions `f : C_c(G, E₁)` and `g : C_c(G, E₂)` against a
left-invariant measure `μ` finite on compact sets, then

`∫ s, ‖F s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ`.

Neither local compactness, separability, nor σ-finiteness of `μ` is assumed: integrability and the
iterated-integral identity come from `TauCeti.integrable_integral_norm_mul_inv_mul` and
`TauCeti.integral_integral_norm_mul_inv_mul`.

## Main statements

* `TauCeti.integral_norm_le_mul_of_norm_le_integral`: pointwise domination of `‖F s‖` by the scalar
  convolution `∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ` implies `∫ ‖F‖ ≤ (∫ ‖f‖) * ∫ ‖g‖`.
-/

public section

open MeasureTheory Function
open scoped CompactlySupported

namespace TauCeti

/-- If `F : C_c(G, E₃)` is bounded in norm pointwise by the scalar convolution
`s ↦ ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ` of `f : C_c(G, E₁)` and `g : C_c(G, E₂)` against a
left-invariant measure `μ` finite on compacts, then
`∫ s, ‖F s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ`. -/
theorem integral_norm_le_mul_of_norm_le_integral {G E₁ E₂ E₃ : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [MeasurableMul G]
    [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (F : C_c(G, E₃)) (f : C_c(G, E₁)) (g : C_c(G, E₂))
    (hF : ∀ s, ‖F s‖ ≤ ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ) :
    ∫ s, ‖F s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ :=
  calc ∫ s, ‖F s‖ ∂μ
      ≤ ∫ s, ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ :=
        integral_mono
          (F.continuous.norm.integrable_of_hasCompactSupport
            (F.hasCompactSupport.comp_left norm_zero))
          (integrable_integral_norm_mul_inv_mul μ μ f.continuous f.hasCompactSupport
            g.continuous g.hasCompactSupport)
          hF
    _ = (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ :=
        integral_integral_norm_mul_inv_mul μ μ f.continuous f.hasCompactSupport
          g.continuous g.hasCompactSupport

end TauCeti
