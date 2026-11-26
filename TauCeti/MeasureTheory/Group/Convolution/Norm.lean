/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Norm estimates for convolution-type integrals over a group

If a compactly supported continuous function `F : C_c(G, E₃)` on a topological group `G` is
dominated pointwise in norm by the scalar convolution `s ↦ ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ` of
compactly supported continuous functions `f : C_c(G, E₁)` and `g : C_c(G, E₂)` against a
left-invariant measure `μ` finite on compact sets, then

`∫ s, ‖F s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ`.

Neither local compactness, separability, nor σ-finiteness of `μ` is assumed: continuity of the
scalar convolution comes from `TauCeti.continuous_integral_of_compact_support`, its compact support
from `TauCeti.hasCompactSupport_integral_of_inv_mul_mem`, and the Fubini swap from
`MeasureTheory.integral_integral_swap_of_hasCompactSupport`.

## Main statements

* `TauCeti.integral_integral_mul_inv_mul`: for continuous compactly supported scalar functions,
  `∫ s, ∫ r, u r * v (r⁻¹ * s) ∂μ ∂μ = (∫ u) * ∫ v`.
* `TauCeti.integral_norm_le_mul_of_norm_le_integral`: pointwise domination of `‖F s‖` by the scalar
  convolution `∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ` implies `∫ ‖F‖ ≤ (∫ ‖f‖) * ∫ ‖g‖`.
-/

public section

open MeasureTheory Function
open scoped CompactlySupported

namespace TauCeti

/-- For continuous compactly supported `u v : G → 𝕜` and a left-invariant measure `μ` finite on
compacts, `∫ s, ∫ r, u r * v (r⁻¹ * s) ∂μ ∂μ = (∫ s, u s ∂μ) * ∫ s, v s ∂μ`. -/
theorem integral_integral_mul_inv_mul {G 𝕜 : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    [RCLike 𝕜] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    {u v : G → 𝕜} (hu : Continuous u) (hv : Continuous v) (hu' : HasCompactSupport u)
    (hv' : HasCompactSupport v) :
    ∫ s, ∫ r, u r * v (r⁻¹ * s) ∂μ ∂μ = (∫ s, u s ∂μ) * ∫ s, v s ∂μ := by
  have hsupp : ∀ s r, u r * v (r⁻¹ * s) ≠ 0 → r ∈ tsupport u ∧ r⁻¹ * s ∈ tsupport v :=
    fun _ _ h => mem_tsupport_and_inv_mul_mem_tsupport h (by intro hf; simp [hf])
      (by intro hg; simp [hg])
  have hcont : Continuous (uncurry fun s r => u r * v (r⁻¹ * s)) := by
    rw [uncurry_def]
    fun_prop
  calc ∫ s, ∫ r, u r * v (r⁻¹ * s) ∂μ ∂μ
      = ∫ r, ∫ s, u r * v (r⁻¹ * s) ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hcont
          (hasCompactSupport_uncurry_of_inv_mul_mem hu' hv' hsupp)
    _ = ∫ r, u r * ∫ s, v s ∂μ ∂μ := by
        congr 1 with r
        rw [integral_const_mul, integral_mul_left_eq_self v r⁻¹]
    _ = (∫ s, u s ∂μ) * ∫ s, v s ∂μ := integral_mul_const _ _

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
    ∫ s, ‖F s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
  have hsupp : ∀ s r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ≠ 0 → r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
    fun _ _ h => mem_tsupport_and_inv_mul_mem_tsupport h (by intro hf; simp [hf])
      (by intro hg; simp [hg])
  have hcont : Continuous (uncurry fun s r => ‖f r‖ * ‖g (r⁻¹ * s)‖) := by
    rw [uncurry_def]
    fun_prop
  have hNcont := continuous_integral_of_compact_support μ f.hasCompactSupport hcont
    fun s r h => (hsupp s r h).1
  have hNsupp := hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport
    g.hasCompactSupport hsupp
  calc ∫ s, ‖F s‖ ∂μ
      ≤ ∫ s, ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ :=
        integral_mono
          (F.continuous.norm.integrable_of_hasCompactSupport
            (F.hasCompactSupport.comp_left norm_zero))
          (hNcont.integrable_of_hasCompactSupport hNsupp) hF
    _ = (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ :=
        integral_integral_mul_inv_mul μ f.continuous.norm g.continuous.norm
          (f.hasCompactSupport.comp_left norm_zero) (g.hasCompactSupport.comp_left norm_zero)

end TauCeti
