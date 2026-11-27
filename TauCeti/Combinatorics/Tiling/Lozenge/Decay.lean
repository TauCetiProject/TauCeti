/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.CharacteristicFunction
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Defs.Filter
import TauCeti.Analysis.Fourier.RiemannLebesgue

/-!
# Decay of the lozenge kernel

For type weights `w = (w₁, w₂, w₃)`, the kernel
`G_w(d) = (4π²)⁻¹ ∫∫_{[0,2π]²} e^{i(d₁θ + d₂φ)} / P_w(θ, φ) dθ dφ` (`TauCeti.lozengeKernel`)
tends to `0` as `d → ∞` in `ℤ²`, that is, along the cofinite filter
(`TauCeti.tendsto_lozengeKernel_cofinite`). This is the Riemann--Lebesgue lemma
(`TauCeti.tendsto_integral_exp_sum_int_mul_I_smul_cofinite`) at `ι = Fin 2`, applied to the
function `1_{[0,2π]²} / P_w` on `ℝ²`, which is integrable for liquid weights
(`TauCeti.IsLiquidWeights.integrableOn_inv_lozengeCharFun`). No hypothesis on `w` is needed: when
`1 / P_w` is not integrable on the torus, every `G_w(d)` is `0`.
-/

public section

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology

namespace TauCeti

/-- **Decay of the lozenge kernel.** `G_w(d) → 0` as `d → ∞` in `ℤ²`. -/
theorem tendsto_lozengeKernel_cofinite (w₁ w₂ w₃ : ℝ) :
    Tendsto (lozengeKernel w₁ w₂ w₃) cofinite (𝓝 0) := by
  set T := Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)
  set g : ℝ × ℝ → ℂ := T.indicator fun p => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹
  have h := ((tendsto_integral_exp_sum_int_mul_I_smul_cofinite
    (g ∘ MeasurableEquiv.finTwoArrow)).comp
      (finTwoArrowEquiv ℤ).symm.injective.tendsto_cofinite).const_smul ((4 * Real.pi ^ 2)⁻¹ : ℝ)
  rw [smul_zero] at h
  refine h.congr fun d => ?_
  rw [lozengeKernel_def, ← integral_indicator (measurableSet_Ioc.prod measurableSet_Ioc),
    Function.comp_apply, ← (volume_preserving_finTwoArrow ℝ).integral_comp']
  congr 1
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [Function.comp_apply, Fin.sum_univ_two, g, indicator_apply, smul_eq_mul,
    div_eq_mul_inv]
  split_ifs <;> simp

end TauCeti
