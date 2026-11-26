/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Dilation
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Dilation scaling of the Poincaré constants

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, let
`c ≠ 0`, and let `U, V ⊆ E` be open with `V = c U`, that is `U = (c • ·)⁻¹(V)`. This file proves
that the constants of the first-order Poincaré inequalities scale linearly with the size of the
domain: an inequality holds on `U` with constant `C` exactly when it holds on `V` with constant
`|c| C`. Since this is an equivalence for every `C`, the optimal constant on `V` is `|c|` times the
optimal constant on `U`.

* **Poincaré–Friedrichs.** For a set `Γ` and `1 ≤ p < ∞`, the inequality
  `‖u‖_{Lᵖ} ≤ C ‖∇u‖_{Lᵖ}` holds on the space `W^{1,p}_{(c • ·)⁻¹(Γ)}(U)` of Sobolev functions
  vanishing on `(c • ·)⁻¹(Γ)` exactly when `‖u‖_{Lᵖ} ≤ |c| C ‖∇u‖_{Lᵖ}` holds on `W^{1,p}_Γ(V)`
  (`TauCeti.W1p.forall_norm_value_le_mul_norm_gradient_iff_of_preimage_smul`). At `Γ` the frontier
  this is the zero-boundary Poincaré inequality on `W^{1,p}_0`
  (`TauCeti.w1pVanishingOnSubmodule_frontier`).
* **Poincaré–Wirtinger.** For `S ⊆ V`, the inequality `‖u - ⨍_{(c • ·)⁻¹(S)} u‖_{Lᵖ} ≤ C ‖∇u‖_{Lᵖ}`
  holds on `W^{1,p}(U)` exactly when `‖u - ⨍_S u‖_{Lᵖ} ≤ |c| C ‖∇u‖_{Lᵖ}` holds on `W^{1,p}(V)`
  (`TauCeti.W1p.forall_eLpNorm_value_sub_setAverage_le_iff_of_preimage_smul`).

Both follow from the exact scaling of the two halves of the Sobolev norm under the dilation
`u ↦ u (c • ·)` (`TauCeti.W1p.norm_value_compSMulL`, `TauCeti.W1p.norm_gradient_compSMulL`): the
`Lᵖ` norm of the function is multiplied by `|c| ^ (-n / p)` and that of its gradient by
`|c| ^ (1 - n / p)`, so their ratio by `|c|⁻¹`. Means over a set are unchanged by the dilation, and
so is vanishing on a boundary part, which is dilated along.

## Main declarations

* `TauCeti.W1p.forall_norm_value_le_mul_norm_gradient_iff_of_preimage_smul`: the
  Poincaré–Friedrichs constant scales linearly under dilation.
* `TauCeti.W1p.forall_eLpNorm_value_sub_setAverage_le_iff_of_preimage_smul`: the
  Poincaré–Wirtinger constant scales linearly under dilation.
-/

public section

noncomputable section

open Function MeasureTheory Module Set TopologicalSpace
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ}

/-- **The Poincaré–Friedrichs constant scales linearly under dilation.** Let `c ≠ 0`, `1 ≤ p < ∞`
and `U = (c • ·)⁻¹(V)`, so that `V` is the dilate of `U` by `c`, and let `Γ` be a set. The
inequality `‖u‖_{Lᵖ(U)} ≤ C ‖∇u‖_{Lᵖ(U)}` holds for every `u ∈ W^{1,p}_{(c • ·)⁻¹(Γ)}(U)` exactly
when `‖u‖_{Lᵖ(V)} ≤ |c| C ‖∇u‖_{Lᵖ(V)}` holds for every `u ∈ W^{1,p}_Γ(V)`. -/
theorem W1p.forall_norm_value_le_mul_norm_gradient_iff_of_preimage_smul (hp : p ≠ ⊤)
    (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V) (Γ : Set E) (C : ℝ) :
    (∀ u ∈ w1pVanishingOnSubmodule mu U p ((c • ·) ⁻¹' Γ),
        ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖) ↔
      ∀ u ∈ w1pVanishingOnSubmodule mu V p Γ, ‖W1p.value u‖ ≤ |c| * C * ‖W1p.gradient u‖ := by
  have hk {c : ℝ} (hc : c ≠ 0) : 0 < (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ := by positivity
  constructor
  · -- Test the inequality on `U` with the dilate `u (c • ·)`.
    intro h u hu
    have h' := h _ ((W1p.compSMulL_mem_w1pVanishingOnSubmodule_iff hp hc hUV).2 hu)
    rw [W1p.norm_value_compSMulL, W1p.norm_gradient_compSMulL] at h'
    refine le_of_mul_le_mul_left ?_ (hk hc)
    linarith
  · -- Test the inequality on `V` with the dilate `u (c⁻¹ • ·)`.
    intro h u hu
    have hVU := eq_preimage_inv_smul_of_eq_preimage_smul₀ hc hUV
    have hu' : W1p.compSMulL mu hp (inv_ne_zero hc) hVU u ∈ w1pVanishingOnSubmodule mu V p Γ := by
      rw [← W1p.compSMulL_mem_w1pVanishingOnSubmodule_iff hp (inv_ne_zero hc) hVU,
        LeftInverse.preimage_preimage (f := fun x : E => c⁻¹ • x) (fun x => smul_inv_smul₀ hc x)]
        at hu
      exact hu
    have h' := h _ hu'
    rw [W1p.norm_value_compSMulL, W1p.norm_gradient_compSMulL, abs_inv] at h'
    refine le_of_mul_le_mul_left ?_ (hk (inv_ne_zero hc))
    rw [abs_inv]
    have hcc : |c| * |c|⁻¹ = 1 := mul_inv_cancel₀ (abs_ne_zero.2 hc)
    set K := (|c|⁻¹ ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹
    calc K * ‖W1p.value u‖ ≤ |c| * C * (|c|⁻¹ * K * ‖W1p.gradient u‖) := h'
      _ = K * (C * ‖W1p.gradient u‖) := by
        linear_combination (C * K * ‖W1p.gradient u‖) * hcc

/-- **The Poincaré–Wirtinger constant scales linearly under dilation.** Let `c ≠ 0`, `1 ≤ p < ∞`
and `U = (c • ·)⁻¹(V)`, so that `V` is the dilate of `U` by `c`, and let `S ⊆ V`. The inequality
`‖u - ⨍_{(c • ·)⁻¹(S)} u‖_{Lᵖ(U)} ≤ C ‖∇u‖_{Lᵖ(U)}` holds for every `u ∈ W^{1,p}(U)` exactly when
`‖u - ⨍_S u‖_{Lᵖ(V)} ≤ |c| C ‖∇u‖_{Lᵖ(V)}` holds for every `u ∈ W^{1,p}(V)`. -/
theorem W1p.forall_eLpNorm_value_sub_setAverage_le_iff_of_preimage_smul (hp : p ≠ ⊤)
    (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V) {S : Set E} (hS : S ⊆ V) (C : ℝ) :
    (∀ u : W1p mu U p,
        eLpNorm (fun x => W1p.value u x - ⨍ y in (c • ·) ⁻¹' S, W1p.value u y ∂mu) p
          (mu.restrict U) ≤ ENNReal.ofReal C * ‖W1p.gradient u‖ₑ) ↔
      ∀ u : W1p mu V p,
        eLpNorm (fun x => W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) p (mu.restrict V) ≤
          ENNReal.ofReal (|c| * C) * ‖W1p.gradient u‖ₑ := by
  have hk {c : ℝ} (hc : c ≠ 0) :
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  rw [ENNReal.ofReal_mul (abs_nonneg c)]
  constructor
  · -- Test the inequality on `U` with the dilate `u (c • ·)`.
    intro h u
    have h' := h (W1p.compSMulL mu hp hc hUV u)
    rw [W1p.setAverage_value_compSMulL hp hc hUV hS, W1p.eLpNorm_value_compSMulL_sub hp hc hUV,
      W1p.enorm_gradient_compSMulL hp hc hUV] at h'
    refine (ENNReal.mul_le_mul_iff_right (hk hc) ENNReal.ofReal_ne_top).1 ?_
    calc _ ≤ _ := h'
      _ = _ := by ring
  · -- Test the inequality on `V` with the dilate `u (c⁻¹ • ·)`.
    intro h u
    have hVU := eq_preimage_inv_smul_of_eq_preimage_smul₀ hc hUV
    have hSU : (c • ·) ⁻¹' S ⊆ (U : Set E) := (preimage_mono hS).trans hUV.symm.subset
    have h' := h (W1p.compSMulL mu hp (inv_ne_zero hc) hVU u)
    rw [← LeftInverse.preimage_preimage (f := fun x : E => c⁻¹ • x)
        (fun x => smul_inv_smul₀ hc x) S,
      W1p.setAverage_value_compSMulL hp (inv_ne_zero hc) hVU hSU,
      W1p.eLpNorm_value_compSMulL_sub hp (inv_ne_zero hc) hVU,
      W1p.enorm_gradient_compSMulL hp (inv_ne_zero hc) hVU] at h'
    refine (ENNReal.mul_le_mul_iff_right (hk (inv_ne_zero hc)) ENNReal.ofReal_ne_top).1 ?_
    have hcc : ENNReal.ofReal |c| * ENNReal.ofReal |c⁻¹| = 1 := by
      rw [← ENNReal.ofReal_mul (abs_nonneg c), ← abs_mul, mul_inv_cancel₀ hc, abs_one,
        ENNReal.ofReal_one]
    calc _ ≤ _ := h'
      _ = ENNReal.ofReal (|c⁻¹| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ *
          (ENNReal.ofReal C * ‖W1p.gradient u‖ₑ) * (ENNReal.ofReal |c| * ENNReal.ofReal |c⁻¹|) := by
        ring
      _ = _ := by rw [hcc, mul_one]

end TauCeti
