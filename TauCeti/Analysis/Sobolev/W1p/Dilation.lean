/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.Analysis.Calculus.FDeriv.ConstSMul
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Integral.Average

/-!
# Dilations in `W^{1,p}`

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, let `c ≠ 0`, and let `U, V ⊆ E` be open with `U = c⁻¹ V`, that is
`U = (c • ·)⁻¹(V)`. For `1 ≤ p < ∞`, precomposition with the dilation `x ↦ c • x` is a bounded
operator `W^{1,p}(V) →L[ℝ] W^{1,p}(U)` (`TauCeti.W1p.compSMulL`), the case `Φ = c • ·` of
`TauCeti.W1p.compL`. Its value is `u (c • ·)` and its weak gradient is `c • (∇u) (c • ·)`, by the
chain rule, and it rescales the two halves of the Sobolev norm by exact factors:

`‖u (c • ·)‖_{Lᵖ(U)} = |c| ^ (-n / p) ‖u‖_{Lᵖ(V)}` and
`‖∇(u (c • ·))‖_{Lᵖ(U)} = |c| ^ (1 - n / p) ‖∇u‖_{Lᵖ(V)}`

(`TauCeti.W1p.norm_value_compSMulL`, `TauCeti.W1p.norm_gradient_compSMulL`). The extra factor
`|c|` in the gradient is the chain rule. The ratio of the two norms thus scales by `|c|⁻¹`, which
is why the constant of every first-order Poincaré inequality is proportional to the size of the
domain (`TauCeti.Analysis.Sobolev.Poincare.Dilation`).

## Main declarations

* `TauCeti.W1p.compSMulL`: precomposition with the dilation `x ↦ c • x`.
* `TauCeti.W1p.value_compSMulL_ae`, `TauCeti.W1p.gradient_compSMulL_ae`: its value and its weak
  gradient.
* `TauCeti.W1p.eLpNorm_value_compSMulL_sub`: the `Lᵖ` seminorm of the deviation of the dilate from
  a constant.
* `TauCeti.W1p.norm_value_compSMulL`, `TauCeti.W1p.norm_gradient_compSMulL`: the exact scaling of
  the `Lᵖ` norms of the value and of the weak gradient, and `TauCeti.W1p.enorm_gradient_compSMulL`,
  the latter in the extended norm.
* `TauCeti.W1p.setAverage_value_compSMulL`: means over a set are unchanged by the dilation.
* `TauCeti.W1p.compSMulL_compSMulL_of_mul_eq_one`: dilating by `d` and then by `c = d⁻¹` is the
  identity.
* `TauCeti.W1p.compSMulL_mem_w1pVanishingOnSubmodule_iff`: dilations preserve the spaces
  `W^{1,p}_Γ` of Sobolev functions vanishing on a boundary part `Γ`, which is dilated along: the
  dilation case of `TauCeti.W1p.compL_mem_w1pVanishingOnSubmodule_iff`.

The `Lᵖ` identities are `MeasureTheory.Measure.eLpNorm_comp_smul_restrict_preimage`, and the bounds
on the derivative of the dilation are `TauCeti.norm_fderiv_const_smul_le` and
`TauCeti.det_fderiv_const_smul`.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal InnerProductSpace Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {U V : Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ}

variable (mu) in
/-- **Dilation in `W^{1,p}`.** For `c ≠ 0`, `1 ≤ p < ∞` and `U = (c • ·)⁻¹(V)`, precomposition
with the dilation `x ↦ c • x` is a bounded linear operator `W^{1,p}(V) →L[ℝ] W^{1,p}(U)`, with value
`u (c • ·)` (`TauCeti.W1p.value_compSMulL_ae`) and weak gradient `c • (∇u) (c • ·)`
(`TauCeti.W1p.gradient_compSMulL_ae`). -/
def W1p.compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V) :
    W1p mu V p →L[ℝ] W1p mu U p :=
  W1p.compL (fun x => c • x) hp ((differentiable_id.const_smul c).differentiableOn)
    ((smul_right_injective E hc).injOn) (by rw [hUV]; exact mapsTo_preimage _ _)
    (fun x _ => norm_fderiv_const_smul_le c x) (pow_pos (abs_pos.2 hc) (finrank ℝ E))
    (fun x _ => by rw [det_fderiv_const_smul, abs_pow])

/-- The value of `W1p.compSMulL … u` is `u (c • ·)`, almost everywhere on `U`. -/
theorem W1p.value_compSMulL_ae (hp : p ≠ ⊤) (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V)
    (u : W1p mu V p) :
    W1p.value (W1p.compSMulL mu hp hc hUV u) =ᵐ[mu.restrict U] fun x => W1p.value u (c • x) :=
  W1p.value_compL_ae _ _ _ _ _ _ _ _ u

/-- **The chain rule for dilations.** The weak gradient of `W1p.compSMulL … u` is
`c • (∇u) (c • ·)`, almost everywhere on `U`. -/
theorem W1p.gradient_compSMulL_ae (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) (u : W1p mu V p) :
    W1p.gradient (W1p.compSMulL mu hp hc hUV u) =ᵐ[mu.restrict U]
      fun x => c • W1p.gradient u (c • x) := by
  rw [W1p.compSMulL]
  filter_upwards [W1p.gradient_compL_ae _ _ _ _ _ _ _ _ u] with x hx
  -- The derivative `c • id` is self-adjoint.
  have hadj : (fderiv ℝ (fun y : E => c • y) x).adjoint = c • ContinuousLinearMap.id ℝ E := by
    rw [fderiv_const_smul', eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro y z
    simp [real_inner_smul_left, real_inner_smul_right]
  rw [hx, hadj, smul_apply, ContinuousLinearMap.id_apply]

/-- **Dilation scaling of the deviation from a constant.** For every `a`,
`‖u (c • ·) - a‖_{Lᵖ(U)} = |c| ^ (-n / p) ‖u - a‖_{Lᵖ(V)}`, where `n` is the dimension of `E`. -/
theorem W1p.eLpNorm_value_compSMulL_sub (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) (u : W1p mu V p) (a : ℝ) :
    eLpNorm (fun x => W1p.value (W1p.compSMulL mu hp hc hUV u) x - a) p (mu.restrict U) =
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ *
        eLpNorm (fun x => W1p.value u x - a) p (mu.restrict V) := by
  rw [← Measure.eLpNorm_comp_smul_restrict_preimage mu _ hc p (V : Set E), ← hUV]
  refine eLpNorm_congr_ae ?_
  filter_upwards [W1p.value_compSMulL_ae hp hc hUV u] with x hx
  rw [hx]

/-- **Dilation scaling of the value.** `‖u (c • ·)‖_{Lᵖ(U)} = |c| ^ (-n / p) ‖u‖_{Lᵖ(V)}`, where
`n` is the dimension of `E`. -/
@[simp]
theorem W1p.norm_value_compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V)
    (u : W1p mu V p) :
    ‖W1p.value (W1p.compSMulL mu hp hc hUV u)‖ =
      (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ * ‖W1p.value u‖ := by
  have h := W1p.eLpNorm_value_compSMulL_sub hp hc hUV u 0
  simp only [sub_zero] at h
  rw [Lp.norm_def, Lp.norm_def, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- **Dilation scaling of the weak gradient.**
`‖∇(u (c • ·))‖_{Lᵖ(U)} = |c| ^ (1 - n / p) ‖∇u‖_{Lᵖ(V)}`, written as `|c| * |c| ^ (-n / p)`, where
`n` is the dimension of `E`. -/
@[simp]
theorem W1p.norm_gradient_compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) (u : W1p mu V p) :
    ‖W1p.gradient (W1p.compSMulL mu hp hc hUV u)‖ =
      |c| * (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ * ‖W1p.gradient u‖ := by
  have h : (fun x => c • W1p.gradient u (c • x)) = c • fun x => W1p.gradient u (c • x) :=
    (Pi.smul_def c _).symm
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (W1p.gradient_compSMulL_ae hp hc hUV u), h,
    eLpNorm_const_smul, hUV, Measure.eLpNorm_comp_smul_restrict_preimage mu _ hc]
  have hk : 0 ≤ (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ := by positivity
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk, mul_assoc]

/-- **Dilation scaling of the weak gradient**, in the extended norm:
`‖∇(u (c • ·))‖ₑ = |c| * |c| ^ (-n / p) * ‖∇u‖ₑ`, where `n` is the dimension of `E`. -/
theorem W1p.enorm_gradient_compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) (u : W1p mu V p) :
    ‖W1p.gradient (W1p.compSMulL mu hp hc hUV u)‖ₑ =
      ENNReal.ofReal |c| * ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ *
        ‖W1p.gradient u‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, W1p.norm_gradient_compSMulL, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (abs_nonneg c)]

/-- **Means are invariant under dilation.** For `S ⊆ V`, the mean of the dilate `u (c • ·)` over
`(c • ·)⁻¹(S)` is the mean of `u` over `S`. -/
theorem W1p.setAverage_value_compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) {S : Set E} (hS : S ⊆ V) (u : W1p mu V p) :
    ⨍ y in (c • ·) ⁻¹' S, W1p.value (W1p.compSMulL mu hp hc hUV u) y ∂mu =
      ⨍ y in S, W1p.value u y ∂mu := by
  have hSU : (c • ·) ⁻¹' S ⊆ (U : Set E) := (preimage_mono hS).trans hUV.symm.subset
  rw [average_congr (ae_restrict_of_ae_restrict_of_subset hSU (W1p.value_compSMulL_ae hp hc hUV u))]
  -- Change variables by `x ↦ c • x`, which pushes `mu` forward to `|c ^ n|⁻¹ • mu`.
  exact setAverage_comp_preimage_of_map_eq_smul
    (e := (Homeomorph.smulOfNeZero c hc).toMeasurableEquiv) (Measure.map_addHaar_smul mu hc)
    (by simp [hc]) ENNReal.ofReal_ne_top _ S

/-- Dilating by `d` and then by `c` with `d * c = 1` is the identity: for `u ∈ W^{1,p}(U)`,
`(u (d • ·)) (c • ·) = u`. -/
theorem W1p.compSMulL_compSMulL_of_mul_eq_one (hp : p ≠ ⊤) {d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hdc : d * c = 1) (hUV : (U : Set E) = (c • ·) ⁻¹' V) (hVU : (V : Set E) = (d • ·) ⁻¹' U)
    (u : W1p mu U p) :
    W1p.compSMulL mu hp hc hUV (W1p.compSMulL mu hp hd hVU u) = u := by
  rw [W1p.compSMulL, W1p.compSMulL]
  exact W1p.compL_compL_of_leftInvOn _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun x _ => by simp only [smul_smul, hdc, one_smul]) u

/-- **Dilations preserve vanishing on a boundary part.** For `c ≠ 0`, `1 ≤ p < ∞` and
`U = (c • ·)⁻¹(V)`, the dilate `u (c • ·)` lies in `W^{1,p}_{(c • ·)⁻¹(Γ)}(U)` exactly when `u` lies
in `W^{1,p}_Γ(V)`. -/
@[simp]
theorem W1p.compSMulL_mem_w1pVanishingOnSubmodule_iff (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) {Γ : Set E} {u : W1p mu V p} :
    W1p.compSMulL mu hp hc hUV u ∈ w1pVanishingOnSubmodule mu U p ((c • ·) ⁻¹' Γ) ↔
      u ∈ w1pVanishingOnSubmodule mu V p Γ := by
  rw [W1p.compSMulL]
  -- The inverse change of variables is the dilation `y ↦ c⁻¹ • y`.
  exact W1p.compL_mem_w1pVanishingOnSubmodule_iff _ hp _ _ _ _ _ _ (contDiff_const_smul c)
    (Homeomorph.smulOfNeZero c hc).isProperMap (contDiff_const_smul c⁻¹)
    (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc)).isProperMap
    (mapsTo_iff_subset_preimage.mpr (eq_preimage_inv_smul_of_eq_preimage_smul₀ hc hUV).subset)
    (fun y _ => norm_fderiv_const_smul_le c⁻¹ y) (pow_pos (abs_pos.2 (inv_ne_zero hc)) _)
    (fun y _ => by rw [det_fderiv_const_smul, abs_pow]) (fun y => smul_inv_smul₀ hc y)

end TauCeti
