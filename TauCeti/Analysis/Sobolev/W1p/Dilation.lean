/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Dilation

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
  the `Lᵖ` norms of the value and of the weak gradient.
* `TauCeti.W1p.setAverage_value_compSMulL`: means over a set are unchanged by the dilation.
* `TauCeti.W1p.compSMulL_compSMulL_of_mul_eq_one`: dilating by `d` and then by `c = d⁻¹` is the
  identity.
* `TauCeti.W1p.compSMulL_mem_w1pVanishingOnSubmodule_iff`: dilations preserve the spaces
  `W^{1,p}_Γ` of Sobolev functions vanishing on a boundary part `Γ`, which is dilated along.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal InnerProductSpace Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : ℝ}

/-- The dilation `x ↦ c • x` has derivative `c • id` everywhere. -/
private theorem fderiv_smul_left (c : ℝ) (x : E) :
    fderiv ℝ (fun y : E => c • y) x = c • ContinuousLinearMap.id ℝ E :=
  ((hasFDerivAt_id x).const_smul c).fderiv

private theorem norm_fderiv_smul_left_le (c : ℝ) (x : E) :
    ‖fderiv ℝ (fun y : E => c • y) x‖ ≤ |c| := by
  rw [fderiv_smul_left]
  exact (norm_smul_le c _).trans (by
    simpa [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg c))

private theorem abs_det_fderiv_smul_left (c : ℝ) (x : E) :
    |(fderiv ℝ (fun y : E => c • y) x).det| = |c| ^ finrank ℝ E := by
  rw [fderiv_smul_left, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow]

/-- The dilation `x ↦ c • x` as a continuous linear equivalence. -/
private def smulEquiv [FiniteDimensional ℝ E] (c : ℝ) (hc : c ≠ 0) : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv

/-- The Jacobian factor of the dilation in the `Lᵖ` seminorm. -/
private theorem ofReal_abs_inv_det_smulEquiv_rpow [FiniteDimensional ℝ E] (hc : c ≠ 0)
    (p : ℝ≥0∞) :
    ENNReal.ofReal |(LinearMap.det ((smulEquiv c hc : E ≃L[ℝ] E) : E →ₗ[ℝ] E))⁻¹| ^
        (1 / p).toReal =
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ := by
  have hdet : LinearMap.det ((smulEquiv c hc : E ≃L[ℝ] E) : E →ₗ[ℝ] E) = c ^ finrank ℝ E := by
    have h : ((smulEquiv c hc : E ≃L[ℝ] E) : E →ₗ[ℝ] E) = c • LinearMap.id := by
      ext x
      simp [smulEquiv]
    rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [hdet, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg, abs_inv, abs_pow,
    Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c), one_div,
    ENNReal.toReal_inv, div_eq_mul_inv]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
  [mu.IsAddHaarMeasure] {U V : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (mu) in
/-- **Dilation in `W^{1,p}`.** For `c ≠ 0`, `1 ≤ p < ∞` and `U = (c • ·)⁻¹(V)`, precomposition
with the dilation `x ↦ c • x` is a bounded linear operator `W^{1,p}(V) →L[ℝ] W^{1,p}(U)`, with value
`u (c • ·)` (`TauCeti.W1p.value_compSMulL_ae`) and weak gradient `c • (∇u) (c • ·)`
(`TauCeti.W1p.gradient_compSMulL_ae`). -/
def W1p.compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V) :
    W1p mu V p →L[ℝ] W1p mu U p :=
  W1p.compL (fun x => c • x) hp ((differentiable_id.const_smul c).differentiableOn)
    ((smul_right_injective E hc).injOn) (by rw [hUV]; exact mapsTo_preimage _ _)
    (fun x _ => norm_fderiv_smul_left_le c x) (pow_pos (abs_pos.2 hc) (finrank ℝ E))
    (fun x _ => (abs_det_fderiv_smul_left c x).ge)

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
    rw [fderiv_smul_left, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro y z
    simp [real_inner_smul_left, real_inner_smul_right]
  rw [hx, hadj, smul_apply, ContinuousLinearMap.id_apply]

/-- The `Lᵖ` seminorm on `U = (c • ·)⁻¹(V)` of `f (c • ·)` is `|c| ^ (-n / p)` times the `Lᵖ`
seminorm of `f` on `V`: the dilation case of
`MeasureTheory.Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage`, with its Jacobian
factor computed. -/
private theorem eLpNorm_comp_smul_restrict {G : Type*} [TopologicalSpace G] [ContinuousENorm G]
    (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V) (f : E → G) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (c • x)) p (mu.restrict U) =
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ * eLpNorm f p (mu.restrict V) := by
  rw [← ofReal_abs_inv_det_smulEquiv_rpow (E := E) hc p, hUV,
    ← Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage mu f (smulEquiv c hc) p]
  have he : ⇑(smulEquiv c hc : E ≃L[ℝ] E) = (c • ·) := by
    ext x
    simp [smulEquiv]
  rw [he, Function.comp_def]

/-- **Dilation scaling of the deviation from a constant.** For every `a`,
`‖u (c • ·) - a‖_{Lᵖ(U)} = |c| ^ (-n / p) ‖u - a‖_{Lᵖ(V)}`, where `n` is the dimension of `E`. -/
theorem W1p.eLpNorm_value_compSMulL_sub (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) (u : W1p mu V p) (a : ℝ) :
    eLpNorm (fun x => W1p.value (W1p.compSMulL mu hp hc hUV u) x - a) p (mu.restrict U) =
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ *
        eLpNorm (fun x => W1p.value u x - a) p (mu.restrict V) := by
  rw [← eLpNorm_comp_smul_restrict hc hUV (fun y => W1p.value u y - a)]
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
  have h : (fun x => c • W1p.gradient u (c • x)) = c • fun x => W1p.gradient u (c • x) := rfl
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (W1p.gradient_compSMulL_ae hp hc hUV u), h,
    eLpNorm_const_smul, eLpNorm_comp_smul_restrict hc hUV (W1p.gradient u),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), toReal_eNorm,
    Real.norm_eq_abs, mul_assoc]

/-- **Means are invariant under dilation.** For `S ⊆ V`, the mean of the dilate `u (c • ·)` over
`(c • ·)⁻¹(S)` is the mean of `u` over `S`. -/
theorem W1p.setAverage_value_compSMulL (hp : p ≠ ⊤) (hc : c ≠ 0)
    (hUV : (U : Set E) = (c • ·) ⁻¹' V) {S : Set E} (hS : S ⊆ V) (u : W1p mu V p) :
    ⨍ y in (c • ·) ⁻¹' S, W1p.value (W1p.compSMulL mu hp hc hUV u) y ∂mu =
      ⨍ y in S, W1p.value u y ∂mu := by
  have hSU : (c • ·) ⁻¹' S ⊆ (U : Set E) := by
    rw [hUV]
    exact preimage_mono hS
  have hcS : c • ((c • ·) ⁻¹' S) = S := by
    rw [← preimage_smul_inv₀ hc]
    ext y
    simp [smul_smul, mul_inv_cancel₀ hc]
  rw [setAverage_eq, setAverage_eq, integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hSU
      (W1p.value_compSMulL_ae hp hc hUV u)), Measure.setIntegral_comp_smul mu _ _ hc, hcS,
    measureReal_def, Measure.addHaar_preimage_smul mu hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), ← measureReal_def, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (by simpa using pow_ne_zero (finrank ℝ E) hc), mul_one]

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
  have hmem {U V : Opens E} {c : ℝ} (hc : c ≠ 0) (hUV : (U : Set E) = (c • ·) ⁻¹' V)
      {Γ : Set E} {u : W1p mu V p} (hu : u ∈ w1pVanishingOnSubmodule mu V p Γ) :
      W1p.compSMulL mu hp hc hUV u ∈ w1pVanishingOnSubmodule mu U p ((c • ·) ⁻¹' Γ) := by
    rw [W1p.compSMulL]
    exact W1p.compL_mem_w1pVanishingOnSubmodule _ _ _ _ _ _ _ _ (contDiff_const_smul c)
      (Homeomorph.smulOfNeZero c hc).isProperMap hu
  refine ⟨fun hu => ?_, hmem hc hUV⟩
  -- Undo the dilation by `c` with the dilation by `c⁻¹`.
  have hVU : (V : Set E) = (c⁻¹ • ·) ⁻¹' U := by
    rw [hUV]
    ext y
    simp [smul_inv_smul₀ hc]
  have h := hmem (inv_ne_zero hc) hVU hu
  have hΓ : (c⁻¹ • ·) ⁻¹' ((c • ·) ⁻¹' Γ) = Γ := by
    ext y
    simp [smul_smul, mul_inv_cancel₀ hc]
  rwa [hΓ, W1p.compSMulL_compSMulL_of_mul_eq_one hp (inv_ne_zero hc) hc (mul_inv_cancel₀ hc)]
    at h

end TauCeti
