/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import TauCeti.MeasureTheory.Function.Lp.Translation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.Young
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Convolution with an integrable kernel as an operator on `Lᵖ`

On a measurable additive group `G` with an s-finite right-invariant measure `μ`, for instance
an additive Haar measure on a finite-dimensional real normed space, the classical
convolution `(k ⋆ f)(x) = ∫ t, k(t) • f(x - t) dμ(t)` of `k ∈ L¹(μ; 𝕜)`, with `𝕜` real or
complex, and `f ∈ Lᵖ(μ; X)` has an integrand `t ↦ k(t) • f(x - t)` that is integrable for
almost every `x`, lies in `Lᵖ(μ; X)` for every `1 ≤ p ≤ ∞`, and its class does not depend on the
representatives of `k` and `f`. The first part of the file bundles it as a continuous bilinear map
`MeasureTheory.Lp.addConvolutionL μ p : L¹(μ; 𝕜) →L[𝕜] Lᵖ(μ; X) →L[𝕜] Lᵖ(μ; X)` of norm at most
one, which is Young's inequality. This includes the endpoint `p = ∞`, where translation is not
continuous on `L∞` and the translate-integral description below is not available.

Let `k` be an integrable real function on a finite-dimensional real normed space `E` with an
additive Haar measure `μ`, and let `1 ≤ p < ∞`. Convolution with `k` acts on `Lᵖ(μ; F)` by the
`Lᵖ`-valued Bochner integral

`f ↦ ∫ y, k(y) • f(· - y) dμ(y)`,

which is an average of translates of `f`. Taking the integral in `Lᵖ` rather than pointwise
avoids any choice of representative: translation is a strongly continuous family of linear
isometries of `Lᵖ` for `p < ∞`, so the integrand is Bochner integrable as soon as `k` is.

This file bundles that integral as a continuous linear operator, identifies it almost
everywhere with the classical pointwise convolution, and proves the two facts on which a
convolution semigroup rests:

* **Young's inequality** for an `L¹` kernel: the operator norm is at most `∫ ‖k‖`, that is,
  `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`;
* **associativity**: convolving with `k₁ ⋆ k₂` is convolving with `k₂` and then with `k₁`.

It also proves that the dilations `k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` of any integrable kernel, with
`d` the dimension of `E`, form an approximate identity: `k_ε ⋆ f → (∫ k) • f` in `Lᵖ` as
`ε → 0⁺`, with no sign, normalization or support condition on `k`. This is proved for real or
complex kernels acting on Banach-valued functions through the `Lᵖ`-valued integral of
translates: after the substitution `y = ε • z` the integrand is `k(z) • f(· - ε • z)`, which tends
to `k(z) • f` and is dominated by `‖k(z)‖ ‖f‖_p`. The underlying convergence of dilated-kernel
averages of a bounded function continuous at `0`, `TauCeti.tendsto_integral_comp_inv_smul_smul`,
is in `TauCeti.MeasureTheory.Integral.Dilation`.

## Main declarations

* `MeasureTheory.Lp.addConvolutionL`: convolution `L¹(μ; 𝕜) × Lᵖ(μ; X) → Lᵖ(μ; X)` on an
  additive group, for `1 ≤ p ≤ ∞`, as a continuous bilinear map.
* `MeasureTheory.Lp.coeFn_addConvolutionL`: its values are represented almost everywhere by the
  pointwise convolution `k ⋆ f`.
* `MeasureTheory.Lp.norm_addConvolutionL_apply_le`: Young's inequality `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`.
* `MeasureTheory.Lp.compLpL_addConvolutionL`: convolution commutes with postcomposition by a
  continuous linear map between Banach spaces.
* `TauCeti.convolutionLp_eq_addConvolutionL`: for `p < ∞` and a real kernel, the translate-integral
  operator `TauCeti.convolutionLp` is `MeasureTheory.Lp.addConvolutionL` at the `L¹` class of the
  kernel.
* `TauCeti.convolutionLp`: convolution with a real kernel as a continuous linear operator on
  `Lᵖ`; it is zero when the kernel is not integrable.
* `TauCeti.convolutionLp_apply`: the defining `Lᵖ`-valued Bochner integral.
* `TauCeti.norm_convolutionLp_le`: Young's inequality `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`.
* `TauCeti.convolutionLp_convolution`: `(k₁ ⋆ k₂) ⋆ f = k₁ ⋆ (k₂ ⋆ f)`.
* `TauCeti.convolutionLp_zero`, `TauCeti.convolutionLp_add`, `TauCeti.convolutionLp_smul`,
  `TauCeti.convolutionLp_neg`, `TauCeti.convolutionLp_sub`: the operator is linear in the
  integrable kernel, so Young's inequality also bounds the distance
  between two convolution operators by the `L¹` distance of their kernels.
* `TauCeti.convolutionLp_comp_comm`: convolution operators commute.
* `TauCeti.convolutionLp_ae_eq_convolution`: the operator is represented almost everywhere by the
  classical pointwise convolution `(k ⋆ f)(x) = ∫ y, k(y) • f(x - y) dμ(y)`;
  `TauCeti.convolutionLp_ae_eq_convolution_coeFn` is the same for an element of `Lᵖ`.
* `TauCeti.convolutionLp_nonneg`: convolution with a nonnegative kernel preserves positivity.
* `TauCeti.integral_convolutionLp`: on `L¹`, `∫ k ⋆ f = (∫ k) • ∫ f`.
* `TauCeti.integrable_convolution_integrand_restrict`: on a set of finite measure, the
  convolution integrand `(x, y) ↦ k(y) • f(x - y)` of an `L¹` kernel and an `Lᵖ` function is
  integrable, which justifies local Fubini arguments.
* `TauCeti.compLpL_convolutionLp`: convolution commutes with postcomposition by a continuous
  linear map between Banach spaces.
* `TauCeti.tendsto_integral_comp_inv_smul_smul_translateLp`: for an integrable real or complex
  kernel `k`, the averages `∫ y, k_ε(y) • f(· - y) dμ(y)` converge to `(∫ k) • f` in `Lᵖ`.
* `TauCeti.tendsto_convolutionLp_comp_inv_smul`: for a real kernel, `k_ε ⋆ f → (∫ k) • f` in
  `Lᵖ` as `ε → 0⁺`, and `TauCeti.norm_convolutionLp_comp_inv_smul_le` bounds the operator norms
  of these convolutions by `∫ ‖k‖`, uniformly in `ε`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Section 8.2; Theorem 8.14 for dilations of an integrable kernel.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.15.
* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces, Volume I*,
  Lemma 1.2.30 (Young's inequality, including the endpoint `p = ∞` by the authors' errata) and
  Proposition 1.2.32, for Banach-valued functions.
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open ContinuousLinearMap Filter
open scoped Convolution ENNReal

/-! ### Convolution of `L¹` with `Lᵖ` on an additive group

On a measurable additive group with an s-finite right-invariant measure, such as an additive
Haar measure on a finite-dimensional real normed space, the convolution
`(k ⋆ f)(x) = ∫ t, k(t) • f(x - t) dμ(t)` of `k ∈ L¹(μ; 𝕜)` and `f ∈ Lᵖ(μ; X)` has an integrand
that is integrable at almost every `x`, and lies in `Lᵖ(μ; X)` for every `1 ≤ p ≤ ∞`
(`MeasureTheory.Integrable.ae_convolution_exists_of_memLp` and
`MeasureTheory.Integrable.memLp_convolution`), and its
almost-everywhere class does not depend on the representatives of `k` and `f`
(`MeasureTheory.convolution_congr`). -/

variable {G X : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G]
  [MeasurableNeg G] {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 X]

omit [NormedSpace ℝ X] in
private theorem ae_convolutionExistsAt (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt (k : G → 𝕜) (f : G → X) x (lsmul 𝕜 𝕜) μ :=
  (L1.integrable_coeFn k).ae_convolution_exists_of_memLp _ (Lp.memLp f) Fact.out

private theorem memLp_convolution (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    MemLp ((k : G → 𝕜) ⋆[lsmul 𝕜 𝕜, μ] (f : G → X)) p μ :=
  (L1.integrable_coeFn k).memLp_convolution _ (Lp.memLp f) Fact.out

private theorem toLp_convolution_add_left (k₁ k₂ : Lp 𝕜 1 μ) (f : Lp X p μ) :
    (memLp_convolution (k₁ + k₂) f).toLp _ =
      (memLp_convolution k₁ f).toLp _ + (memLp_convolution k₂ f).toLp _ := by
  rw [← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  rw [convolution_congr _ (Lp.coeFn_add k₁ k₂) EventuallyEq.rfl]
  filter_upwards [ae_convolutionExistsAt k₁ f, ae_convolutionExistsAt k₂ f] with x h₁ h₂
  exact h₁.add_distrib h₂

private theorem toLp_convolution_add_right (k : Lp 𝕜 1 μ) (f₁ f₂ : Lp X p μ) :
    (memLp_convolution k (f₁ + f₂)).toLp _ =
      (memLp_convolution k f₁).toLp _ + (memLp_convolution k f₂).toLp _ := by
  rw [← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  rw [convolution_congr _ EventuallyEq.rfl (Lp.coeFn_add f₁ f₂)]
  filter_upwards [ae_convolutionExistsAt k f₁, ae_convolutionExistsAt k f₂] with x h₁ h₂
  exact h₁.distrib_add h₂

variable [SMulCommClass ℝ 𝕜 X]

private theorem toLp_convolution_smul_left (c : 𝕜) (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    (memLp_convolution (c • k) f).toLp _ = c • (memLp_convolution k f).toLp _ := by
  rw [← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (EventuallyEq.of_eq ?_)
  rw [convolution_congr _ (Lp.coeFn_smul c k) EventuallyEq.rfl, smul_convolution]

private theorem toLp_convolution_smul_right (c : 𝕜) (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    (memLp_convolution k (c • f)).toLp _ = c • (memLp_convolution k f).toLp _ := by
  rw [← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (EventuallyEq.of_eq ?_)
  rw [convolution_congr _ EventuallyEq.rfl (Lp.coeFn_smul c f), convolution_smul]

omit [SMulCommClass ℝ 𝕜 X] in
/-- Young's inequality `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`, in the form needed to bundle the convolution. -/
private theorem norm_toLp_convolution_le (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    ‖(memLp_convolution k f).toLp _‖ ≤ 1 * ‖k‖ * ‖f‖ := by
  rw [one_mul, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top k) (Lp.eLpNorm_ne_top f)) ?_
  calc eLpNorm ((k : G → 𝕜) ⋆[lsmul 𝕜 𝕜, μ] (f : G → X)) p μ
      ≤ ‖(lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] X →L[𝕜] X)‖ₑ * eLpNorm k 1 μ * eLpNorm f p μ :=
        eLpNorm_convolution_le _ (Lp.aestronglyMeasurable k) (Lp.aestronglyMeasurable f) Fact.out
    _ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
        rw [mul_assoc]
        refine mul_le_of_le_one_left' ?_
        simpa [eNorm_eq_nnNorm] using ENNReal.coe_le_coe.2 opNNNorm_lsmul_le

variable (μ p) in
/-- **Convolution of an `L¹` kernel with an `Lᵖ` function**, for every `1 ≤ p ≤ ∞`: the
continuous bilinear map `(k, f) ↦ k ⋆ f` from `L¹(μ; 𝕜) × Lᵖ(μ; X)` to `Lᵖ(μ; X)` sending the
classes of `k` and `f` to the class of `x ↦ ∫ t, k(t) • f(x - t) dμ(t)`
(`MeasureTheory.Lp.coeFn_addConvolutionL`). It has norm at most one
(`MeasureTheory.Lp.norm_addConvolutionL_le`), which is **Young's inequality**
`‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`.

The kernel may be real or complex and `X` is any normed space; as for the Bochner integral, the
convolution vanishes unless `X` is complete. For finite `p` on a multiplicatively written locally
compact group, the analogous operator, defined as an integral of translates, is
`MeasureTheory.Lp.convolutionL`. -/
def addConvolutionL : Lp 𝕜 1 μ →L[𝕜] Lp X p μ →L[𝕜] Lp X p μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun k f ↦ (memLp_convolution k f).toLp _) toLp_convolution_add_left
      toLp_convolution_smul_left toLp_convolution_add_right toLp_convolution_smul_right)
    1 norm_toLp_convolution_le

private theorem addConvolutionL_apply (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    addConvolutionL μ p k f = (memLp_convolution k f).toLp _ :=
  (rfl)

/-- The convolution `k ⋆ f` of `k ∈ L¹` and `f ∈ Lᵖ` is represented almost everywhere by
`x ↦ ∫ t, k(t) • f(x - t) dμ(t)`. -/
theorem coeFn_addConvolutionL (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    addConvolutionL μ p k f =ᵐ[μ] (k : G → 𝕜) ⋆[lsmul 𝕜 𝕜, μ] (f : G → X) := by
  rw [addConvolutionL_apply]
  exact MemLp.coeFn_toLp _

/-- The convolution of the classes of an integrable `k` and of `f ∈ Lᵖ` is represented almost
everywhere by `x ↦ ∫ t, k(t) • f(x - t) dμ(t)`. -/
theorem coeFn_addConvolutionL_toL1_toLp {k : G → 𝕜} (hk : Integrable k μ) {f : G → X}
    (hf : MemLp f p μ) :
    addConvolutionL μ p (hk.toL1 k) (hf.toLp f) =ᵐ[μ] k ⋆[lsmul 𝕜 𝕜, μ] f := by
  rw [← convolution_congr _ hk.coeFn_toL1 hf.coeFn_toLp]
  exact coeFn_addConvolutionL _ _

/-- **Young's inequality** for an `L¹` kernel: `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`. -/
theorem norm_addConvolutionL_apply_le (k : Lp 𝕜 1 μ) (f : Lp X p μ) :
    ‖addConvolutionL μ p k f‖ ≤ ‖k‖ * ‖f‖ := by
  simpa only [addConvolutionL_apply, one_mul] using norm_toLp_convolution_le k f

/-- Convolution has norm at most one as a bilinear map. -/
theorem norm_addConvolutionL_le : ‖addConvolutionL (𝕜 := 𝕜) (X := X) μ p‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end NontriviallyNormedField

/-- Convolution commutes with postcomposition by a continuous linear map between Banach spaces:
`T ∘ (k ⋆ f) = k ⋆ (T ∘ f)`. -/
theorem compLpL_addConvolutionL {𝕜 Y : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 X]
    [SMulCommClass ℝ 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedSpace 𝕜 Y] [SMulCommClass ℝ 𝕜 Y] [CompleteSpace Y] (T : X →L[𝕜] Y) (k : Lp 𝕜 1 μ)
    (f : Lp X p μ) :
    T.compLpL p μ (addConvolutionL μ p k f) = addConvolutionL μ p k (T.compLpL p μ f) := by
  refine Lp.ext ?_
  have hTf : (k : G → 𝕜) ⋆[lsmul 𝕜 𝕜, μ] (T.compLpL p μ f : G → Y) =
      (k : G → 𝕜) ⋆[lsmul 𝕜 𝕜, μ] fun y ↦ T (f y) :=
    convolution_congr _ EventuallyEq.rfl (T.coeFn_compLpL f)
  filter_upwards [T.coeFn_compLpL (addConvolutionL μ p k f), coeFn_addConvolutionL k f,
    coeFn_addConvolutionL k (T.compLpL p μ f), ae_convolutionExistsAt k f] with x h₁ h₂ h₃ hx
  rw [h₁, h₂, h₃, hTf, T.convolution_lsmul_comp_comm hx]

end MeasureTheory.Lp

namespace TauCeti

open ContinuousLinearMap _root_.MeasureTheory
open scoped Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `p < ∞`, weighting the translates `f(· - y)` of an `Lᵖ` function by an integrable kernel
gives a Bochner-integrable `Lᵖ`-valued function of `y`. -/
theorem integrable_smul_translateLp (hp : p ≠ ∞) {k : E → ℝ} (hk : Integrable k μ)
    (f : Lp F p μ) : Integrable (fun y ↦ k y • μ.translateLp p (-y) f) μ :=
  hk.smul_of_top_left <| memLp_top_of_bound
    ((Measure.continuous_translateLp hp f).comp continuous_neg).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun _ ↦ (LinearIsometryEquiv.norm_map _ f).le)

open scoped Classical in
/-- Convolution with a real kernel `k`, as a continuous linear operator on `Lᵖ` for `p < ∞`:
for integrable `k` it sends `f` to the `Lᵖ`-valued Bochner integral `∫ y, k y • f(· - y) dμ`
(`TauCeti.convolutionLp_apply`). It is defined to be zero when `k` is not integrable.

As with `MeasureTheory.integral`, completeness of `F` is not part of the definition: the
Bochner integral vanishes unless `Lᵖ(μ; F)` is complete, so the operator is the advertised
convolution precisely when `F` is a Banach space. Its norm is at most `∫ ‖k‖` in either case
(`TauCeti.norm_convolutionLp_le`). -/
def convolutionLp (hp : p ≠ ∞) (k : E → ℝ) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Lp F p μ →L[ℝ] Lp F p μ :=
  if hk : Integrable k μ then
    LinearMap.mkContinuous
      { toFun f := ∫ y, k y • μ.translateLp p (-y) f ∂μ
        map_add' f g := by
          simp only [map_add, smul_add]
          exact integral_add (integrable_smul_translateLp hp hk f)
            (integrable_smul_translateLp hp hk g)
        map_smul' c f := by
          simp only [map_smul, smul_comm _ c, integral_smul, RingHom.id_apply] }
      (∫ y, ‖k y‖ ∂μ) fun f ↦ by
        refine (norm_integral_le_of_norm_le (hk.norm.mul_const ‖f‖) (ae_of_all _ fun y ↦ ?_)).trans
          (integral_mul_const _ _).le
        rw [norm_smul, LinearIsometryEquiv.norm_map]
  else 0

/-- The defining `Lᵖ`-valued Bochner integral of convolution with an integrable kernel. -/
theorem convolutionLp_apply (hp : p ≠ ∞) {k : E → ℝ} (hk : Integrable k μ) (f : Lp F p μ) :
    convolutionLp hp k μ f = ∫ y, k y • μ.translateLp p (-y) f ∂μ := by
  simp only [convolutionLp, hk, ↓reduceDIte, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk]

/-- Convolution with a non-integrable kernel is the zero operator by convention. -/
theorem convolutionLp_of_not_integrable (hp : p ≠ ∞) {k : E → ℝ} (hk : ¬Integrable k μ) :
    convolutionLp (F := F) hp k μ = 0 := by
  simp only [convolutionLp, hk, ↓reduceDIte]

/-- **Young's inequality** for convolution with an integrable kernel:
`‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` for `1 ≤ p < ∞`, as a bound on the operator norm. -/
theorem norm_convolutionLp_le (hp : p ≠ ∞) (k : E → ℝ) :
    ‖convolutionLp (F := F) hp k μ‖ ≤ ∫ y, ‖k y‖ ∂μ := by
  by_cases hk : Integrable k μ
  · simp only [convolutionLp, hk, ↓reduceDIte]
    exact LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _
  · rw [convolutionLp_of_not_integrable hp hk, norm_zero]
    exact integral_nonneg fun _ ↦ norm_nonneg _

/-- Convolution on `Lᵖ` is additive in the integrable kernel. -/
theorem convolutionLp_add (hp : p ≠ ∞) {k₁ k₂ : E → ℝ} (hk₁ : Integrable k₁ μ)
    (hk₂ : Integrable k₂ μ) :
    convolutionLp (F := F) hp (k₁ + k₂) μ = convolutionLp hp k₁ μ + convolutionLp hp k₂ μ := by
  ext1 f
  rw [add_apply, convolutionLp_apply hp (hk₁.add hk₂), convolutionLp_apply hp hk₁,
    convolutionLp_apply hp hk₂, ← integral_add (integrable_smul_translateLp hp hk₁ f)
      (integrable_smul_translateLp hp hk₂ f)]
  simp only [Pi.add_apply, add_smul]

/-- Convolution on `Lᵖ` with the zero kernel is the zero operator. -/
@[simp]
theorem convolutionLp_zero (hp : p ≠ ∞) : convolutionLp (F := F) hp (0 : E → ℝ) μ = 0 := by
  ext1 f
  simp [convolutionLp_apply hp (integrable_zero E ℝ μ)]

/-- Convolution on `Lᵖ` is homogeneous in the kernel. -/
@[simp]
theorem convolutionLp_smul (hp : p ≠ ∞) (c : ℝ) (k : E → ℝ) :
    convolutionLp (F := F) hp (c • k) μ = c • convolutionLp hp k μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · ext1 f
    simp
  by_cases hk : Integrable k μ
  · ext1 f
    rw [smul_apply, convolutionLp_apply hp (hk.smul c), convolutionLp_apply hp hk,
      ← integral_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
  · have hck : ¬Integrable (c • k) μ := by rwa [integrable_smul_iff hc]
    rw [convolutionLp_of_not_integrable hp hk, convolutionLp_of_not_integrable hp hck]
    exact (smul_zero (A := Lp F p μ →L[ℝ] Lp F p μ) c).symm

/-- Convolution on `Lᵖ` with the negated kernel is the negated operator. -/
@[simp]
theorem convolutionLp_neg (hp : p ≠ ∞) (k : E → ℝ) :
    convolutionLp (F := F) hp (-k) μ = -convolutionLp hp k μ := by
  rw [← neg_one_smul ℝ k, convolutionLp_smul]
  ext1 f
  simp

/-- Convolution on `Lᵖ` turns differences of integrable kernels into differences of operators. -/
theorem convolutionLp_sub (hp : p ≠ ∞) {k₁ k₂ : E → ℝ} (hk₁ : Integrable k₁ μ)
    (hk₂ : Integrable k₂ μ) :
    convolutionLp (F := F) hp (k₁ - k₂) μ = convolutionLp hp k₁ μ - convolutionLp hp k₂ μ := by
  rw [sub_eq_add_neg, convolutionLp_add hp hk₁ hk₂.neg, convolutionLp_neg, ← sub_eq_add_neg]

/-- **Associativity of convolution on `Lᵖ`.** For integrable kernels `k₁` and `k₂`, convolving
an `Lᵖ` function with `k₁ ⋆ k₂` is convolving it with `k₂` and then with `k₁`. -/
theorem convolutionLp_convolution [CompleteSpace F] (hp : p ≠ ∞) {k₁ k₂ : E → ℝ}
    (hk₁ : Integrable k₁ μ) (hk₂ : Integrable k₂ μ) :
    convolutionLp (F := F) hp (k₁ ⋆[lsmul ℝ ℝ, μ] k₂) μ =
      (convolutionLp hp k₁ μ).comp (convolutionLp hp k₂ μ) := by
  ext1 f
  set τ : E → Lp F p μ := fun y ↦ μ.translateLp p (-y) f with hτ
  have hτc : Continuous τ := (Measure.continuous_translateLp hp f).comp continuous_neg
  -- The integrand `(w, y) ↦ k₁(y) k₂(w - y) • f(· - w)` is integrable on `E × E`.
  have hint : Integrable (Function.uncurry fun w y ↦ (k₁ y * k₂ (w - y)) • τ w) (μ.prod μ) := by
    have hconv := hk₁.convolution_integrand (lsmul ℝ ℝ) hk₂
    simp only [lsmul_apply, smul_eq_mul] at hconv
    exact hconv.smul_of_top_left <| memLp_top_of_bound
      (hτc.comp continuous_fst).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun _ ↦ (LinearIsometryEquiv.norm_map _ f).le)
  rw [convolutionLp_apply hp (hk₁.integrable_convolution (lsmul ℝ ℝ) hk₂), comp_apply,
    convolutionLp_apply hp hk₂, convolutionLp_apply hp hk₁]
  calc ∫ w, (k₁ ⋆[lsmul ℝ ℝ, μ] k₂) w • τ w ∂μ
      = ∫ w, ∫ y, (k₁ y * k₂ (w - y)) • τ w ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
        simp only [convolution_lsmul, smul_eq_mul, integral_smul_const]
    _ = ∫ y, ∫ w, (k₁ y * k₂ (w - y)) • τ w ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, k₁ y • μ.translateLp p (-y) (∫ z, k₂ z • τ z ∂μ) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        -- Substitute `w = z + y` and pull the translation and `k₁ y` inside the inner integral.
        refine (integral_add_right_eq_self (μ := μ)
          (fun w ↦ (k₁ y * k₂ (w - y)) • τ w) y).symm.trans ?_
        beta_reduce
        rw [← LinearIsometryEquiv.coe_toLinearIsometry, ← LinearIsometry.integral_comp_comm,
          ← integral_smul]
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        simp only [hτ, LinearIsometryEquiv.coe_toLinearIsometry, map_smul, smul_smul]
        rw [add_sub_cancel_right, ← LinearIsometryEquiv.trans_apply, ← Measure.translateLp_add,
          neg_add, add_comm (-z) (-y)]

/-- Convolution operators commute: `k₁ ⋆ (k₂ ⋆ f) = k₂ ⋆ (k₁ ⋆ f)`. Both sides vanish when
either kernel is not integrable. -/
theorem convolutionLp_comp_comm [CompleteSpace F] (hp : p ≠ ∞) (k₁ k₂ : E → ℝ) :
    (convolutionLp (F := F) hp k₁ μ).comp (convolutionLp hp k₂ μ) =
      (convolutionLp hp k₂ μ).comp (convolutionLp hp k₁ μ) := by
  by_cases hk₁ : Integrable k₁ μ
  swap
  · simp [convolutionLp_of_not_integrable hp hk₁]
  by_cases hk₂ : Integrable k₂ μ
  swap
  · simp [convolutionLp_of_not_integrable hp hk₂]
  have hL : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    ext
    simp
  rw [← convolutionLp_convolution hp hk₁ hk₂, ← convolutionLp_convolution hp hk₂ hk₁,
    convolution_symm _ hL]

/-- On a set `s` of finite measure, the convolution integrand `(x, y) ↦ k(y) • f(x - y)` of an
integrable kernel `k` and an `Lᵖ` function `f` is integrable: `∫_s ‖f(x - y)‖ dx` is bounded
uniformly in `y`, by the `Lᵖ` norm of `f`. -/
theorem integrable_convolution_integrand_restrict {k : E → ℝ}
    (hk : Integrable k μ) {f : E → F} (hf : MemLp f p μ) {s : Set E} (hμs : μ s < ∞) :
    Integrable (Function.uncurry fun x y ↦ k y • f (x - y)) ((μ.restrict s).prod μ) := by
  have _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y ↦ k y • f (x - y))
      ((μ.restrict s).prod μ) :=
    (hk.aestronglyMeasurable.convolution_integrand (lsmul ℝ ℝ) hf.aestronglyMeasurable).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  -- The restriction to `s` of a translate of `f`, as an `L¹(s)` class, has norm at most `C`.
  set R := Set.LpToL1RestrictCLM (𝕜 := ℝ) (F := F) (p := p) s hμs
  have hbound (y : E) : ∫ x in s, ‖f (x - y)‖ ∂μ ≤ ‖R‖ * ‖hf.toLp f‖ := by
    calc ∫ x in s, ‖f (x - y)‖ ∂μ = ‖R (μ.translateLp p (-y) (hf.toLp f))‖ := by
          rw [L1.norm_eq_integral_norm]
          refine integral_congr_ae ?_
          filter_upwards [Set.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) s hμs
            (μ.translateLp p (-y) (hf.toLp f)),
            ae_restrict_of_ae (hf.coeFn_translateLp_toLp (-y))] with x hx hx'
          rw [hx, hx', sub_eq_add_neg]
      _ ≤ ‖R‖ * ‖hf.toLp f‖ := by
          rw [← LinearIsometryEquiv.norm_map (μ.translateLp p (-y)) (hf.toLp f)]
          exact R.le_opNorm _
  refine (integrable_prod_iff' hmeas).2 ⟨ae_of_all _ fun y ↦ ?_, ?_⟩
  · exact (((hf.comp_measurePreserving (measurePreserving_sub_right μ y)).restrict s).integrable
      Fact.out).smul (k y)
  · refine (hk.norm.mul_const (‖R‖ * ‖hf.toLp f‖)).mono' hmeas.prod_swap.norm.integral_prod_right'
      (ae_of_all _ fun y ↦ ?_)
    simp only [Function.uncurry_apply_pair, norm_smul, integral_const_mul]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _)

/-- **The pointwise representative of `convolutionLp`.** For an integrable kernel `k` and
`f ∈ Lᵖ`, the `Lᵖ` class `convolutionLp hp k μ f` is represented almost everywhere by the
classical convolution `(k ⋆ f)(x) = ∫ y, k(y) • f(x - y) dμ(y)`. -/
theorem convolutionLp_ae_eq_convolution [CompleteSpace F] (hp : p ≠ ∞) {k : E → ℝ}
    (hk : Integrable k μ) {f : E → F} (hf : MemLp f p μ) :
    convolutionLp hp k μ (hf.toLp f) =ᵐ[μ] k ⋆[lsmul ℝ ℝ, μ] f := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hμs ↦ ?_) (fun s _ hμs ↦ ?_) fun s _ hμs ↦ ?_
  · have _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
    exact ((Lp.memLp _).restrict s).integrable Fact.out
  · have h := (integrable_convolution_integrand_restrict hk hf hμs).integral_prod_left
    simp only [Function.uncurry_apply_pair] at h
    exact h.congr (ae_of_all _ fun x ↦ convolution_lsmul.symm)
  -- Integrate over `s` inside the `Lᵖ`-valued integral, then exchange the two integrals.
  set S := Set.setIntegralLp (𝕜 := ℝ) (F := F) (p := p) s hμs
  calc ∫ x in s, convolutionLp hp k μ (hf.toLp f) x ∂μ
      = S (convolutionLp hp k μ (hf.toLp f)) := (Set.setIntegralLp_apply s hμs _).symm
    _ = ∫ y, k y • ∫ x in s, f (x - y) ∂μ ∂μ := by
        rw [convolutionLp_apply hp hk,
          ← S.integral_comp_comm (integrable_smul_translateLp hp hk _)]
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        dsimp only
        rw [map_smul, Set.setIntegralLp_apply]
        congr 1
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hf.coeFn_translateLp_toLp (-y)] with x hx
        rw [hx, sub_eq_add_neg]
    _ = ∫ y, ∫ x in s, k y • f (x - y) ∂μ ∂μ := by simp only [integral_smul]
    _ = ∫ x in s, (k ⋆[lsmul ℝ ℝ, μ] f) x ∂μ := by
        rw [← integral_integral_swap (integrable_convolution_integrand_restrict hk hf hμs)]
        simp only [convolution_lsmul]

/-- The pointwise representative of `convolutionLp` applied to an element `f` of `Lᵖ`: the class
`convolutionLp hp k μ f` is represented almost everywhere by `k ⋆ f`, for integrable `k`. -/
theorem convolutionLp_ae_eq_convolution_coeFn [CompleteSpace F] (hp : p ≠ ∞) {k : E → ℝ}
    (hk : Integrable k μ) (f : Lp F p μ) :
    convolutionLp hp k μ f =ᵐ[μ] k ⋆[lsmul ℝ ℝ, μ] (f : E → F) := by
  simpa only [Lp.toLp_coeFn] using convolutionLp_ae_eq_convolution hp hk (Lp.memLp f)

/-- For a real kernel and `p < ∞`, convolution with `k` is the bilinear convolution
`MeasureTheory.Lp.addConvolutionL` with the `L¹` class of `k`. -/
theorem convolutionLp_eq_addConvolutionL [CompleteSpace F] (hp : p ≠ ∞) {k : E → ℝ}
    (hk : Integrable k μ) (f : Lp F p μ) :
    convolutionLp hp k μ f = Lp.addConvolutionL μ p (hk.toL1 k) f := by
  refine Lp.ext ?_
  filter_upwards [convolutionLp_ae_eq_convolution_coeFn hp hk f,
    Lp.coeFn_addConvolutionL (hk.toL1 k) f] with x h₁ h₂
  rw [h₁, h₂, convolution_congr _ hk.coeFn_toL1 Filter.EventuallyEq.rfl]

/-- **Convolution with a nonnegative kernel preserves positivity**: if `k ≥ 0` almost everywhere
and `f ∈ Lᵖ` is nonnegative, then so is `k ⋆ f`. -/
theorem convolutionLp_nonneg (hp : p ≠ ∞) {k : E → ℝ} (hk : 0 ≤ᵐ[μ] k) {f : Lp ℝ p μ}
    (hf : 0 ≤ f) : 0 ≤ convolutionLp hp k μ f := by
  by_cases hki : Integrable k μ
  · have h := convolutionLp_ae_eq_convolution_coeFn hp hki f
    rw [← Lp.coeFn_nonneg] at hf ⊢
    filter_upwards [h] with x hx
    rw [hx, convolution_lsmul]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hk, (quasiMeasurePreserving_sub_left μ x).ae hf] with y hky hfy
    exact smul_nonneg hky hfy
  · rw [convolutionLp_of_not_integrable hp hki, _root_.zero_apply]

/-- **Convolution multiplies integrals**: for `f ∈ L¹`, `∫ k ⋆ f = (∫ k) • ∫ f`. Both sides
vanish when `k` is not integrable. -/
theorem integral_convolutionLp [CompleteSpace F] (k : E → ℝ) (f : Lp F 1 μ) :
    ∫ x, convolutionLp ENNReal.one_ne_top k μ f x ∂μ = (∫ x, k x ∂μ) • ∫ x, f x ∂μ := by
  by_cases hk : Integrable k μ
  · rw [integral_congr_ae (convolutionLp_ae_eq_convolution_coeFn ENNReal.one_ne_top hk f),
      integral_convolution _ hk (L1.integrable_coeFn f), lsmul_apply]
  · rw [convolutionLp_of_not_integrable ENNReal.one_ne_top hk, integral_undef hk, zero_smul,
      _root_.zero_apply, integral_congr_ae (Lp.coeFn_zero F 1 μ)]
    exact integral_zero E F

/-- Convolution commutes with postcomposition by a continuous linear map between Banach spaces:
`L ∘ (k ⋆ f) = k ⋆ (L ∘ f)`. -/
theorem compLpL_convolutionLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G] (hp : p ≠ ∞) (k : E → ℝ) (L : F →L[ℝ] G)
    (f : Lp F p μ) :
    L.compLpL p μ (convolutionLp hp k μ f) = convolutionLp hp k μ (L.compLpL p μ f) := by
  by_cases hk : Integrable k μ
  · rw [convolutionLp_apply hp hk, convolutionLp_apply hp hk,
      ← (L.compLpL p μ).integral_comp_comm (integrable_smul_translateLp hp hk f)]
    simp only [map_smul, ContinuousLinearMap.compLpL_translateLp]
  · simp only [convolutionLp_of_not_integrable hp hk, _root_.zero_apply, map_zero]

open Filter Module
open scoped Topology

/-! ### Dilations of an integrable kernel

For `ε > 0` the dilation `k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` of a kernel `k`, where `d` is the dimension of
`E`, has the same integral as `k`. The averages of a bounded function `g` continuous at `0` against
`k_ε` converge to `(∫ k) • g 0` as `ε → 0⁺` (`TauCeti.tendsto_integral_comp_inv_smul_smul`). No
sign, normalization or support condition on `k` is needed, and the kernel may be real or complex.
Applied to the translates `y ↦ f(· - y)` of an `Lᵖ` function, this is the `Lᵖ` convergence of the
dilated convolutions `k_ε ⋆ f` to `(∫ k) • f`. -/

section Dilation

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [IsScalarTower ℝ 𝕜 V]

/-- **Dilations of an integrable kernel act as an approximate identity on `Lᵖ`.** For an
integrable real or complex kernel `k`, `1 ≤ p < ∞` and `f ∈ Lᵖ(μ; V)` with `V` a Banach space,
the averages `∫ y, k_ε(y) • f(· - y) dμ(y)` of the translates of `f` against the dilations
`k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` converge to `(∫ k) • f` in `Lᵖ` as `ε → 0⁺`. -/
theorem tendsto_integral_comp_inv_smul_smul_translateLp [CompleteSpace V] (hp : p ≠ ∞)
    {k : E → 𝕜} (hk : Integrable k μ) (f : Lp V p μ) :
    Tendsto (fun ε : ℝ ↦
        ∫ y, ((ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) • μ.translateLp p (-y) f ∂μ)
      (𝓝[>] 0) (𝓝 ((∫ y, k y ∂μ) • f)) := by
  have hτ : Continuous fun y : E ↦ μ.translateLp p (-y) f :=
    (Measure.continuous_translateLp hp f).comp continuous_neg
  simpa only [neg_zero, Measure.translateLp_zero] using
    tendsto_integral_comp_inv_smul_smul hk hτ.aestronglyMeasurable
      (ae_of_all _ fun y ↦ (LinearIsometryEquiv.norm_map _ f).le) hτ.continuousAt

end Dilation

/-- **Dilations of an integrable kernel form an approximate identity for convolution.** For an
integrable real kernel `k`, `1 ≤ p < ∞` and `f ∈ Lᵖ(μ; F)` with `F` a Banach space, convolution
with the dilations `k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` converges strongly: `k_ε ⋆ f → (∫ k) • f` in `Lᵖ` as
`ε → 0⁺`. -/
theorem tendsto_convolutionLp_comp_inv_smul [CompleteSpace F] (hp : p ≠ ∞) {k : E → ℝ}
    (hk : Integrable k μ) (f : Lp F p μ) :
    Tendsto (fun ε : ℝ ↦ convolutionLp hp (fun y ↦ (ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) μ f)
      (𝓝[>] 0) (𝓝 ((∫ y, k y ∂μ) • f)) :=
  (tendsto_integral_comp_inv_smul_smul_translateLp hp hk f).congr'
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦ by
      have hkε : Integrable (fun y ↦ (ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) μ := by
        simpa only [smul_eq_mul] using (hk.comp_smul (inv_ne_zero hε.ne')).const_mul _
      exact (convolutionLp_apply hp hkε f).symm)

/-- **Young's inequality for dilated kernels.** For `ε > 0`, convolution with the dilation
`ε⁻ᵈ k(ε⁻¹ • ·)` of a real kernel `k` has operator norm at most `∫ ‖k‖`, uniformly in `ε`. -/
theorem norm_convolutionLp_comp_inv_smul_le (hp : p ≠ ∞) (k : E → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖convolutionLp (F := F) hp (fun y ↦ (ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) μ‖ ≤
      ∫ y, ‖k y‖ ∂μ := by
  refine (norm_convolutionLp_le hp _).trans_eq ?_
  simp_rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg hε.le _))]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg μ (fun y ↦ ‖k y‖) hε.le,
    smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hε.ne')]

end TauCeti
