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
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Convolution with an integrable kernel as an operator on `Lᵖ`

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

## Main declarations

* `TauCeti.convolutionLp`: convolution with a real kernel as a continuous linear operator on
  `Lᵖ`; it is zero when the kernel is not integrable.
* `TauCeti.convolutionLp_apply`: the defining `Lᵖ`-valued Bochner integral.
* `TauCeti.norm_convolutionLp_le`: Young's inequality `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`.
* `TauCeti.convolutionLp_convolution`: `(k₁ ⋆ k₂) ⋆ f = k₁ ⋆ (k₂ ⋆ f)`.
* `TauCeti.convolutionLp_ae_eq_convolution`: the operator is represented almost everywhere by the
  classical pointwise convolution `(k ⋆ f)(x) = ∫ y, k(y) • f(x - y) dμ(y)`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Section 8.2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.15.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap MeasureTheory
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
          neg_add]

/-- On a set `s` of finite measure, the convolution integrand `(x, y) ↦ k(y) • f(x - y)` of an
integrable kernel `k` and an `Lᵖ` function `f` is integrable: `∫_s ‖f(x - y)‖ dx` is bounded
uniformly in `y`, by the `Lᵖ` norm of `f`. -/
private theorem integrable_convolution_integrand_restrict [CompleteSpace F] {k : E → ℝ}
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

end TauCeti
