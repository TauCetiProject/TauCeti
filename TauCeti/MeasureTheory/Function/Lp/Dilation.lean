/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.MeasureTheory.Function.Lp.Precomposition

/-!
# Dilation scaling of the `Lᵖ` seminorm

Dilating the variable of a function on a finite-dimensional real normed space `E` by `r⁻¹`, for
`r > 0`, multiplies its `Lᵖ` seminorm against an additive Haar measure by `r ^ (n / p)`, where
`n` is the dimension of `E`. Here `n / p` stands for `n / p.toReal`, which is `0` at `p = 0` and
`p = ∞` by Lean's conventions `ENNReal.toReal ∞ = 0` and `x / 0 = 0`, so at those two exponents
the factor is `1`. This is the `eLpNorm` counterpart of the lower Lebesgue integral law
`TauCeti.lintegral_comp_inv_smul`.

More generally, composing with a linear automorphism `e` multiplies the `Lᵖ` seminorm by
`|det e|^(-1 / p)`, and the `Lᵖ` seminorm on a preimage `e ⁻¹' s` by the same factor relative to
the `Lᵖ` seminorm on `s`, for any set `s`. The codomain only needs a continuous extended norm.

Normalizing the dilation by the inverse factor turns it into a linear isometric equivalence of
`Lᵖ`: `MeasureTheory.Measure.dilateLp` sends `f` to `x ↦ r ^ (-n / p) • f (r⁻¹ • x)`, and these
equivalences form an action of the multiplicative group of positive reals. Like translation
(`MeasureTheory.Measure.translateLp`), it is an isometric action on `Lᵖ` that passes to the
whole-space homogeneous Sobolev spaces, whose elements are recorded by their `Lᵖ` gradients.

## Main declarations

* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv`: `‖u ∘ e‖_p = |det e|^(-1 / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv_restrict_preimage`: the same identity for the `Lᵖ`
  seminorms on `e ⁻¹' s` and on `s`.
* `MeasureTheory.Measure.dilateLp`: the normalized dilation as a linear isometric equivalence of
  `Lᵖ`, with `MeasureTheory.Measure.coeFn_dilateLp` (its almost everywhere formula) and the action
  laws `MeasureTheory.Measure.dilateLp_one`, `MeasureTheory.Measure.dilateLp_mul` and
  `MeasureTheory.Measure.dilateLp_symm`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {G : Type*} [TopologicalSpace G] [ContinuousENorm G]

/-- **Dilation scaling of the `Lᵖ` seminorm:** `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`, where
`n` is the dimension of the ambient space. The exponent `n / p` is `n / p.toReal`, which is `0` at
`p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_inv_smul (u : E → G) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    eLpNorm (fun x => u (r⁻¹ • x)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm u p μ := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  rw [← Function.comp_def, ← (measurableEmbedding_const_smul₀ hr').eLpNorm_map_measure,
    Measure.map_addHaar_smul μ hr', eLpNorm_smul_measure_of_ne_zero (by positivity), smul_eq_mul]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le, one_div, ENNReal.toReal_inv, div_eq_mul_inv]

/-- **Linear change of variables in the `Lᵖ` seminorm on a set:** composing with a linear
automorphism `e` multiplies the `Lᵖ` seminorm on `e ⁻¹' s`, against an additive Haar measure, by
`|det e|^(-1 / p)` relative to the `Lᵖ` seminorm of the function on `s`. The set `s` need not be
measurable. -/
theorem eLpNorm_comp_continuousLinearEquiv_restrict_preimage
    (u : E → G) (e : E ≃L[ℝ] E) (p : ℝ≥0∞) {s : Set E} :
    eLpNorm (u ∘ e) p (μ.restrict (e ⁻¹' s)) =
      ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
        eLpNorm u p (μ.restrict s) := by
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : Measure.map e μ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [← he.eLpNorm_map_measure, ← he.restrict_map, hmap, Measure.restrict_smul,
    eLpNorm_smul_measure_of_ne_zero (by simpa using hdet), smul_eq_mul]

/-- **Linear change of variables in the `Lᵖ` seminorm:** composing with a linear automorphism `e`
multiplies the `Lᵖ` seminorm against an additive Haar measure by `|det e|^(-1 / p)`. The exponent
`1 / p` is `(1 / p).toReal`, which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_continuousLinearEquiv (u : E → G) (e : E ≃L[ℝ] E) (p : ℝ≥0∞) :
    eLpNorm (u ∘ e) p μ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
      eLpNorm u p μ := by
  simpa using eLpNorm_comp_continuousLinearEquiv_restrict_preimage μ u e p (s := Set.univ)

end TauCeti

namespace MeasureTheory.Measure

open Module TauCeti
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {r s : ℝ}

/-- The unnormalized dilation `f ↦ f (r⁻¹ • ·)` of `Lᵖ` classes, as a linear equivalence. -/
private noncomputable def compInvSmulLp (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hr : 0 < r) : Lp F p μ ≃ₗ[ℝ] Lp F p μ :=
  (Lp.compEquivOfMapLeSmul ℝ (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
    (map_addHaar_smul μ (inv_ne_zero hr.ne')).le (measurable_const_smul r) ENNReal.ofReal_ne_top
    (map_addHaar_smul μ hr.ne').le (fun x => smul_inv_smul₀ hr.ne' x)
    (fun x => inv_smul_smul₀ hr.ne' x)).toLinearEquiv

private theorem coeFn_compInvSmulLp (hr : 0 < r) (f : Lp F p μ) :
    ⇑(compInvSmulLp μ p hr f) =ᵐ[μ] fun x => f (r⁻¹ • x) := by
  simp only [compInvSmulLp, ContinuousLinearEquiv.coe_toLinearEquiv,
    Lp.compEquivOfMapLeSmul_apply]
  exact Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
    (map_addHaar_smul μ (inv_ne_zero hr.ne')).le f

variable (μ p) in
/-- **Dilation of `Lᵖ` classes**, normalized to be isometric: for `r > 0` it sends `f` to
`x ↦ r ^ (-n / p) • f (r⁻¹ • x)` almost everywhere (`MeasureTheory.Measure.coeFn_dilateLp`),
where `n` is the dimension of `E` and `n / p` stands for `n / p.toReal`, so that the factor is
`1` for `p = ∞`. The equivalences form an action of the positive reals
(`MeasureTheory.Measure.dilateLp_mul`), and the inverse of dilation by `r` is dilation by `r⁻¹`. -/
noncomputable def dilateLp (hr : 0 < r) : Lp F p μ ≃ₗᵢ[ℝ] Lp F p μ where
  toLinearEquiv := (compInvSmulLp μ p hr).trans
    (LinearEquiv.smulOfNeZero ℝ _ (r ^ (-((finrank ℝ E : ℝ) / p.toReal)))
      (Real.rpow_pos_of_pos hr _).ne')
  norm_map' f := by
    -- Precomposition with `r⁻¹ • ·` scales the norm by `r ^ (n / p)`, which the factor cancels.
    have hnorm : ‖compInvSmulLp μ p hr f‖ = r ^ ((finrank ℝ E : ℝ) / p.toReal) * ‖f‖ := by
      simp only [Lp.norm_def, eLpNorm_congr_ae (coeFn_compInvSmulLp hr f),
        eLpNorm_comp_inv_smul μ _ hr, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)]
    have hc : r ^ (-((finrank ℝ E : ℝ) / p.toReal)) * r ^ ((finrank ℝ E : ℝ) / p.toReal) = 1 := by
      rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, norm_smul, hnorm,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), ← mul_assoc, hc, one_mul]

private theorem dilateLp_eq_smul (hr : 0 < r) (f : Lp F p μ) :
    dilateLp μ p hr f = r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • compInvSmulLp μ p hr f :=
  (rfl)

/-- Dilation by `r` is, almost everywhere, `x ↦ r ^ (-n / p) • f (r⁻¹ • x)`. -/
theorem coeFn_dilateLp (hr : 0 < r) (f : Lp F p μ) :
    ⇑(dilateLp μ p hr f) =ᵐ[μ]
      fun x => r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • f (r⁻¹ • x) := by
  rw [dilateLp_eq_smul]
  filter_upwards [Lp.coeFn_smul (r ^ (-((finrank ℝ E : ℝ) / p.toReal))) (compInvSmulLp μ p hr f),
    coeFn_compInvSmulLp hr f] with x hx hy
  rw [hx, Pi.smul_apply, hy]

/-- The dilate of the `Lᵖ` class of `f` is almost everywhere `x ↦ r ^ (-n / p) • f (r⁻¹ • x)`. -/
theorem _root_.MeasureTheory.MemLp.coeFn_dilateLp_toLp {f : E → F} (hf : MemLp f p μ)
    (hr : 0 < r) :
    ⇑(dilateLp μ p hr (hf.toLp f)) =ᵐ[μ]
      fun x => r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • f (r⁻¹ • x) := by
  filter_upwards [coeFn_dilateLp hr (hf.toLp f),
    (quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp hf.coeFn_toLp]
    with x hx hy
  rw [hx]
  exact congrArg _ hy

/-- Dilation by `r * s` is dilation by `s` followed by dilation by `r`. -/
theorem dilateLp_mul (hr : 0 < r) (hs : 0 < s) :
    dilateLp (F := F) μ p (mul_pos hr hs) = (dilateLp μ p hs).trans (dilateLp μ p hr) := by
  refine LinearIsometryEquiv.ext fun f => Lp.ext ?_
  filter_upwards [coeFn_dilateLp (mul_pos hr hs) f, coeFn_dilateLp hr (dilateLp μ p hs f),
    (quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp (coeFn_dilateLp hs f)]
    with x hx hy hz
  simp only [Function.comp_apply] at hz
  rw [hx, LinearIsometryEquiv.trans_apply, hy, hz, smul_smul, smul_smul,
    Real.mul_rpow hr.le hs.le, mul_comm (r ^ _), mul_inv_rev]

/-- Dilation by `1` is the identity. -/
@[simp]
theorem dilateLp_one (f : Lp F p μ) : dilateLp μ p one_pos f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilateLp one_pos f] with x hx
  rw [hx, Real.one_rpow, inv_one, one_smul, one_smul]

/-- The inverse of dilation by `r` is dilation by `r⁻¹`. -/
@[simp]
theorem dilateLp_symm (hr : 0 < r) :
    (dilateLp (F := F) μ p hr).symm = dilateLp μ p (inv_pos.2 hr) :=
  LinearIsometryEquiv.ext fun f => (LinearIsometryEquiv.symm_apply_eq _).2 <| by
    have h1 : ∀ {t : ℝ} (ht : 0 < t), t = 1 → dilateLp μ p ht f = f := by
      rintro _ _ rfl
      exact dilateLp_one f
    rw [← LinearIsometryEquiv.trans_apply, ← dilateLp_mul, h1 _ (mul_inv_cancel₀ hr.ne')]

end MeasureTheory.Measure
