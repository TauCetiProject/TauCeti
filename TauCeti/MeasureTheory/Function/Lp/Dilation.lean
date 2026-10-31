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

Normalizing by the inverse factor turns dilation into a linear isometric equivalence
`f ↦ r ^ (-n / p) • f (r⁻¹ • ·)` of `Lᵖ`, and these equivalences form an action of the positive
reals. They are the `Lᵖ`-isometric dilations of scale-invariant problems such as the sharp Sobolev
inequality, where the critical `Lᵖ` norm and the `Lᵖ` norm of the gradient are both invariant.

More generally, composing with a linear automorphism `e` multiplies the `Lᵖ` seminorm by
`|det e|^(-1 / p)`, and the `Lᵖ` seminorm on a preimage `e ⁻¹' s` by the same factor relative to
the `Lᵖ` seminorm on `s`, for any set `s`. The codomain only needs a continuous extended norm.

## Main declarations

* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv`: `‖u ∘ e‖_p = |det e|^(-1 / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv_restrict_preimage`: the same identity for the `Lᵖ`
  seminorms on `e ⁻¹' s` and on `s`.
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

variable (μ p) in
/-- **The normalized dilation of `Lᵖ`** by a factor `r > 0`, as a linear isometric equivalence:
almost everywhere it sends `f` to `r ^ (-n / p) • f (r⁻¹ • ·)`, where `n` is the dimension of `E`
(`MeasureTheory.Measure.coeFn_dilateLp`), and its inverse is the dilation by `r⁻¹`
(`MeasureTheory.Measure.dilateLp_symm`). The exponent `n / p` is `n / p.toReal`, which is `0` at
`p = ∞`, where the dilation is plain precomposition. -/
noncomputable def dilateLp (r : ℝ) (hr : 0 < r) : Lp F p μ ≃ₗᵢ[ℝ] Lp F p μ :=
  let P : Lp F p μ ≃L[ℝ] Lp F p μ :=
    Lp.compEquivOfMapLeSmul ℝ (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
      (map_addHaar_smul μ (inv_ne_zero hr.ne')).le (measurable_const_smul r)
      ENNReal.ofReal_ne_top (map_addHaar_smul μ hr.ne').le
      (fun x ↦ smul_inv_smul₀ hr.ne' x) (fun x ↦ inv_smul_smul₀ hr.ne' x)
  { (P.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℝ _ _
      (Real.rpow_pos_of_pos hr (-((finrank ℝ E : ℝ) / p.toReal))).ne')) with
    norm_map' f := by
      have hae : (P f : E → F) =ᵐ[μ] fun x ↦ f (r⁻¹ • x) := by
        rw [Lp.compEquivOfMapLeSmul_apply]
        exact Lp.coeFn_compOfMapLeSmul _ _ _ f
      have hPf : ‖P f‖ = r ^ ((finrank ℝ E : ℝ) / p.toReal) * ‖f‖ := by
        rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_comp_inv_smul μ _ hr,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      simp only [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
        LinearEquiv.smulOfNeZero_apply, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _), hPf, ← mul_assoc,
        ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, one_mul] }

/-- The normalized dilation is almost everywhere `f ↦ r ^ (-n / p) • f (r⁻¹ • ·)`. -/
theorem coeFn_dilateLp (hr : 0 < r) (f : Lp F p μ) :
    ⇑(dilateLp μ p r hr f) =ᵐ[μ]
      fun x ↦ r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • f (r⁻¹ • x) := by
  -- The dilation is, by construction, the scalar multiple of the precomposition.
  have h : dilateLp μ p r hr f = r ^ (-((finrank ℝ E : ℝ) / p.toReal)) •
      Lp.compOfMapLeSmul ℝ (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
        (map_addHaar_smul μ (inv_ne_zero hr.ne')).le f := by
    simp only [dilateLp, LinearIsometryEquiv.coe_mk, LinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, Lp.compEquivOfMapLeSmul_apply,
      LinearEquiv.smulOfNeZero_apply]
  rw [h]
  filter_upwards [Lp.coeFn_smul (r ^ (-((finrank ℝ E : ℝ) / p.toReal)))
      (Lp.compOfMapLeSmul ℝ (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
        (map_addHaar_smul μ (inv_ne_zero hr.ne')).le f),
    Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
      (map_addHaar_smul μ (inv_ne_zero hr.ne')).le f] with x hx hy
  rw [hx, Pi.smul_apply, hy, Function.comp_apply]

/-- The dilation by `1` is the identity. -/
@[simp]
theorem dilateLp_one (f : Lp F p μ) : dilateLp μ p 1 one_pos f = f := by
  apply Lp.ext
  filter_upwards [coeFn_dilateLp (μ := μ) one_pos f] with x hx
  rw [hx, Real.one_rpow, one_smul, inv_one, one_smul]

/-- Dilating by `r * s` is dilating by `s` and then by `r`. -/
theorem dilateLp_mul (hr : 0 < r) (hs : 0 < s) :
    dilateLp (F := F) μ p (r * s) (mul_pos hr hs) =
      (dilateLp μ p s hs).trans (dilateLp μ p r hr) := by
  refine LinearIsometryEquiv.ext fun f ↦ Lp.ext ?_
  filter_upwards [coeFn_dilateLp (μ := μ) (mul_pos hr hs) f,
    coeFn_dilateLp (μ := μ) hr (dilateLp μ p s hs f),
    (quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp
      (coeFn_dilateLp (μ := μ) hs f)] with x hx hy hz
  simp only [Function.comp_apply] at hz
  rw [hx, LinearIsometryEquiv.trans_apply, hy, hz, smul_smul, smul_smul,
    Real.mul_rpow hr.le hs.le, mul_inv, mul_comm s⁻¹ r⁻¹]

/-- The inverse of the dilation by `r` is the dilation by `r⁻¹`. -/
theorem dilateLp_symm (hr : 0 < r) :
    (dilateLp (F := F) μ p r hr).symm = dilateLp μ p r⁻¹ (inv_pos.2 hr) := by
  refine LinearIsometryEquiv.ext fun f ↦ (dilateLp μ p r hr).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, ← LinearIsometryEquiv.trans_apply, ← dilateLp_mul]
  simp only [mul_inv_cancel₀ hr.ne', dilateLp_one]

end MeasureTheory.Measure
