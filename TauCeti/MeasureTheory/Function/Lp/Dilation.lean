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

Normalizing by the inverse factor makes dilation an isometry of `Lᵖ`: for `r > 0` and
`1 ≤ p`, the map `f ↦ r ^ (-n / p) • f (r⁻¹ • ·)` is a linear isometric equivalence of `Lᵖ`, and
these equivalences form an action of the multiplicative group of positive reals. This is the
dilation symmetry of the scale-invariant norms of analysis, such as the critical Sobolev norm.

## Main declarations

* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv`: `‖u ∘ e‖_p = |det e|^(-1 / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv_restrict_preimage`: the same identity for the `Lᵖ`
  seminorms on `e ⁻¹' s` and on `s`.
* `MeasureTheory.Measure.dilateLp`: the normalized dilation `f ↦ r ^ (-n / p) • f (r⁻¹ • ·)` as a
  linear isometric equivalence of `Lᵖ`, with `MeasureTheory.Measure.coeFn_dilateLp`.
* `MeasureTheory.Measure.dilateLp_one`, `MeasureTheory.Measure.dilateLp_mul` and
  `MeasureTheory.Measure.dilateLp_symm`: the action laws.
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

namespace MeasureTheory

open Module
open scoped ENNReal

namespace Measure

section LpDilation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {r s : ℝ}

/-- Dilating by `r⁻¹` pushes a Haar measure forward to `r ^ n` times itself. -/
private theorem map_inv_smul_le (hr : 0 < r) :
    μ.map (fun x : E => r⁻¹ • x) ≤ ENNReal.ofReal (r ^ finrank ℝ E) • μ := by
  rw [map_addHaar_smul μ (inv_ne_zero hr.ne'), inv_pow, inv_inv, abs_of_pos (by positivity)]

variable (μ p) in
/-- The normalized dilation as a continuous linear map; `MeasureTheory.Measure.dilateLp` bundles
it with its inverse. -/
private noncomputable def dilateLpL (hr : 0 < r) : Lp F p μ →L[ℝ] Lp F p μ :=
  (r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ •
    Lp.compOfMapLeSmul ℝ (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top (map_inv_smul_le hr)

private theorem coeFn_dilateLpL (hr : 0 < r) (f : Lp F p μ) :
    ⇑(dilateLpL μ p hr f) =ᵐ[μ]
      fun x => (r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ • f (r⁻¹ • x) := by
  filter_upwards [Lp.coeFn_smul (r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹
      (Lp.compOfMapLeSmul ℝ (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
        (map_inv_smul_le hr) f),
    Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) (measurable_const_smul r⁻¹) ENNReal.ofReal_ne_top
      (map_inv_smul_le hr) f] with x hx hcomp
  rw [dilateLpL, _root_.smul_apply, hx, Pi.smul_apply, hcomp, Function.comp_apply]

private theorem norm_dilateLpL (hr : 0 < r) (f : Lp F p μ) : ‖dilateLpL μ p hr f‖ = ‖f‖ := by
  have hc : ‖(r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹‖ₑ *
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) = 1 := by
    have hpos : 0 < r ^ ((finrank ℝ E : ℝ) / p.toReal) := Real.rpow_pos_of_pos hr _
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.2 hpos), ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
  have h := eLpNorm_const_smul (r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ (fun x => f (r⁻¹ • x)) p μ
  rw [TauCeti.eLpNorm_comp_inv_smul μ _ hr, ← mul_assoc, hc, one_mul] at h
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_dilateLpL hr f)]
  exact congrArg ENNReal.toReal h

/-- Dilating by `s` and then by `r` is dilating by `r * s`. -/
private theorem dilateLpL_dilateLpL (hr : 0 < r) (hs : 0 < s) (f : Lp F p μ) :
    dilateLpL μ p hr (dilateLpL μ p hs f) = dilateLpL μ p (mul_pos hr hs) f := by
  apply Lp.ext
  filter_upwards [coeFn_dilateLpL hr (dilateLpL μ p hs f),
    (quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp (coeFn_dilateLpL hs f),
    coeFn_dilateLpL (mul_pos hr hs) f] with x hx hcomp hrs
  simp only [Function.comp_apply] at hcomp
  rw [hx, hrs, hcomp, smul_smul,
    Real.mul_rpow hr.le hs.le, mul_inv, mul_inv, smul_smul, mul_comm s⁻¹]

private theorem dilateLpL_one (f : Lp F p μ) : dilateLpL μ p one_pos f = f := by
  apply Lp.ext
  filter_upwards [coeFn_dilateLpL one_pos f] with x hx
  rw [hx, Real.one_rpow, inv_one, one_smul, one_smul]

variable (μ p) in
/-- **Dilation on `Lᵖ`**, normalized to be isometric: for `r > 0` it sends `f` to
`x ↦ r ^ (-n / p) • f (r⁻¹ • x)`, where `n` is the dimension of `E`, as a linear isometric
equivalence. It spreads `f` out by the factor `r`, and its inverse is dilation by `r⁻¹`. The
exponent `n / p` is `n / p.toReal`, which is `0` at `p = ∞`, where no normalization is needed.
Negative ratios are not included: they compose a positive dilation with the measure-preserving
reflection `x ↦ -x`. -/
noncomputable def dilateLp (hr : 0 < r) : Lp F p μ ≃ₗᵢ[ℝ] Lp F p μ where
  toLinearEquiv := LinearEquiv.ofLinearMap (dilateLpL μ p hr).toLinearMap
    (dilateLpL μ p (inv_pos.2 hr)).toLinearMap
    (LinearMap.ext fun f => by
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
        dilateLpL_dilateLpL, mul_inv_cancel₀ hr.ne', dilateLpL_one, LinearMap.id_coe, id_eq])
    (LinearMap.ext fun f => by
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
        dilateLpL_dilateLpL, inv_mul_cancel₀ hr.ne', dilateLpL_one, LinearMap.id_coe, id_eq])
  norm_map' := norm_dilateLpL hr

/-- Dilation by `r` is almost everywhere `x ↦ r ^ (-n / p) • f (r⁻¹ • x)`. -/
theorem coeFn_dilateLp (hr : 0 < r) (f : Lp F p μ) :
    ⇑(μ.dilateLp p hr f) =ᵐ[μ]
      fun x => (r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ • f (r⁻¹ • x) :=
  coeFn_dilateLpL hr f

/-- Dilation by `1` is the identity on `Lᵖ`. -/
@[simp]
theorem dilateLp_one (f : Lp F p μ) : μ.dilateLp p one_pos f = f :=
  dilateLpL_one f

/-- Dilating by `r * s` is dilating by `s` and then by `r`, so the dilations form an action of
the multiplicative group of positive reals. -/
theorem dilateLp_mul (hr : 0 < r) (hs : 0 < s) :
    μ.dilateLp (F := F) p (mul_pos hr hs) = (μ.dilateLp p hs).trans (μ.dilateLp p hr) :=
  LinearIsometryEquiv.ext fun f => (dilateLpL_dilateLpL hr hs f).symm

/-- The inverse of dilation by `r` is dilation by `r⁻¹`. -/
@[simp]
theorem dilateLp_symm (hr : 0 < r) :
    (μ.dilateLp (F := F) p hr).symm = μ.dilateLp p (inv_pos.2 hr) :=
  LinearIsometryEquiv.ext fun _ => rfl

end LpDilation

end Measure

namespace MemLp

/-- The dilate by `r` of the `Lᵖ` class of `f` is almost everywhere
`x ↦ r ^ (-n / p) • f (r⁻¹ • x)`. -/
theorem coeFn_dilateLp_toLp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
    [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {r : ℝ} {f : E → F} (hf : MemLp f p μ) (hr : 0 < r) :
    ⇑(μ.dilateLp p hr (hf.toLp f)) =ᵐ[μ]
      fun x => (r ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ • f (r⁻¹ • x) := by
  filter_upwards [Measure.coeFn_dilateLp hr (hf.toLp f),
    (Measure.quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp hf.coeFn_toLp]
    with x hx hcomp
  simp only [Function.comp_apply] at hcomp
  rw [hx, hcomp]

end MemLp

end MeasureTheory
