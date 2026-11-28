/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Sobolev.W1p.Density
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Ladyzhenskaya's inequality in dimension two

Let `E` be a two-dimensional real inner product space with its volume measure. Ladyzhenskaya's
inequality bounds the `L⁴` norm of a function on `E` by its `L²` norm and the `L²` norm of its
derivative,

`‖u‖₄² ≤ ‖u‖₂ ‖∇u‖₂`, that is, `∫ ‖u‖⁴ ≤ (∫ ‖u‖²) (∫ ‖∇u‖²)`.

This is the two-dimensional Gagliardo–Nirenberg inequality with the exponent `θ = 1 / 2` forced by
scaling. It is the estimate that controls the convective term of the two-dimensional
Navier–Stokes equations in the energy space. Here `‖∇u x‖` is the operator norm of
`fderiv ℝ u x`, which is at most its Hilbert–Schmidt norm; with the Hilbert–Schmidt norm the
classical statement carries the constant `2`, which the inequality above improves.

## Main results

* `OrthonormalBasis.lintegral_eNorm_pow_four_le`: the product form
  `∫ ‖u‖⁴ ≤ (∫ ‖u‖ ‖∂₁u‖) (∫ ‖u‖ ‖∂₂u‖)` for the partial derivatives along an orthonormal
  basis, for a compactly supported `C¹` map `u` with values in a real inner product space.
* `TauCeti.eLpNorm_four_sq_le_of_finrank_eq_two` and
  `TauCeti.integral_norm_pow_four_le_of_finrank_eq_two`: Ladyzhenskaya's inequality for compactly
  supported `C¹` maps, in `eLpNorm` and in integral form.
* `TauCeti.W1p.eLpNorm_value_four_sq_le_of_finrank_eq_two` and
  `TauCeti.W1p.memLp_value_four_of_finrank_eq_two`: the inequality on `W^{1,2}(E)`, so
  `W^{1,2}(E)` embeds in `L⁴(E)`.

## Proof

By the one-dimensional bound `‖v s‖² ≤ ∫ ‖v‖ ‖v'‖`
(`HasCompactSupport.eNorm_sq_le_lintegral_eNorm_mul_eNorm_deriv`), applied on the horizontal and
the vertical line through a point of the coordinate plane, `‖u (s, t)‖² ≤ A t` and
`‖u (s, t)‖² ≤ B s`, where `A t` and `B s` integrate `‖u‖ ‖∂₁u‖` and `‖u‖ ‖∂₂u‖` along these
lines. Multiplying and integrating by Tonelli's theorem gives the product form, which transfers to
`E` through an orthonormal basis. Hölder's inequality `∫ ‖u‖ ‖∇u‖ ≤ ‖u‖₂ ‖∇u‖₂`
(`TauCeti.lintegral_enorm_mul_enorm_le`) bounds each factor. On `W^{1,2}(E)` the inequality
follows from the density of test functions and Fatou's lemma along an almost everywhere convergent
subsequence.

## References

* O. A. Ladyzhenskaya, *The Mathematical Theory of Viscous Incompressible Flow*, 2nd ed.,
  Gordon and Breach, 1969, Chapter 1, §1.
-/

public section

open MeasureTheory Set Filter Topology Module TopologicalSpace
open scoped ENNReal Distributions

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Ladyzhenskaya's inequality on the coordinate plane `ℝ × ℝ`, in product form. -/
private theorem lintegral_eNorm_pow_four_le_prod {w : ℝ × ℝ → F} (hc : HasCompactSupport w)
    (hw : ContDiff ℝ 1 w) :
    ∫⁻ p, ‖w p‖ₑ ^ 4 ≤ (∫⁻ p, ‖w p‖ₑ * ‖fderiv ℝ w p (1, 0)‖ₑ) *
      ∫⁻ p, ‖w p‖ₑ * ‖fderiv ℝ w p (0, 1)‖ₑ := by
  have hdiff := hw.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  set f : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ‖w p‖ₑ * ‖fderiv ℝ w p (1, 0)‖ₑ with hf_def
  set g : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ‖w p‖ₑ * ‖fderiv ℝ w p (0, 1)‖ₑ with hg_def
  have hw' : Measurable fun p ↦ ‖w p‖ₑ := (continuous_eNorm.comp hw.continuous).measurable
  have hf : Measurable f :=
    hw'.mul (continuous_eNorm.comp (hcont.clm_apply continuous_const)).measurable
  have hg : Measurable g :=
    hw'.mul (continuous_eNorm.comp (hcont.clm_apply continuous_const)).measurable
  -- Bound `‖w‖²` by the integrals along the horizontal and the vertical line through a point.
  have hA (s t : ℝ) : ‖w (s, t)‖ₑ ^ 2 ≤ ∫⁻ r, f (r, t) := by
    have hcs : HasCompactSupport fun r ↦ w (r, t) :=
      HasCompactSupport.intro (hc.image continuous_fst) fun r hr ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hr ⟨_, h, rfl⟩
    have hder (r : ℝ) : deriv (fun r ↦ w (r, t)) r = fderiv ℝ w (r, t) (1, 0) :=
      ((hdiff (r, t)).hasFDerivAt.comp_hasDerivAt r
        (HasDerivAt.prodMk (hasDerivAt_id r) (hasDerivAt_const r t))).deriv
    simpa only [hf_def, hder] using hcs.eNorm_sq_le_lintegral_eNorm_mul_eNorm_deriv
      (hw.comp (contDiff_id.prodMk contDiff_const)) s
  have hB (s t : ℝ) : ‖w (s, t)‖ₑ ^ 2 ≤ ∫⁻ r, g (s, r) := by
    have hcs : HasCompactSupport fun r ↦ w (s, r) :=
      HasCompactSupport.intro (hc.image continuous_snd) fun r hr ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hr ⟨_, h, rfl⟩
    have hder (r : ℝ) : deriv (fun r ↦ w (s, r)) r = fderiv ℝ w (s, r) (0, 1) :=
      ((hdiff (s, r)).hasFDerivAt.comp_hasDerivAt r
        (HasDerivAt.prodMk (hasDerivAt_const r s) (hasDerivAt_id r))).deriv
    simpa only [hg_def, hder] using hcs.eNorm_sq_le_lintegral_eNorm_mul_eNorm_deriv
      (hw.comp (contDiff_const.prodMk contDiff_id)) t
  calc ∫⁻ p, ‖w p‖ₑ ^ 4 ≤ ∫⁻ p, (∫⁻ r, g (p.1, r)) * ∫⁻ r, f (r, p.2) :=
        lintegral_mono fun p ↦ by
          rw [show 4 = 2 + 2 by norm_num, pow_add]
          exact mul_le_mul' (hB p.1 p.2) (hA p.1 p.2)
    _ = (∫⁻ s, ∫⁻ r, g (s, r)) * ∫⁻ t, ∫⁻ r, f (r, t) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hg.lintegral_prod_right'.aemeasurable
          hf.lintegral_prod_left'.aemeasurable
    _ = (∫⁻ p, f p) * ∫⁻ p, g p := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
          lintegral_prod_symm _ hf.aemeasurable, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Ladyzhenskaya's inequality in product form.** For an orthonormal basis `b` of a
two-dimensional real inner product space and a compactly supported `C¹` map `u`,
`∫ ‖u‖⁴ ≤ (∫ ‖u‖ ‖∂_{b 0} u‖) (∫ ‖u‖ ‖∂_{b 1} u‖)`. -/
theorem _root_.OrthonormalBasis.lintegral_eNorm_pow_four_le (b : OrthonormalBasis (Fin 2) ℝ E)
    {u : E → F} (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) :
    ∫⁻ x, ‖u x‖ₑ ^ 4 ≤ (∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ u x (b 0)‖ₑ) *
      ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ u x (b 1)‖ₑ := by
  -- Transport to the coordinate plane by `(s, t) ↦ s • b 0 + t • b 1`, which preserves volume.
  let e : (ℝ × ℝ) ≃L[ℝ] E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 2 ↦ ℝ).symm.trans
      b.repr.symm.toContinuousLinearEquiv)
  have he : MeasurePreserving e volume volume := by
    convert (b.measurePreserving_repr_symm.comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 2)).symm).comp
      (volume_preserving_finTwoArrow ℝ).symm
    funext p
    simp [e]
  have he0 : e (1, 0) = b 0 := by
    simp [e, ← b.sum_repr_symm]
  have he1 : e (0, 1) = b 1 := by
    simp [e, ← b.sum_repr_symm]
  have hcu : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hfd (p v : ℝ × ℝ) : fderiv ℝ (u ∘ e) p v = fderiv ℝ u (e p) (e v) := by
    rw [fderiv_comp p ((hu.differentiable one_ne_zero) _) e.differentiableAt, e.fderiv]
    simp
  have key := lintegral_eNorm_pow_four_le_prod (hc.comp_homeomorph e.toHomeomorph)
    (hu.comp e.contDiff)
  simp only [hfd, he0, he1, Function.comp_apply, ContinuousLinearEquiv.coe_toHomeomorph] at key
  have hu' : Measurable fun x ↦ ‖u x‖ₑ := (continuous_eNorm.comp hu.continuous).measurable
  rwa [he.lintegral_comp (hu'.pow_const 4),
    he.lintegral_comp (f := fun x ↦ ‖u x‖ₑ * ‖fderiv ℝ u x (b 0)‖ₑ)
      (hu'.mul (continuous_eNorm.comp (hcu.clm_apply continuous_const)).measurable),
    he.lintegral_comp (f := fun x ↦ ‖u x‖ₑ * ‖fderiv ℝ u x (b 1)‖ₑ)
      (hu'.mul (continuous_eNorm.comp (hcu.clm_apply continuous_const)).measurable)] at key

/-- **Ladyzhenskaya's inequality.** On a two-dimensional real inner product space, a compactly
supported `C¹` map `u` with values in a real inner product space satisfies
`‖u‖₄² ≤ ‖u‖₂ ‖∇u‖₂`, where `∇u = fderiv ℝ u` carries the operator norm. -/
theorem eLpNorm_four_sq_le_of_finrank_eq_two (hE : finrank ℝ E = 2) {u : E → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) :
    eLpNorm u 4 volume ^ 2 ≤ eLpNorm u 2 volume * eLpNorm (fderiv ℝ u) 2 volume := by
  let b : OrthonormalBasis (Fin 2) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hE)
  have hfac (i : Fin 2) :
      ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ u x (b i)‖ₑ ≤ ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ u x‖ₑ :=
    lintegral_mono fun x ↦ by
      gcongr
      simpa [b.norm_eq_one] using (fderiv ℝ u x).le_opENorm (b i)
  have h4 : eLpNorm u 4 volume ^ 4 = ∫⁻ x, ‖u x‖ₑ ^ 4 := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 4) (by norm_num)
      hu.continuous.aestronglyMeasurable
  have hholder : ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ u x‖ₑ ≤
      eLpNorm u 2 volume * eLpNorm (fderiv ℝ u) 2 volume :=
    lintegral_enorm_mul_enorm_le hu.continuous.aestronglyMeasurable
      (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, ← pow_mul, h4, sq]
  exact (b.lintegral_eNorm_pow_four_le hc hu).trans
    (mul_le_mul' ((hfac 0).trans hholder) ((hfac 1).trans hholder))

/-- **Ladyzhenskaya's inequality**, integral form: on a two-dimensional real inner product space,
a compactly supported `C¹` map `u` with values in a real inner product space satisfies
`∫ ‖u‖⁴ ≤ (∫ ‖u‖²) (∫ ‖∇u‖²)`. -/
theorem integral_norm_pow_four_le_of_finrank_eq_two (hE : finrank ℝ E = 2) {u : E → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) :
    ∫ x, ‖u x‖ ^ 4 ≤ (∫ x, ‖u x‖ ^ 2) * ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
  have hu_m := hu.continuous.aestronglyMeasurable (μ := volume)
  have hDu := hu.continuous_fderiv one_ne_zero
  have h4 := lpNorm_natCast_pow_eq_integral_norm_pow hu_m four_ne_zero
  have h2 := lpNorm_natCast_pow_eq_integral_norm_pow hu_m two_ne_zero
  have h2' := lpNorm_natCast_pow_eq_integral_norm_pow (μ := volume) hDu.aestronglyMeasurable
    two_ne_zero
  simp only [Nat.cast_ofNat] at h4 h2 h2'
  rw [← h4, ← h2, ← h2', ← toReal_eLpNorm, ← toReal_eLpNorm, ← toReal_eLpNorm,
    ← ENNReal.toReal_pow, ← ENNReal.toReal_pow, ← ENNReal.toReal_pow, ← ENNReal.toReal_mul,
    ← mul_pow, show 4 = 2 * 2 by norm_num, pow_mul]
  refine ENNReal.toReal_mono (ENNReal.pow_ne_top (ENNReal.mul_ne_top ?_ ?_)) ?_
  · exact (hu.continuous.memLp_of_hasCompactSupport hc).eLpNorm_ne_top
  · exact (hDu.memLp_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ))).eLpNorm_ne_top
  · gcongr
    exact eLpNorm_four_sq_le_of_finrank_eq_two hE hc hu

/-- Ladyzhenskaya's inequality for a test function embedded in `W^{1,2}(E)`. -/
private theorem eLpNorm_value_ofTestFunctionₗ_four_sq_le (hE : finrank ℝ E = 2)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    eLpNorm (W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)) 4 volume ^ 2 ≤
      eLpNorm (W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)) 2 volume *
        eLpNorm (W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ)) 2 volume := by
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := (volume : Measure E)) (p := 2) φ
  have hg := W1p.gradient_ofTestFunctionₗ_top_ae (mu := (volume : Measure E)) (p := 2) φ
  have hφ1 : ContDiff ℝ 1 φ := φ.contDiff.of_le (by simp)
  have hD := hφ1.continuous_fderiv one_ne_zero
  rw [eLpNorm_congr_ae hv, eLpNorm_congr_ae hv, eLpNorm_congr_ae hg,
    eLpNorm_congr_norm_ae ((W1p.memLp_gradient _).aestronglyMeasurable.congr hg)
      hD.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
        rw [← toDual_gradient, LinearIsometryEquiv.norm_map])]
  exact eLpNorm_four_sq_le_of_finrank_eq_two hE φ.hasCompactSupport hφ1

/-- **Ladyzhenskaya's inequality on `W^{1,2}(E)`.** On a two-dimensional real inner product
space, every `u ∈ W^{1,2}(E)` satisfies `‖u‖₄² ≤ ‖u‖₂ ‖∇u‖₂`. -/
theorem W1p.eLpNorm_value_four_sq_le_of_finrank_eq_two (hE : finrank ℝ E = 2)
    (u : W1p (volume : Measure E) ⊤ 2) :
    eLpNorm (W1p.value u) 4 volume ^ 2 ≤
      eLpNorm (W1p.value u) 2 volume * eLpNorm (W1p.gradient u) 2 volume := by
  -- Approximate `u` in `W^{1,2}` by test functions `φ n`.
  obtain ⟨U, hU, hlim⟩ := mem_closure_iff_seq_limit.1
    (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure E)) (p := 2)
      ENNReal.ofNat_ne_top u)
  have happrox (n : ℕ) : eLpNorm (W1p.value (U n)) 4 volume ^ 2 ≤
      eLpNorm (W1p.value (U n)) 2 volume * eLpNorm (W1p.gradient (U n)) 2 volume := by
    obtain ⟨φ, hφ⟩ := hU n
    exact hφ ▸ eLpNorm_value_ofTestFunctionₗ_four_sq_le hE φ
  have hval : Tendsto (fun n ↦ W1p.value (U n)) atTop (𝓝 (W1p.value u)) :=
    by simpa only [Function.comp_def, W1p.valueL_apply] using
      (W1p.valueL.continuous.tendsto u).comp hlim
  have hgrad : Tendsto (fun n ↦ W1p.gradient (U n)) atTop (𝓝 (W1p.gradient u)) :=
    by simpa only [Function.comp_def, W1p.gradientL_apply] using
      (W1p.gradientL.continuous.tendsto u).comp hlim
  -- The right-hand sides converge.
  have hc : Tendsto (fun n ↦ eLpNorm (W1p.value (U n)) 2 volume *
      eLpNorm (W1p.gradient (U n)) 2 volume) atTop
      (𝓝 (eLpNorm (W1p.value u) 2 volume * eLpNorm (W1p.gradient u) 2 volume)) := by
    have h1 := (continuous_eNorm.tendsto _).comp hval
    have h2 := (continuous_eNorm.tendsto _).comp hgrad
    simp only [Function.comp_def, Lp.eNorm_def, Opens.coe_top, Measure.restrict_univ] at h1 h2
    exact ENNReal.Tendsto.mul h1 (Or.inr (W1p.memLp_gradient u).eLpNorm_ne_top) h2
      (Or.inr (W1p.memLp_value u).eLpNorm_ne_top)
  -- The left-hand side is lower semicontinuous along an almost everywhere convergent subsequence.
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  simp only [Opens.coe_top, Measure.restrict_univ] at hae
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 4)
    (fun n ↦ (W1p.memLp_value (U (ns n))).aestronglyMeasurable) _
    (W1p.memLp_value u).aestronglyMeasurable hae
  calc eLpNorm (W1p.value u) 4 volume ^ 2
      ≤ (liminf (fun n ↦ eLpNorm (W1p.value (U (ns n))) 4 volume) atTop) ^ 2 := by gcongr
    _ = liminf (fun n ↦ eLpNorm (W1p.value (U (ns n))) 4 volume ^ 2) atTop :=
      (pow_left_mono 2).map_liminf_of_continuousAt _ (ENNReal.continuous_pow 2).continuousAt
    _ ≤ liminf (fun n ↦ eLpNorm (W1p.value (U (ns n))) 2 volume *
          eLpNorm (W1p.gradient (U (ns n))) 2 volume) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n ↦ happrox (ns n))
    _ = _ := (hc.comp hns.tendsto_atTop).liminf_eq

/-- On a two-dimensional real inner product space, `W^{1,2}(E)` embeds in `L⁴(E)`. -/
theorem W1p.memLp_value_four_of_finrank_eq_two (hE : finrank ℝ E = 2)
    (u : W1p (volume : Measure E) ⊤ 2) : MemLp (W1p.value u) 4 volume := by
  have h := (W1p.eLpNorm_value_four_sq_le_of_finrank_eq_two hE u).trans_lt (ENNReal.mul_lt_top
    (W1p.memLp_value u).eLpNorm_lt_top (W1p.memLp_gradient u).eLpNorm_lt_top)
  exact memLp_iff.2 ((ENNReal.pow_lt_top_iff.1 h).resolve_right two_ne_zero)

end TauCeti
