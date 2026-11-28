/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Exchange
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Recentring the output end of the pair of pants

Some perturbation data on the pair of pants `S = ℂ ∖ {0, 1}` have their output end recentred at a
point `c ∈ [0, 1]`: far out on that end they are `H_∞(t) dt` in the end coordinate
`w = c + φ_∞(s + i t)`, centred at `c` rather than at `0`. The members of the input-exchange
family (`TauCeti.Floer.exchangePerturbation`) and of the input-exchange family capped at `0`
(`TauCeti.Floer.cappedExchangePerturbation`) are such data. The energy identity for data which are
cylindrical in the standard end coordinates of `S` does not apply to them directly. This file
transports it along the diffeomorphism `Φ_c(s, t) = (s + c (1 - μ(|w|)), t)` of the plane, for
`w = s + i t` and a smooth radial cutoff `μ` equal to `1` for `|w| ≤ 3` and to `0` for `|w| ≥ 8`,
with slope at most `1/4` (`TauCeti.Floer.exchangeMap`).

* `Φ_c` is the identity near the inputs `0`, `1` and the translation by `c` near the output end
  (`TauCeti.Floer.exchangeMap_of_norm_le`, `TauCeti.Floer.exchangeMap_of_le_norm`), in
  particular near every point beyond the height `1` of the output end
  (`TauCeti.Floer.exchangeMap_eventuallyEq_add_of_one_lt`). It keeps
  the `t` coordinate and, for `c ≥ 0`, moves `s` by an amount between `0` and `c`
  (`TauCeti.Floer.snd_exchangeMap`, `TauCeti.Floer.le_fst_exchangeMap`,
  `TauCeti.Floer.fst_exchangeMap_le`). It is `C²` (`TauCeti.Floer.contDiff_exchangeMap`), and
  for `|c| ≤ 1` the slope bound makes it
  bijective with nonnegative Jacobian (`TauCeti.Floer.injective_exchangeMap`,
  `TauCeti.Floer.surjective_exchangeMap`, `TauCeti.Floer.det_fderiv_exchangeMap_nonneg`). For
  `0 ≤ c ≤ 1` it maps `S` onto itself
  (`TauCeti.Floer.image_exchangeMap_thricePuncturedSphereReal`) and the truncation `S_R` onto the
  truncation with recentred output end
  (`TauCeti.Floer.image_exchangeMap_truncation`); it fixes the circles `s = R` of the input ends and
  translates the circles `s = -R` of the output end by `c`
  (`TauCeti.Floer.exchangeMap_cylindricalEndLift`,
  `TauCeti.Floer.exchangeMap_cylindricalEndLift_inf`).
* Let `K₁` and `K₀` be data with `K₁ = K₀` on the disc `|w| ≤ 3`, with `K₁` vanishing on the
  annulus `2 ≤ |w - c| ≤ 10` and `K₀` on the annulus `2 ≤ |w| ≤ 10`, and with `K₁(w + c) = K₀(w)`
  for `|w| ≥ 3/2`. Then the pullback of `K₁` along `Φ_c` is `K₀`
  (`TauCeti.Floer.perturbationPullback_exchangeMap_of_eq`).
* For such data which are `C¹` over `S`, and a map `u` into a manifold with a two-form, the energy
  density, the symplectic area density and the curvature are two-forms on the domain
  (`TauCeti.Geometry.Symplectic.Floer.Pullback`). So the energy, area and integrated curvature of
  `u` for `K₁` over the image under `Φ_c` of a measurable part `s` of `S` are those of `u ∘ Φ_c`
  for `K₀` over `s` (`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image_exchangeMap`,
  `TauCeti.SmoothTwoForm.integral_area_image_exchangeMap`,
  `TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_image_exchangeMap`), and integrability
  transfers along `Φ_c` (`TauCeti.Floer.integrableOn_image_exchangeMap_iff`,
  `TauCeti.Floer.integrableOn_of_integrableOn_image_exchangeMap`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_comp_exchangeMap`,
  `TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_image_exchangeMap`).

The diffeomorphism is not holomorphic, so `u ∘ Φ_c` need not solve a Floer equation; only the
energy identity, which holds for every map, is transported.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product and its energy
  estimate.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold

namespace TauCeti

namespace Floer

/-! ### A diffeomorphism moving the output end -/

section Cutoff

open scoped ContDiff

/-- A smooth radial cutoff: `1` on `(-∞, 3]`, `0` on `[8, ∞)`, antitone, with slope at most
`1/4`. -/
private theorem exists_exchangeCutoff :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ Antitone μ ∧ (∀ r, 0 ≤ μ r) ∧ (∀ r, 8 ≤ r → μ r = 0) ∧
      (∀ r ≤ 3, μ r = 1) ∧ (∀ r, |deriv μ r| ≤ 1 / 4) ∧ ∀ r ∉ Ioo 3 8, deriv μ r = 0 :=
  exists_contDiff_antitone_cutoff_abs_deriv_le (by norm_num) zero_le_one (by norm_num)

/-- The radial cutoff of the map `Φ_c`. -/
private noncomputable def exchangeCutoff : ℝ → ℝ :=
  exists_exchangeCutoff.choose

private theorem contDiff_exchangeCutoff : ContDiff ℝ 2 exchangeCutoff :=
  exists_exchangeCutoff.choose_spec.1.of_le (by simp)

end Cutoff

private theorem exchangeCutoff_of_le {r : ℝ} (hr : r ≤ 3) : exchangeCutoff r = 1 :=
  exists_exchangeCutoff.choose_spec.2.2.2.2.1 r hr

private theorem exchangeCutoff_of_ge {r : ℝ} (hr : 8 ≤ r) : exchangeCutoff r = 0 :=
  exists_exchangeCutoff.choose_spec.2.2.2.1 r hr

private theorem exchangeCutoff_nonneg (r : ℝ) : 0 ≤ exchangeCutoff r :=
  exists_exchangeCutoff.choose_spec.2.2.1 r

private theorem exchangeCutoff_le_one (r : ℝ) : exchangeCutoff r ≤ 1 := by
  rcases le_total r 3 with hr | hr
  · exact (exchangeCutoff_of_le hr).le
  · exact (exists_exchangeCutoff.choose_spec.2.1 hr).trans (exchangeCutoff_of_le le_rfl).le

private theorem lipschitzWith_exchangeCutoff : LipschitzWith (1 / 4) exchangeCutoff := by
  refine lipschitzWith_of_nnNorm_deriv_le (contDiff_exchangeCutoff.differentiable two_ne_zero)
    fun r ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs]
  exact (exists_exchangeCutoff.choose_spec.2.2.2.2.2.1 r).trans_eq (by simp)

/-- The horizontal displacement `c (1 - μ(|w|))` of `Φ_c` at `w = s + i t`. -/
private noncomputable def exchangeShift (c : ℝ) (y : ℝ × ℝ) : ℝ :=
  c * (1 - exchangeCutoff ‖Complex.equivRealProdCLM.symm y‖)

/-- The `C²` map `Φ_c(s, t) = (s + c (1 - μ(|w|)), t)` of the plane, for `w = s + i t` and a
smooth radial cutoff `μ` equal to `1` for `|w| ≤ 3` and to `0` for `|w| ≥ 8`, with slope at most
`1/4`. It is the identity near the inputs `0`, `1` and the translation by `c` near the output end,
it is a diffeomorphism of the plane for `|c| ≤ 1`, and it carries the pair-of-pants datum to the
member `c` of the input-exchange family. -/
noncomputable def exchangeMap (c : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (y.1 + exchangeShift c y, y.2)

variable {c : ℝ} {y : ℝ × ℝ}

private theorem exchangeShift_of_norm_le (hy : ‖Complex.equivRealProdCLM.symm y‖ ≤ 3) :
    exchangeShift c y = 0 := by
  simp [exchangeShift, exchangeCutoff_of_le hy]

private theorem exchangeShift_of_le_norm (hy : 8 ≤ ‖Complex.equivRealProdCLM.symm y‖) :
    exchangeShift c y = c := by
  simp [exchangeShift, exchangeCutoff_of_ge hy]

private theorem exchangeShift_nonneg (hc : 0 ≤ c) (y : ℝ × ℝ) : 0 ≤ exchangeShift c y :=
  mul_nonneg hc (sub_nonneg.2 (exchangeCutoff_le_one _))

private theorem exchangeShift_le (hc : 0 ≤ c) (y : ℝ × ℝ) : exchangeShift c y ≤ c :=
  mul_le_of_le_one_right hc (sub_le_self _ (exchangeCutoff_nonneg _))

private theorem equivRealProdCLM_symm_exchangeMap (c : ℝ) (y : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (exchangeMap c y) =
      Complex.equivRealProdCLM.symm y + exchangeShift c y := by
  simp only [exchangeMap, Complex.equivRealProdCLM_symm_apply]
  push_cast
  ring

private theorem contDiff_exchangeShift (c : ℝ) : ContDiff ℝ 2 (exchangeShift c) := by
  refine contDiff_const.mul (contDiff_const.sub (contDiff_iff_contDiffAt.2 fun y ↦ ?_))
  set e := Complex.equivRealProdCLM.symm
  by_cases hy : ‖e y‖ < 3
  · -- Near the disc `|w| < 3` the cutoff is constant.
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt (continuous_norm.comp e.continuous) continuous_const).mem_nhds hy]
      with y' hy' using exchangeCutoff_of_le (le_of_lt hy')
  · have hne : e y ≠ 0 := fun h ↦ hy (by simp [h])
    exact contDiff_exchangeCutoff.contDiffAt.comp y
      ((contDiffAt_norm ℝ hne).comp y e.contDiff.contDiffAt)

/-- The map `Φ_c` is `C²`. -/
theorem contDiff_exchangeMap (c : ℝ) : ContDiff ℝ 2 (exchangeMap c) :=
  (contDiff_fst.add (contDiff_exchangeShift c)).prodMk contDiff_snd

/-- For `|c| ≤ 1` the displacement is `1/2`-Lipschitz, since the cutoff has slope at most `1/4`
and `|w| ≤ |s| + |t| ≤ 2 ‖(s, t)‖`. -/
private theorem lipschitzWith_exchangeShift (hc : |c| ≤ 1) :
    LipschitzWith (1 / 2) (exchangeShift c) := by
  refine LipschitzWith.of_dist_le_mul fun y y' ↦ ?_
  set e := Complex.equivRealProdCLM.symm
  have hμ := lipschitzWith_exchangeCutoff.dist_le_mul ‖e y‖ ‖e y'‖
  have hn : dist ‖e y‖ ‖e y'‖ ≤ 2 * dist y y' := by
    rw [Real.dist_eq, dist_eq_norm]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← map_sub]
    -- `|s + i t| ≤ |s| + |t| ≤ 2 ‖(s, t)‖` for the sup norm on `ℝ × ℝ`.
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h₁ := norm_fst_le (y - y')
    have h₂ := norm_snd_le (y - y')
    rw [Real.norm_eq_abs] at h₁ h₂
    simp only [e, Complex.equivRealProdCLM_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im]
    linarith
  rw [Real.dist_eq, exchangeShift, exchangeShift, ← mul_sub, abs_mul, sub_sub_sub_cancel_left,
    ← Real.dist_eq, dist_comm]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hμ ⊢
  calc |c| * dist (exchangeCutoff ‖e y‖) (exchangeCutoff ‖e y'‖)
      ≤ 1 * (1 / 4 * (2 * dist y y')) :=
        mul_le_mul hc (hμ.trans (by gcongr)) dist_nonneg zero_le_one
    _ = 1 / 2 * dist y y' := by ring

/-- For `|c| ≤ 1` the diffeomorphism `Φ_c` differs from the identity by a `1/2`-Lipschitz map. -/
private theorem approximatesLinearOn_exchangeMap (hc : |c| ≤ 1) :
    ApproximatesLinearOn (exchangeMap c)
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) univ
      (1 / 2) := by
  refine LipschitzOnWith.approximatesLinearOn (LipschitzWith.lipschitzOnWith ?_)
  have h : exchangeMap c - ⇑(ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ) =
      fun y ↦ (exchangeShift c y, 0) := by
    ext y <;> simp [exchangeMap]
  rw [h]
  simpa using (lipschitzWith_exchangeShift hc).prodMk (LipschitzWith.const (0 : ℝ))

private theorem one_half_lt_inv_nnnorm_refl :
    (1 / 2 : ℝ≥0) < ‖((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).symm : ℝ × ℝ →L[ℝ] ℝ × ℝ)‖₊⁻¹ := by
  rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
    ContinuousLinearMap.nnNorm_id, inv_one]
  norm_num

/-- For `|c| ≤ 1` the map `Φ_c` is injective. -/
theorem injective_exchangeMap (hc : |c| ≤ 1) : Injective (exchangeMap c) :=
  injOn_univ.1 <| (approximatesLinearOn_exchangeMap hc).injOn (Or.inr one_half_lt_inv_nnnorm_refl)

/-- For `|c| ≤ 1` the map `Φ_c` is surjective. -/
theorem surjective_exchangeMap (hc : |c| ≤ 1) : Surjective (exchangeMap c) :=
  (approximatesLinearOn_exchangeMap hc).surjective (Or.inr one_half_lt_inv_nnnorm_refl)

/-- For `|c| ≤ 1` the diffeomorphism `Φ_c` preserves orientation: its Jacobian determinant is
`1 + ∂_s` of the displacement, which is at least `1/2`. -/
theorem det_fderiv_exchangeMap_nonneg (hc : |c| ≤ 1) (y : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (exchangeMap c) y).det := by
  set g := exchangeShift c
  have hg : HasFDerivAt g (fderiv ℝ g y) y :=
    ((contDiff_exchangeShift c).differentiable two_ne_zero y).hasFDerivAt
  have hΦ : HasFDerivAt (exchangeMap c)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ) + fderiv ℝ g y).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) y :=
    (hasFDerivAt_fst.add hg).prodMk hasFDerivAt_snd
  have hnorm : ‖fderiv ℝ g y‖ ≤ 1 / 2 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_exchangeShift hc) (x₀ := y)
  have hcol : |fderiv ℝ g y (1, 0)| ≤ 1 / 2 := by
    have h := (fderiv ℝ g y).le_opNorm (1, 0)
    rw [Real.norm_eq_abs] at h
    have h₁ : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
    rw [h₁, mul_one] at h
    exact h.trans hnorm
  rw [ContinuousLinearMap.det, hΦ.fderiv, LinearMap.det_finTwoProd]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd']
  simp only [_root_.add_apply, ContinuousLinearMap.coe_fst']
  linarith [(abs_le.1 hcol).1]

/-- On the disc `|w| < 3` the map `Φ_c` is the identity nearby. -/
theorem exchangeMap_eventuallyEq_id (hy : ‖Complex.equivRealProdCLM.symm y‖ < 3) :
    exchangeMap c =ᶠ[𝓝 y] id := by
  filter_upwards [(isOpen_lt (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)
    continuous_const).mem_nhds hy] with y' hy'
  ext <;> simp [exchangeMap, exchangeShift_of_norm_le (le_of_lt hy')]

/-- Off the disc `|w| ≤ 8` the map `Φ_c` is the translation by `c` nearby. -/
theorem exchangeMap_eventuallyEq_add (hy : 8 < ‖Complex.equivRealProdCLM.symm y‖) :
    exchangeMap c =ᶠ[𝓝 y] (· + (c, 0)) := by
  filter_upwards [(isOpen_lt continuous_const
    (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)).mem_nhds hy] with y' hy'
  ext <;> simp [exchangeMap, exchangeShift_of_le_norm (le_of_lt hy')]

/-- Beyond the height `1` of the output end, the map `Φ_c` is the translation by `c` nearby. -/
theorem exchangeMap_eventuallyEq_add_of_one_lt (hy : 1 < (positiveEndCoord inf y).1) :
    exchangeMap c =ᶠ[𝓝 y] (· + (c, 0)) :=
  exchangeMap_eventuallyEq_add (eight_lt_norm_of_one_lt_fst_positiveEndCoord_inf hy)

/-- On the disc `|w| ≤ 3` the map `Φ_c` is the identity. -/
theorem exchangeMap_of_norm_le (hy : ‖Complex.equivRealProdCLM.symm y‖ ≤ 3) :
    exchangeMap c y = y := by
  ext <;> simp [exchangeMap, exchangeShift_of_norm_le hy]

/-- Off the open disc `|w| < 8` the map `Φ_c` is the translation by `c`. -/
theorem exchangeMap_of_le_norm (hy : 8 ≤ ‖Complex.equivRealProdCLM.symm y‖) :
    exchangeMap c y = y + (c, 0) := by
  ext <;> simp [exchangeMap, exchangeShift_of_le_norm hy]

/-- The map `Φ_c` keeps the `t` coordinate. -/
@[simp]
theorem snd_exchangeMap (c : ℝ) (y : ℝ × ℝ) : (exchangeMap c y).2 = y.2 := by
  simp [exchangeMap]

/-- For `c ≥ 0` the map `Φ_c` moves the `s` coordinate to the right. -/
theorem le_fst_exchangeMap (hc : 0 ≤ c) (y : ℝ × ℝ) : y.1 ≤ (exchangeMap c y).1 := by
  simpa [exchangeMap] using exchangeShift_nonneg hc y

/-- For `c ≥ 0` the map `Φ_c` moves the `s` coordinate by at most `c`. -/
theorem fst_exchangeMap_le (hc : 0 ≤ c) (y : ℝ × ℝ) : (exchangeMap c y).1 ≤ y.1 + c := by
  simpa [exchangeMap] using exchangeShift_le hc y

/-! ### Pulling back along `Φ_c` -/

section Datum

variable {M : Type*}

/-- **Pulling back along `Φ_c` moves the recentred output end back to `∞`.** Let `K₁` and `K₀` be
perturbation data on `ℂ` and `0 ≤ c ≤ 1`. Suppose that `K₁` agrees with `K₀` on the disc
`|w| ≤ 3`, that `K₁` vanishes on the annulus `2 ≤ |w - c| ≤ 10` and `K₀` on the annulus
`2 ≤ |w| ≤ 10`, and that `K₁(w + c) = K₀(w)` for `|w| ≥ 3/2`. Then the pullback of `K₁` along
`Φ_c` is `K₀`. The member `c` of the input-exchange family is such a datum, with `K₀` the
pair-of-pants datum. -/
theorem perturbationPullback_exchangeMap_of_eq (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {K₁ K₀ : ℂ → M → ℂ →L[ℝ] ℝ} (hnear : ∀ w : ℂ, ‖w‖ ≤ 3 → K₁ w = K₀ w)
    (hmid₁ : ∀ w : ℂ, 2 ≤ ‖w - c‖ → ‖w - c‖ ≤ 10 → K₁ w = 0)
    (hmid₀ : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖w‖ ≤ 10 → K₀ w = 0)
    (hfar : ∀ w : ℂ, 3 / 2 ≤ ‖w‖ → K₁ (w + c) = K₀ w) (v y : ℝ × ℝ) (x : M) :
    perturbationPullback (exchangeMap c)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
      K₀ (Complex.equivRealProdCLM.symm y) x (Complex.equivRealProdCLM.symm v) := by
  set e := Complex.equivRealProdCLM.symm
  -- A real-linear form on `ℂ` evaluated on `s + i t`.
  have hv : K₀ (e y) x (e v) = v.1 * K₀ (e y) x 1 + v.2 * K₀ (e y) x Complex.I := by
    have h := ((K₀ (e y) x).comp (e : ℝ × ℝ →L[ℝ] ℂ) : ℝ × ℝ →ₗ[ℝ] ℝ).apply_stdComplexLine v
    simpa [e] using h
  rw [perturbationPullback_apply, hv]
  rcases lt_or_ge ‖e y‖ 3 with h₃ | h₃
  · -- Near the input ends `Φ_c` is the identity and the two data agree.
    rw [(exchangeMap_eventuallyEq_id h₃).fderiv_eq, exchangeMap_of_norm_le h₃.le]
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
    rw [hnear _ h₃.le]
  rcases le_or_gt ‖e y‖ 8 with h₈ | h₈
  · -- In between both data vanish.
    have hw : e (exchangeMap c y) - c = e y + (exchangeShift c y - c : ℝ) := by
      rw [equivRealProdCLM_symm_exchangeMap]
      push_cast
      ring
    have hs : |exchangeShift c y - c| ≤ 1 := abs_le.2 ⟨by linarith [exchangeShift_nonneg hc₀ y],
      by linarith [exchangeShift_le hc₀ y]⟩
    have hn := norm_add_le (e y) ((exchangeShift c y - c : ℝ) : ℂ)
    have hn' := norm_sub_norm_le (e y) (-((exchangeShift c y - c : ℝ) : ℂ))
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, sub_neg_eq_add] at hn'
    have h0 := hmid₁ (e (exchangeMap c y)) (by rw [hw]; linarith) (by rw [hw]; linarith)
    have h0' := hmid₀ (e y) (by linarith) (by linarith)
    simp [h0, h0']
  · -- Near the output end `Φ_c` is the translation by `c` and the data are translates.
    rw [(exchangeMap_eventuallyEq_add h₈).fderiv_eq, fderiv_add_const,
      exchangeMap_of_le_norm h₈.le]
    simp only [fderiv_fun_id, ContinuousLinearMap.id_apply]
    have he : e (y + (c, 0)) = e y + c := by
      rw [map_add, Complex.equivRealProdCLM_symm_apply (c, 0)]
      simp
    rw [he, hfar _ (by linarith)]

/-- The pullback along `Φ_c` in the directions `∂_s` and `∂_t`, for data as in
`TauCeti.Floer.perturbationPullback_exchangeMap_of_eq`. -/
private theorem perturbationPullback_exchangeMap_stdComplexLine {K₁ K₀ : ℂ → M → ℂ →L[ℝ] ℝ}
    (hpull : ∀ v y x, perturbationPullback (exchangeMap c)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
        K₀ (Complex.equivRealProdCLM.symm y) x (Complex.equivRealProdCLM.symm v)) :
    perturbationPullback (exchangeMap c) (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal =
      (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x 1) ∧
    perturbationPullback (exchangeMap c) (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag =
      fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x Complex.I :=
  ⟨funext fun y ↦ funext fun x ↦ by rw [hpull, equivRealProdCLM_symm_stdComplexLineReal],
    funext fun y ↦ funext fun x ↦ by rw [hpull, equivRealProdCLM_symm_stdComplexLineImag]⟩

end Datum


/-! ### Images of domains under `Φ_c` -/

/-- Norm estimates for `Φ_c(w) = w + g`, where `0 ≤ g ≤ c ≤ 1`. -/
private theorem norm_exchangeMap_bounds (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (y : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm y‖ - 1 ≤ ‖Complex.equivRealProdCLM.symm (exchangeMap c y)‖ ∧
      ‖Complex.equivRealProdCLM.symm y‖ - 2 ≤
        ‖Complex.equivRealProdCLM.symm (exchangeMap c y) - 1‖ ∧
      ‖Complex.equivRealProdCLM.symm (exchangeMap c y) - c‖ ≤
        ‖Complex.equivRealProdCLM.symm y‖ + 1 := by
  rw [equivRealProdCLM_symm_exchangeMap]
  set w := Complex.equivRealProdCLM.symm y
  set g := exchangeShift c y
  have hg₀ : 0 ≤ g := exchangeShift_nonneg hc₀ y
  have hg₁ : g ≤ c := exchangeShift_le hc₀ y
  have h₁ := norm_sub_norm_le w (-(g : ℂ))
  have h₂ := norm_sub_norm_le w (1 - (g : ℂ))
  have h₃ := norm_add_le w ((g : ℂ) - c)
  have hn₁ : ‖(1 : ℂ) - g‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hn₃ : ‖(g : ℂ) - c‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hg₀, sub_neg_eq_add] at h₁
  rw [sub_sub_eq_add_sub] at h₂
  rw [show w + (g : ℂ) - c = w + ((g : ℂ) - c) by ring]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- `Φ_c` preserves the thrice-punctured sphere `S = ℂ ∖ {0, 1}`. -/
theorem exchangeMap_mem_thricePuncturedSphereReal_iff (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (y : ℝ × ℝ) :
    exchangeMap c y ∈ thricePuncturedSphereReal ↔ y ∈ thricePuncturedSphereReal := by
  simp only [mem_thricePuncturedSphereReal_iff]
  set w := Complex.equivRealProdCLM.symm y
  rcases le_or_gt ‖w‖ 3 with h₃ | h₃
  · rw [exchangeMap_of_norm_le h₃]
  · obtain ⟨h₁, h₂, -⟩ := norm_exchangeMap_bounds hc₀ hc₁ y
    have hne {z : ℂ} (hz : 1 < ‖z‖) : z ≠ 0 ∧ z ≠ 1 :=
      ⟨fun h ↦ by rw [h, norm_zero] at hz; linarith, fun h ↦ by rw [h, norm_one] at hz; linarith⟩
    have hne' {z : ℂ} (hz₀ : 1 < ‖z‖) (hz₁ : 0 < ‖z - 1‖) : z ≠ 0 ∧ z ≠ 1 :=
      ⟨(hne hz₀).1, fun h ↦ by rw [h, sub_self, norm_zero] at hz₁; linarith⟩
    exact iff_of_true (hne' (by linarith) (by linarith)) (hne (by linarith))

/-- For `0 ≤ c ≤ 1`, `Φ_c` maps the thrice-punctured sphere `S = ℂ ∖ {0, 1}` onto itself. -/
theorem image_exchangeMap_thricePuncturedSphereReal (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    exchangeMap c '' thricePuncturedSphereReal = thricePuncturedSphereReal := by
  have h : thricePuncturedSphereReal = exchangeMap c ⁻¹' thricePuncturedSphereReal :=
    Set.ext fun y ↦ (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ y).symm
  conv_lhs => rw [h]
  exact Set.image_preimage_eq _ (surjective_exchangeMap (abs_le.2 ⟨by linarith, hc₁⟩))

/-- For `R ≥ 1`, `Φ_c` maps the truncation `S_R` of the pair of pants onto the truncation with
output end recentred at `c`. -/
theorem image_exchangeMap_truncation (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {R : ℝ} (hR : 1 ≤ R) :
    exchangeMap c '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R) =
      Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R := by
  have hr : Real.exp (-(2 * π * R)) / 2 ≤ 1 / 2 := by
    have : Real.exp (-(2 * π * R)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    linarith
  have hρ : 14 ≤ 2 * Real.exp (2 * π * R) := by
    have h₁ : 2 * π ≤ 2 * π * R := le_mul_of_one_le_right (by positivity) hR
    linarith [Real.exp_le_exp.2 h₁, fourteen_le_two_mul_exp_two_pi]
  have h : Complex.equivRealProdCLM.symm ⁻¹' truncation R =
      exchangeMap c ⁻¹' (Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R) := by
    ext y
    simp only [mem_preimage, ← exchangeTruncation_zero, mem_exchangeTruncation,
      Complex.ofReal_zero, sub_zero]
    set w := Complex.equivRealProdCLM.symm y
    rcases le_or_gt ‖w‖ 3 with h₃ | h₃
    · -- Near the inputs `Φ_c` is the identity, and both outer circles lie far out.
      rw [exchangeMap_of_norm_le h₃]
      have hwc : ‖w - c‖ ≤ 4 := by
        have := norm_sub_le w (c : ℂ)
        rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at this
        linarith
      exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
        iff_of_true (by linarith) (by linarith)
    rcases le_or_gt ‖w‖ 8 with h₈ | h₈
    · -- In between every condition holds on both sides.
      obtain ⟨h₁, h₂, h₄⟩ := norm_exchangeMap_bounds hc₀ hc₁ y
      have hw₁ := norm_sub_norm_le w 1
      rw [norm_one] at hw₁
      exact iff_of_true ⟨by linarith, by linarith, by linarith⟩
        ⟨by linarith, by linarith, by linarith⟩
    · -- Near the output end `Φ_c` is the translation by `c`.
      rw [exchangeMap_of_le_norm h₈.le]
      have he : Complex.equivRealProdCLM.symm (y + (c, 0)) = w + c :=
        TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero y c
      have hw₁ := norm_sub_norm_le w 1
      have hw₂ := norm_sub_norm_le (w + c) 1
      have hw₃ := norm_sub_norm_le w (-(c : ℂ))
      rw [norm_one] at hw₁ hw₂
      rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hc₀, sub_neg_eq_add] at hw₃
      rw [he, add_sub_cancel_right]
      exact and_congr (iff_of_true (by linarith) (by linarith))
        (and_congr (iff_of_true (by linarith) (by linarith)) Iff.rfl)
  rw [h, Set.image_preimage_eq _ (surjective_exchangeMap (abs_le.2 ⟨by linarith, hc₁⟩))]

/-! ### The boundary loops -/

/-- On the boundary circle `s = R ≥ 0` of an input end, `Φ_c` is the identity. -/
theorem exchangeMap_cylindricalEndLift (c : ℝ) {q : Puncture} (hq : q ≠ inf) {R : ℝ}
    (hR : 0 ≤ R) (t : ℝ) :
    exchangeMap c (Complex.equivRealProdCLM (q.cylindricalEndLift (R + t * Complex.I))) =
      Complex.equivRealProdCLM (q.cylindricalEndLift (R + t * Complex.I)) := by
  refine exchangeMap_of_norm_le ?_
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have h := norm_cylindricalEndLift_sub_le hq le_rfl zero_le_one
    (z := ↑R + ↑t * Complex.I) (by simpa using hR)
  rw [Complex.ofReal_zero, sub_zero] at h
  exact h.trans (by norm_num)

/-- On the boundary circle `s = -R ≤ -1` of the output end, `Φ_c` is the translation by `c`. -/
theorem exchangeMap_cylindricalEndLift_inf (c : ℝ) {R : ℝ} (hR : 1 ≤ R) (t : ℝ) :
    exchangeMap c (Complex.equivRealProdCLM (inf.cylindricalEndLift (↑(-R) + t * Complex.I))) =
      Complex.equivRealProdCLM (c + inf.cylindricalEndLift (↑(-R) + t * Complex.I)) := by
  rw [exchangeMap_of_le_norm]
  · ext <;> simp [add_comm]
  · rw [ContinuousLinearEquiv.symm_apply_apply]
    have h := two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
      (z := ↑(-R) + ↑t * Complex.I) (by simpa using hR)
    rw [mul_one] at h
    linarith [fourteen_le_two_mul_exp_two_pi]

/-! ### Transport of integrals along `Φ_c` -/

/-- A density is integrable over the image of a measurable set under `Φ_c` if and only if the
density pulled back along `Φ_c` is integrable over the set. -/
theorem integrableOn_image_exchangeMap_iff (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) {g g' : ℝ × ℝ → ℝ}
    (hg' : ∀ w ∈ s, g' w = (fderiv ℝ (exchangeMap c) w).det * g (exchangeMap c w)) :
    IntegrableOn g (exchangeMap c '' s) ↔ IntegrableOn g' s := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hd (w : ℝ × ℝ) : DifferentiableAt ℝ (exchangeMap c) w :=
    (contDiff_exchangeMap c).differentiable two_ne_zero w
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun w _ ↦ (hd w).hasFDerivAt.hasFDerivWithinAt) (injective_exchangeMap hc).injOn g]
  refine integrableOn_congr_fun (fun w hw ↦ ?_) hs
  rw [abs_of_nonneg (det_fderiv_exchangeMap_nonneg hc w), smul_eq_mul, hg' w hw]

/-- Integrability over the image of a measurable set under `Φ_c` transfers to the density
pulled back along `Φ_c`. -/
theorem integrableOn_of_integrableOn_image_exchangeMap (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) {g g' : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (exchangeMap c '' s))
    (hg' : ∀ w ∈ s, g' w = (fderiv ℝ (exchangeMap c) w).det * g (exchangeMap c w)) :
    IntegrableOn g' s :=
  (integrableOn_image_exchangeMap_iff hc₀ hc₁ hs hg').1 hg

section Manifold

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- If `u` is `C¹` on `S`, then so is `u ∘ Φ_c`. -/
theorem contMDiffOn_comp_exchangeMap (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ exchangeMap c) thricePuncturedSphereReal :=
  hu.comp ((contDiff_exchangeMap c).of_le one_le_two).contMDiff.contMDiffOn
    fun w hw ↦ (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 hw

/-- If `u` is `C¹` on `S`, then it is differentiable at the image under `Φ_c` of every point of
`S`. -/
theorem mdifferentiableAt_exchangeMap (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {w : ℝ × ℝ} (hw : w ∈ thricePuncturedSphereReal) :
    MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (exchangeMap c w) :=
  have hS := (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 hw
  ((hu.mdifferentiableOn one_ne_zero) _ hS).mdifferentiableAt
    (isOpen_thricePuncturedSphereReal.mem_nhds hS)

end Manifold

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] {c : ℝ}

variable {K₁ K₀ : ℂ → M → ℂ →L[ℝ] ℝ}

variable [IsManifold I ⊤ M] {ω : SmoothTwoForm I M}

/-- **Pulling back along `Φ_c` multiplies the energy density by the Jacobian.** Let `K₁` be a
datum which is `C¹` over `S` and whose pullback along `Φ_c` is `K₀`, as in
`TauCeti.Floer.perturbationPullback_exchangeMap_of_eq`. At points of `S` the energy density of
`u ∘ Φ_c` for `K₀` is `det dΦ_c` times that of `u` for `K₁` at the image point. -/
theorem floerEnergyDensity_comp_exchangeMap (ω : SmoothTwoForm I M)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K₁ p.1 p.2) (Complex.equivRealProdCLM.symm z, x))
    (hpull : ∀ v y x, perturbationPullback (exchangeMap c)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
        K₀ (Complex.equivRealProdCLM.symm y) x (Complex.equivRealProdCLM.symm v))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {w : ℝ × ℝ}
    (hw : w ∈ thricePuncturedSphereReal) :
    ω.floerEnergyDensity
        (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ exchangeMap c) w =
      (fderiv ℝ (exchangeMap c) w).det * ω.floerEnergyDensity
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (exchangeMap c w) := by
  have hS := (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 hw
  rw [← (perturbationPullback_exchangeMap_stdComplexLine hpull).1,
    ← (perturbationPullback_exchangeMap_stdComplexLine hpull).2]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_exchangeMap c).differentiable two_ne_zero w)
    (mdifferentiableAt_exchangeMap hc₀ hc₁ hu hw)
    (mdifferentiableAt_target_of_contMDiffAt (hK _ hS _) one_ne_zero _)
    (mdifferentiableAt_target_of_contMDiffAt (hK _ hS _) one_ne_zero _)

/-- **Energy is invariant under `Φ_c`.** For a datum `K₁` which is `C¹` over `S` and whose
pullback along `Φ_c` is `K₀`, the energy of `u` for `K₁` over the image under `Φ_c` of a
measurable part `s` of `S` is the energy of `u ∘ Φ_c` for `K₀` over `s`, for a manifold
target. -/
theorem integral_floerEnergyDensity_image_exchangeMap (ω : SmoothTwoForm I M)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K₁ p.1 p.2) (Complex.equivRealProdCLM.symm z, x))
    (hpull : ∀ v y x, perturbationPullback (exchangeMap c)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
        K₀ (Complex.equivRealProdCLM.symm y) x (Complex.equivRealProdCLM.symm v))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsS : s ⊆ thricePuncturedSphereReal) :
    ∫ z in exchangeMap c '' s, ω.floerEnergyDensity
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in s, ω.floerEnergyDensity
        (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ exchangeMap c) z := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  have hS {w : ℝ × ℝ} (hw : w ∈ s) : exchangeMap c w ∈ thricePuncturedSphereReal :=
    (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 (hsS hw)
  rw [ω.integral_floerEnergyDensity_image hs (injective_exchangeMap hc).injOn
    (fun w _ ↦ (contDiff_exchangeMap c).differentiable two_ne_zero w)
    (fun w _ ↦ det_fderiv_exchangeMap_nonneg hc w)
    (fun w hw ↦ mdifferentiableAt_exchangeMap hc₀ hc₁ hu (hsS hw))
    (fun w hw ↦ mdifferentiableAt_target_of_contMDiffAt (hK _ (hS hw) _) one_ne_zero _)
    (fun w hw ↦ mdifferentiableAt_target_of_contMDiffAt (hK _ (hS hw) _) one_ne_zero _),
    (perturbationPullback_exchangeMap_stdComplexLine hpull).1,
    (perturbationPullback_exchangeMap_stdComplexLine hpull).2]

/-- **Symplectic area is invariant under `Φ_c`.** The symplectic area of `u` over the image under
`Φ_c` of a measurable part `s` of `S` is that of `u ∘ Φ_c` over `s`. -/
theorem integral_area_image_exchangeMap (ω : SmoothTwoForm I M) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsS : s ⊆ thricePuncturedSphereReal) :
    ∫ z in exchangeMap c '' s,
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      ∫ z in s,
        (SmoothBundleForm.eval₂ ω ((u ∘ exchangeMap c) z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ exchangeMap c) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ exchangeMap c) z stdComplexLineImag) : ℝ) := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  exact ω.integral_eval₂_mfderiv_stdComplexLine_image hs (injective_exchangeMap hc).injOn
    (fun w _ ↦ (contDiff_exchangeMap c).differentiable two_ne_zero w)
    (fun w _ ↦ det_fderiv_exchangeMap_nonneg hc w)
    (fun w hw ↦ mdifferentiableAt_exchangeMap hc₀ hc₁ hu (hsS hw))

/-- **Integrated curvature is invariant under `Φ_c`.** For a datum `K₁` which is `C¹` over `S`
and whose pullback along `Φ_c` is `K₀`, the integrated curvature of `K₁` along `u` over the image
under `Φ_c` of a measurable part `s` of `S` is that of `K₀` along `u ∘ Φ_c` over `s`. -/
theorem integral_hamiltonianCurvature_image_exchangeMap (ω : SmoothTwoForm I M)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K₁ p.1 p.2) (Complex.equivRealProdCLM.symm z, x))
    (hpull : ∀ v y x, perturbationPullback (exchangeMap c)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
        K₀ (Complex.equivRealProdCLM.symm y) x (Complex.equivRealProdCLM.symm v))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (u : ℝ × ℝ → M) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsS : s ⊆ thricePuncturedSphereReal) :
    ∫ z in exchangeMap c '' s, ω.hamiltonianCurvature
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x Complex.I)
        z ((u ∘ exchangeMap c) z) := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  have hS {w : ℝ × ℝ} (hw : w ∈ s) : exchangeMap c w ∈ thricePuncturedSphereReal :=
    (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 (hsS hw)
  rw [ω.integral_hamiltonianCurvature_image hs (injective_exchangeMap hc).injOn
    (fun w _ ↦ (contDiff_exchangeMap c).contDiffAt)
    (fun w _ ↦ det_fderiv_exchangeMap_nonneg hc w)
    (fun w hw ↦ differentiableAt_domain_of_contMDiffAt (hK _ (hS hw) _) one_ne_zero _)
    (fun w hw ↦ differentiableAt_domain_of_contMDiffAt (hK _ (hS hw) _) one_ne_zero _)
    (fun w hw ↦ mdifferentiableAt_target_of_contMDiffAt (hK _ (hS hw) _) one_ne_zero _)
    (fun w hw ↦ mdifferentiableAt_target_of_contMDiffAt (hK _ (hS hw) _) one_ne_zero _),
    (perturbationPullback_exchangeMap_stdComplexLine hpull).1,
    (perturbationPullback_exchangeMap_stdComplexLine hpull).2]
  simp only [comp_apply]

/-- **Integrability of the curvature transfers along `Φ_c`.** For a datum `K₁` which is `C¹` over
`S` and whose pullback along `Φ_c` is `K₀`, if the curvature of `K₀` along `u ∘ Φ_c` is integrable
over a measurable part `s` of `S`, then the curvature of `K₁` along `u` is integrable over the
image of `s` under `Φ_c`. -/
theorem integrableOn_hamiltonianCurvature_image_exchangeMap (ω : SmoothTwoForm I M)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K₁ p.1 p.2) (Complex.equivRealProdCLM.symm z, x))
    (hpull : ∀ v y x, perturbationPullback (exchangeMap c)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
        K₀ (Complex.equivRealProdCLM.symm y) x (Complex.equivRealProdCLM.symm v))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (u : ℝ × ℝ → M) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsS : s ⊆ thricePuncturedSphereReal)
    (hint : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₀ (Complex.equivRealProdCLM.symm z) x Complex.I)
      z ((u ∘ exchangeMap c) z)) s) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K₁ (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) (exchangeMap c '' s) := by
  refine (integrableOn_image_exchangeMap_iff hc₀ hc₁ hs fun w hw ↦ ?_).2 hint
  have hS := (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 (hsS hw)
  rw [← (perturbationPullback_exchangeMap_stdComplexLine hpull).1,
    ← (perturbationPullback_exchangeMap_stdComplexLine hpull).2]
  exact ω.hamiltonianCurvature_perturbationPullback (contDiff_exchangeMap c).contDiffAt
    (differentiableAt_domain_of_contMDiffAt (hK _ hS _) one_ne_zero _)
    (differentiableAt_domain_of_contMDiffAt (hK _ hS _) one_ne_zero _)
    (mdifferentiableAt_target_of_contMDiffAt (hK _ hS _) one_ne_zero _)
    (mdifferentiableAt_target_of_contMDiffAt (hK _ hS _) one_ne_zero _)

end SmoothTwoForm

end TauCeti
