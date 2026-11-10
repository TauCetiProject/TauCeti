/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.LinearAlgebra.Determinant.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# The energy of the input-exchange family

Graded commutativity of the pair-of-pants product is proved with the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, of perturbation data on
`S = ℂ ∖ {0, 1}`: the input part of the pair-of-pants datum plus the negative plane datum of the
output Hamiltonian translated by `c`, so that the output end of `K_c` is the end at `∞` recentred at
`c`. A one-parameter family of moduli spaces gives a chain homotopy whose kernel must be supported
in the sense of `TauCeti.NovikovModule.kernelProduct`, and this support comes from an action bound
that is uniform in `c`. This file proves the energy identity of every member of the family and the
resulting action and energy bounds, all with the same constants as for the pair of pants.

Write `ℓ_q(R)(t) = u(φ_q(R + i t))` for the loops of a map `u` along the circles `s = R` of the
input ends `q ∈ {0, 1}`, and `ℓ^c_∞(R)(t) = u(c + φ_∞(-R + i t))` for its loop along the circle
`s = -R` of the recentred output end. These circles bound the truncation
`TauCeti.ThricePuncturedSphere.exchangeTruncation c R`. For a map `u` which is `C²` on `S`,
period-one `C¹` Hamiltonians `H_q` on a symplectic vector space and `R ≥ 2`, the Floer energy of
`u` for `K_c` over this truncation is

`∫ E = A_{H_0}(ℓ_0(R)) + A_{H_1}(ℓ_1(R)) - A_{H_∞}(ℓ^c_∞(R)) - ∫_S R_{K_c}(u)`

(`SymplecticForm.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation`), where
`A_H` is the Hamiltonian action `TauCeti.SymplecticForm.hamiltonianAction`. For `c = 0` this is the
energy identity of the pair of pants
(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`).
Since the curvature of `K_c` along `u` is that of `K_0` along `u ∘ Φ_c`, the curvature bound
`TauCeti.SymplecticForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le` shows that
the energy differs from the change of action by at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`
(`SymplecticForm.abs_integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation_sub_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, which gives the action bound `A_{H_∞}(ℓ^c_∞(R)) ≤ A_{H_0}(ℓ_0(R)) + A_{H_1}(ℓ_1(R))
+ B₀ + B₁ + B_∞` (`SymplecticForm.hamiltonianAction_le_add_add_sum_of_exchangePerturbation`) and its
limit `a_∞ ≤ a_0 + a_1 + B₀ + B₁ + B_∞` for the limiting actions of the ends
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation`). As for the
pair of pants, the constant can be replaced by the one-sided constant
`-∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞` for functions of time with `h_q ≤ H_q` on the inputs and
`H_∞ ≤ h_∞` on the output, which transforms correctly under a change of normalization of the
Hamiltonians (`SymplecticForm.hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation`,
`SymplecticForm.le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation`).

The member `c` of the family is the pullback of the pair-of-pants datum `K_0` along an
orientation-preserving diffeomorphism `Φ_c` of the plane, `Φ_c(s, t) = (s + c (1 - μ(|w|)), t)` for
`w = s + i t` and a smooth radial cutoff `μ` equal to `1` for `|w| ≤ 3` and to `0` for `|w| ≥ 8`,
with slope at most `1/4`. It is the identity near the input ends, where `K_c = K_0`, the
translation by `c` near the output end, where `K_c` is the translate of `K_0`, and in between both
data vanish. The slope bound makes `Φ_c` injective with positive Jacobian, and `Φ_c` maps the
truncation `S_R` of the pair of pants onto the truncation with recentred output end. Since the
energy density and the curvature are two-forms (`TauCeti.Geometry.Symplectic.Floer.Pullback`),
the energy identity of the pair of pants for `u ∘ Φ_c` is the energy identity of `K_c` for `u`.
The diffeomorphism is not holomorphic, so `u ∘ Φ_c` need not solve a Floer equation; only the
energy identity, which holds for every map, is transported.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product and its energy
  estimate.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal

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

/-- The radial cutoff of the diffeomorphism `Φ_c`. -/
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
  refine lipschitzWith_of_nnnorm_deriv_le (contDiff_exchangeCutoff.differentiable two_ne_zero)
    fun r ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact (exists_exchangeCutoff.choose_spec.2.2.2.2.2.1 r).trans_eq (by simp)

/-- The horizontal displacement `c (1 - μ(|w|))` of `Φ_c` at `w = s + i t`. -/
private noncomputable def exchangeShift (c : ℝ) (y : ℝ × ℝ) : ℝ :=
  c * (1 - exchangeCutoff ‖Complex.equivRealProdCLM.symm y‖)

/-- The diffeomorphism `Φ_c(s, t) = (s + c (1 - μ(|w|)), t)` of the plane, which carries the
pair-of-pants datum to the member `c` of the input-exchange family. -/
private noncomputable def exchangeMap (c : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
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

private theorem contDiff_exchangeMap (c : ℝ) : ContDiff ℝ 2 (exchangeMap c) :=
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
    ContinuousLinearMap.nnnorm_id, inv_one]
  norm_num

private theorem injective_exchangeMap (hc : |c| ≤ 1) : Injective (exchangeMap c) :=
  injOn_univ.1 <| (approximatesLinearOn_exchangeMap hc).injOn (Or.inr one_half_lt_inv_nnnorm_refl)

private theorem surjective_exchangeMap (hc : |c| ≤ 1) : Surjective (exchangeMap c) :=
  (approximatesLinearOn_exchangeMap hc).surjective (Or.inr one_half_lt_inv_nnnorm_refl)

/-- For `|c| ≤ 1` the diffeomorphism `Φ_c` preserves orientation: its Jacobian determinant is
`1 + ∂_s` of the displacement, which is at least `1/2`. -/
private theorem det_fderiv_exchangeMap_nonneg (hc : |c| ≤ 1) (y : ℝ × ℝ) :
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

/-- On the disc `|w| < 3` the diffeomorphism `Φ_c` is the identity nearby. -/
private theorem exchangeMap_eventuallyEq_id (hy : ‖Complex.equivRealProdCLM.symm y‖ < 3) :
    exchangeMap c =ᶠ[𝓝 y] id := by
  filter_upwards [(isOpen_lt (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)
    continuous_const).mem_nhds hy] with y' hy'
  ext <;> simp [exchangeMap, exchangeShift_of_norm_le (le_of_lt hy')]

/-- Off the disc `|w| ≤ 8` the diffeomorphism `Φ_c` is the translation by `c` nearby. -/
private theorem exchangeMap_eventuallyEq_add (hy : 8 < ‖Complex.equivRealProdCLM.symm y‖) :
    exchangeMap c =ᶠ[𝓝 y] (· + (c, 0)) := by
  filter_upwards [(isOpen_lt continuous_const
    (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)).mem_nhds hy] with y' hy'
  ext <;> simp [exchangeMap, exchangeShift_of_le_norm (le_of_lt hy')]

private theorem exchangeMap_of_norm_le (hy : ‖Complex.equivRealProdCLM.symm y‖ ≤ 3) :
    exchangeMap c y = y := by
  ext <;> simp [exchangeMap, exchangeShift_of_norm_le hy]

private theorem exchangeMap_of_le_norm (hy : 8 ≤ ‖Complex.equivRealProdCLM.symm y‖) :
    exchangeMap c y = y + (c, 0) := by
  ext <;> simp [exchangeMap, exchangeShift_of_le_norm hy]

/-! ### The family as a pullback of the pair-of-pants datum -/

section Datum

variable {M : Type*} {H : Puncture → ℝ → M → ℝ}

/-- `2 exp (2π)` exceeds `14`. -/
private theorem fourteen_le_two_mul_exp_two_pi : 14 ≤ 2 * Real.exp (2 * π) := by
  nlinarith [Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * π), Real.two_le_pi]

/-- **The member `c` of the family is the pullback of the pair-of-pants datum along `Φ_c`.** -/
private theorem perturbationPullback_exchangeMap (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (v y : ℝ × ℝ)
    (x : M) :
    perturbationPullback (exchangeMap c)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm y) x
        (Complex.equivRealProdCLM.symm v) := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  set e := Complex.equivRealProdCLM.symm
  -- A real-linear form on `ℂ` evaluated on `s + i t`.
  have hv : pairOfPantsPerturbation H (e y) x (e v) = v.1 * pairOfPantsPerturbation H (e y) x 1 +
      v.2 * pairOfPantsPerturbation H (e y) x Complex.I := by
    have h := ((pairOfPantsPerturbation H (e y) x).comp (e : ℝ × ℝ →L[ℝ] ℂ) :
      ℝ × ℝ →ₗ[ℝ] ℝ).apply_stdComplexLine v
    simpa [e] using h
  rw [perturbationPullback_apply, hv]
  rcases lt_or_ge ‖e y‖ 3 with h₃ | h₃
  · -- Near the input ends `Φ_c` is the identity and the two data agree.
    rw [(exchangeMap_eventuallyEq_id h₃).fderiv_eq, exchangeMap_of_norm_le h₃.le]
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
    rw [exchangePerturbation_of_norm_le hc₀ hc₁ h₃.le]
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
    have h0 := exchangePerturbation_eq_zero (H := H) hc₀ hc₁ (w := e (exchangeMap c y))
      (by rw [hw]; linarith) (by rw [hw]; linarith)
    have h0' : pairOfPantsPerturbation H (e y) x = 0 := by
      rw [← exchangePerturbation_zero]
      exact exchangePerturbation_eq_zero le_rfl zero_le_one (by simpa using by linarith)
        (by simpa using by linarith) x
    simp [h0, h0']
  · -- Near the output end `Φ_c` is the translation by `c` and the data are translates.
    rw [(exchangeMap_eventuallyEq_add h₈).fderiv_eq, fderiv_add_const,
      exchangeMap_of_le_norm h₈.le]
    simp only [fderiv_fun_id, ContinuousLinearMap.id_apply]
    have he : e (y + (c, 0)) = e y + c := by
      rw [map_add, Complex.equivRealProdCLM_symm_apply (c, 0)]
      simp
    rw [he, exchangePerturbation_add hc₀ hc₁ (by linarith)]

private theorem perturbationPullback_exchangeMap_stdComplexLineReal (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    perturbationPullback (exchangeMap c)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal =
      fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 := by
  funext y x
  rw [perturbationPullback_exchangeMap hc₀ hc₁, equivRealProdCLM_symm_stdComplexLineReal]

private theorem perturbationPullback_exchangeMap_stdComplexLineImag (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    perturbationPullback (exchangeMap c)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag =
      fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I := by
  funext y x
  rw [perturbationPullback_exchangeMap hc₀ hc₁, equivRealProdCLM_symm_stdComplexLineImag]

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
private theorem exchangeMap_mem_iff (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (y : ℝ × ℝ) :
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

private theorem image_exchangeMap_thricePuncturedSphereReal (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    exchangeMap c '' thricePuncturedSphereReal = thricePuncturedSphereReal := by
  have h : thricePuncturedSphereReal = exchangeMap c ⁻¹' thricePuncturedSphereReal :=
    Set.ext fun y ↦ (exchangeMap_mem_iff hc₀ hc₁ y).symm
  conv_lhs => rw [h]
  exact Set.image_preimage_eq _ (surjective_exchangeMap (abs_le.2 ⟨by linarith, hc₁⟩))

/-- For `R ≥ 1`, `Φ_c` maps the truncation `S_R` of the pair of pants onto the truncation with
output end recentred at `c`. -/
private theorem image_exchangeMap_truncation (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {R : ℝ} (hR : 1 ≤ R) :
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
      have he : Complex.equivRealProdCLM.symm (y + (c, 0)) = w + c := by
        apply Complex.ext <;> simp [w]
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
private theorem exchangeMap_cylindricalEndLift (c : ℝ) {q : Puncture} (hq : q ≠ inf) {R : ℝ}
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
private theorem exchangeMap_cylindricalEndLift_inf (c : ℝ) {R : ℝ} (hR : 1 ≤ R) (t : ℝ) :
    exchangeMap c (Complex.equivRealProdCLM (inf.cylindricalEndLift (↑(-R) + t * Complex.I))) =
      Complex.equivRealProdCLM (c + inf.cylindricalEndLift (↑(-R) + t * Complex.I)) := by
  rw [exchangeMap_of_le_norm]
  · ext <;> simp [add_comm]
  · rw [ContinuousLinearEquiv.symm_apply_apply]
    have h := two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
      (z := ↑(-R) + ↑t * Complex.I) (by simpa using hR)
    rw [mul_one] at h
    linarith [fourteen_le_two_mul_exp_two_pi]

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : ℝ}

omit [FiniteDimensional ℝ V] in
private theorem differentiableAt_exchangePerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (c : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x v)
      x :=
  ((contDiffAt_uncurry_exchangePerturbation hH hHs c hz x v).comp x
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt one_ne_zero

omit [FiniteDimensional ℝ V] in
private theorem differentiableAt_exchangePerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (c : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun z ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x v)
      z :=
  ((contDiffAt_uncurry_exchangePerturbation hH hHs c hz x v).comp z
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt one_ne_zero

/-- The energy of `u` for `K_c` over the truncation with recentred output end is the energy of
`u ∘ Φ_c` for the pair-of-pants datum over the truncation `S_R`. -/
private theorem integral_floerEnergyDensity_exchangeTruncation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {R : ℝ}
    (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ exchangeMap c) z := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  have hS {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R) :
      exchangeMap c w ∈ thricePuncturedSphereReal :=
    (exchangeMap_mem_iff hc₀ hc₁ w).2 ⟨(mem_truncation.1 hw).1, (mem_truncation.1 hw).2.1⟩
  rw [← image_exchangeMap_truncation hc₀ hc₁ hR, integral_floerEnergyDensity_image ω
    ((isCompact_truncation R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
    (injective_exchangeMap hc).injOn
    (fun w _ ↦ (contDiff_exchangeMap c).differentiable two_ne_zero w)
    (fun w _ ↦ det_fderiv_exchangeMap_nonneg hc w)
    (fun w hw ↦ (hu.differentiableOn two_ne_zero _ (hS hw)).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw)))
    (fun w hw ↦ differentiableAt_exchangePerturbation_target hH hHs c (hS hw) _ _)
    (fun w hw ↦ differentiableAt_exchangePerturbation_target hH hHs c (hS hw) _ _),
    perturbationPullback_exchangeMap_stdComplexLineReal hc₀ hc₁,
    perturbationPullback_exchangeMap_stdComplexLineImag hc₀ hc₁]

/-- The integrated curvature of `K_c` along `u` is that of the pair-of-pants datum along
`u ∘ Φ_c`. -/
private theorem integral_hamiltonianCurvature_exchangePerturbation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) (u : ℝ × ℝ → V) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z ((u ∘ exchangeMap c) z) := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  have hS {w : ℝ × ℝ} (hw : w ∈ thricePuncturedSphereReal) :
      exchangeMap c w ∈ thricePuncturedSphereReal :=
    (exchangeMap_mem_iff hc₀ hc₁ w).2 hw
  conv_lhs => rw [← image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁]
  rw [integral_hamiltonianCurvature_image ω isOpen_thricePuncturedSphereReal.measurableSet
    (injective_exchangeMap hc).injOn (fun w _ ↦ (contDiff_exchangeMap c).contDiffAt)
    (fun w _ ↦ det_fderiv_exchangeMap_nonneg hc w)
    (fun w hw ↦ differentiableAt_exchangePerturbation_domain hH hHs c (hS hw) _ _)
    (fun w hw ↦ differentiableAt_exchangePerturbation_domain hH hHs c (hS hw) _ _),
    perturbationPullback_exchangeMap_stdComplexLineReal hc₀ hc₁,
    perturbationPullback_exchangeMap_stdComplexLineImag hc₀ hc₁]
  simp only [comp_apply]

/-- **The energy identity of the input-exchange family.** Let `K_c` be the member `c ∈ [0, 1]`
of the input-exchange family of period-one `C¹` Hamiltonians `H_q`, with components
`K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let
`u` be a map which is `C²` on `S = ℂ ∖ {0, 1}`. For `R ≥ 2`, the Floer energy of `u` over the
truncation of `S` with output end recentred at `c` is the change of action between the loops
`ℓ_q(t) = u(φ_q(R + i t))` along the boundary circles of the input ends and the loop
`ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` along the boundary circle of the recentred output end, minus the
integrated curvature over `S`:

`∫ E = A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞) - ∫_S R_{K_c}(u)`. -/
theorem integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hc : |c| ≤ 1 := abs_le.2 ⟨by linarith, hc₁⟩
  -- The map `u ∘ Φ_c` is `C²` on `S`, and the energy identity of the pair of pants applies to it.
  have hv : ContDiffOn ℝ 2 (u ∘ exchangeMap c) thricePuncturedSphereReal :=
    hu.comp (contDiff_exchangeMap c).contDiffOn fun w hw ↦ (exchangeMap_mem_iff hc₀ hc₁ w).2 hw
  have h := integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    ω hH hHs hv hR
  have hS : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} = thricePuncturedSphereReal :=
    Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  rw [hS] at h ⊢
  rw [← integral_floerEnergyDensity_exchangeTruncation_eq ω hH hHs hc₀ hc₁ hu (by linarith),
    ← integral_hamiltonianCurvature_exchangePerturbation_eq ω hH hHs hc₀ hc₁] at h
  rw [h]
  -- The boundary loops of `u ∘ Φ_c` are those of `u` on the recentred ends.
  simp only [Puncture.sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul,
    comp_apply, exchangeMap_cylindricalEndLift c (q := zero) (by decide) (by linarith : 0 ≤ R),
    exchangeMap_cylindricalEndLift c (q := one) (by decide) (by linarith : 0 ≤ R),
    exchangeMap_cylindricalEndLift_inf c (by linarith : (1 : ℝ) ≤ R)]
  ring

/-- **The energy and the actions along the input-exchange family.** If the end Hamiltonians are
bounded, `|H_q| ≤ B_q`, then for every `c ∈ [0, 1]` and `R ≥ 2` the Floer energy of `u` for the
member `c` of the family over the truncation with recentred output end differs from the change of
action `A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞)` of its boundary loops by at most
`B_0 + B_1 + B_∞`, uniformly in `c` and `R`. -/
theorem abs_integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      (ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  rw [integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation ω hH hHs hc₀ hc₁ hu hR,
    sub_sub_cancel_left, abs_neg]
  -- The curvature along `u` is the curvature of the pair-of-pants datum along `u ∘ Φ_c`.
  have hS : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} = thricePuncturedSphereReal :=
    Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  rw [hS, integral_hamiltonianCurvature_exchangePerturbation_eq ω hH hHs hc₀ hc₁]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB _ _

/-- **The one-sided action bound along the input-exchange family.** Let `u` be a map which is
`C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for the member
`c ∈ [0, 1]` of the input-exchange family, with almost complex structures `J(z)` tamed by `ω`, on
the truncation with recentred output end, `R ≥ 2`. If `h_q` are functions of time, integrable over
one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output end, then

`A_{H_∞}(ℓ^c_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - ∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞`

for the boundary loops `ℓ_q(t) = u(φ_q(R + i t))` and `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))`. The
constant does not depend on `c`. -/
theorem hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t := by
  -- The energy over the truncation is nonnegative.
  have hE := setIntegral_nonneg (μ := volume) ((isClosed_exchangeTruncation c R).preimage
    Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  -- The curvature along `u` is the curvature of the pair-of-pants datum along `u ∘ Φ_c`.
  have hv : ContDiffOn ℝ 2 (u ∘ exchangeMap c) thricePuncturedSphereReal :=
    hu.comp (contDiff_exchangeMap c).contDiffOn fun w hw ↦ (exchangeMap_mem_iff hc₀ hc₁ w).2 hw
  have hcurv := sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation
    ω hH hHs hh hhH hv.continuousOn
  have hS : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} = thricePuncturedSphereReal :=
    Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  rw [hS, ← integral_hamiltonianCurvature_exchangePerturbation_eq ω hH hHs hc₀ hc₁] at hcurv
  rw [integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation ω hH hHs hc₀ hc₁ hu hR,
    hS] at hE
  linarith

/-- **The action bound along the input-exchange family.** Let `K_c` be the member `c ∈ [0, 1]`
of the input-exchange family of period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `u`
be a map which is `C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for
`K_c` on the truncation with recentred output end, `R ≥ 2`, for almost complex structures `J(z)`
tamed by `ω`. Then the action of the output loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` is at most the
sum of the actions of the input loops `ℓ_q(t) = u(φ_q(R + i t))` plus `B_0 + B_1 + B_∞`:

`A_{H_∞}(ℓ^c_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) + B_0 + B_1 + B_∞`,

uniformly in `c`. -/
theorem hamiltonianAction_le_add_add_sum_of_exchangePerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) + ∑ q, B q := by
  have h := hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation ω hH hHs
    (h := fun q _ ↦ -(q.endSign * B q)) (fun _ ↦ intervalIntegrable_const)
    (endSign_mul_neg_endSign_mul_le hB) hc₀ hc₁ hu hR hJ hfloer
  rwa [sum_endSign_mul_integral_neg_endSign_mul, sub_neg_eq_add] at h

/-- **The one-sided action bound for the limiting actions along the input-exchange family.**
Let `u` be a map which is `C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation for the member
`c ∈ [0, 1]` of the input-exchange family on `S`, for almost complex structures `J(z)` tamed by
`ω`. If the actions of the input loops `ℓ_q(t) = u(φ_q(R + i t))` and of the output loop
`ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` converge to `a_q` as `R → ∞`, and `h_q` are functions of time,
integrable over one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output end,
then

`a_∞ ≤ a_0 + a_1 - ∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞`. -/
theorem le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    a inf ≤ a zero + a one - ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t := by
  exact le_of_tendsto_of_tendsto ha ((ha₀.add ha₁).sub_const _) <| eventually_atTop.2
    ⟨2, fun R hR ↦ hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation ω hH hHs hh hhH
      hc₀ hc₁ hu hR (fun z hz ↦ hJ z (exchangeTruncation_subset c R hz))
      fun z hz ↦ hfloer z (exchangeTruncation_subset c R hz)⟩

/-- **The action bound for the limiting actions along the input-exchange family.** Under the
hypotheses of `SymplecticForm.le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation`,
if moreover `|H_q| ≤ B_q`, then the limiting action of the recentred output end is at most the sum
of the limiting actions of the input ends plus `B_0 + B_1 + B_∞`:

`a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞`,

uniformly in `c ∈ [0, 1]`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    a inf ≤ a zero + a one + ∑ q, B q := by
  have h := le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation ω hH hHs
    (h := fun q _ ↦ -(q.endSign * B q)) (fun _ ↦ intervalIntegrable_const)
    (endSign_mul_neg_endSign_mul_le hB) hc₀ hc₁ hu hJ hfloer ha₀ ha₁ ha
  rwa [sum_endSign_mul_integral_neg_endSign_mul, sub_neg_eq_add] at h

end SymplecticForm

end TauCeti
