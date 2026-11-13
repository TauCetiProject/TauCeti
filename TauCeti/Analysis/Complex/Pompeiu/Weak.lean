/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Weyl
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Complex.CauchyKernel
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The Cauchy transform of integrable data

The normalized Cauchy transform `TauCeti.cauchyTransform f w = π⁻¹ ∫ z, (w - z)⁻¹ • f z` is a
right inverse of `bar∂ = (∂ₛ + i ∂ₜ) / 2` on compactly supported `C¹` data
(`HasCompactSupport.conjWirtingerDeriv_cauchyTransform`). This file extends the identity
`bar∂ (T f) = f` to every integrable `f`, in particular to every compactly supported `Lᵖ` map with
`1 ≤ p ≤ ∞`, as a distributional equation on every open subset of the plane
(`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform`). Such data is too rough for the classical
derivative of `T f` to exist, and the equation is the one tested against smooth compactly
supported functions, `TauCeti.HasWeakConjWirtingerDerivOn`.

The proof is Fubini's theorem. The reciprocal kernel is integrable over any set `s` of finite
measure uniformly in its pole: `∫_s |w - z|⁻¹ dw ≤ 2π + |s|`, by comparison with its integral
`2π` over the unit disc about the pole and with `1` outside that disc
(`TauCeti.setLIntegral_enorm_sub_inv_le`). Hence `(w, z) ↦ (w - z)⁻¹ • f z` is integrable on
`s × ℂ`, so `T f` is locally integrable (`TauCeti.locallyIntegrable_cauchyTransform`), and against
a test function `φ` the order of integration may be exchanged:

`∫ (bar∂ φ) (T f) = ∫ z, (π⁻¹ ∫ w, (w - z)⁻¹ bar∂ φ w) f z = -∫ φ f`,

the inner integral being `-φ z` by the left-inverse identity
`HasCompactSupport.cauchyTransform_conjWirtingerDeriv` for the smooth compactly supported `φ`.

Combined with Weyl's lemma for `bar∂`, every distributional solution of `bar∂ u = f` with
integrable `f` and finite-dimensional coefficients is `T f` plus a holomorphic function, almost
everywhere on its domain
(`TauCeti.HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq_cauchyTransform_add`). This
is the representation through which interior regularity for `bar∂` is read off from the mapping
properties of the Cauchy transform.

## Main results

* `TauCeti.integrable_prod_sub_inv_smul`: integrability of the Cauchy kernel against integrable
  data on `s × ℂ`.
* `TauCeti.integrableOn_cauchyTransform` and `TauCeti.locallyIntegrable_cauchyTransform`: the
  Cauchy transform of integrable data is integrable on sets of finite measure.
* `TauCeti.integral_conjWirtingerDeriv_smul_cauchyTransform`: `∫ bar∂ψ • T f = -∫ ψ • f` for a
  compactly supported complex `C¹` function `ψ`.
* `TauCeti.integral_lineDeriv_smul_cauchyTransform_add_I_smul_eq_neg_two_smul_integral_smul`:
  its form against a compactly supported real `C¹` function.
* `TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform`: `bar∂ (T f) = f` distributionally, and
  `TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp` its form for compactly supported
  `Lᵖ` data.
* `TauCeti.integral_cauchyTransform_apply_conjWirtingerDeriv`: `∫ (T f) (bar∂ψ) = -∫ f ψ` for
  operator-valued `f` and a compactly supported vector-valued `C¹` map `ψ`. The scalar pairing
  `TauCeti.integral_conjWirtingerDeriv_smul_cauchyTransform` is its special case.
* `TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_apply`: the Leibniz rule
  `bar∂ ((T f) ξ) = f ξ + (T f) (bar∂ξ)` on `Ω` for operator-valued `f` and a map `ξ` of class
  `C¹` on `Ω`.
* `TauCeti.HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq_cauchyTransform_add`: every
  distributional solution on `Ω` of `bar∂ u = f` with integrable `f` and finite-dimensional
  coefficients agrees a.e. on `Ω` with `T f` plus a holomorphic function.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2 (the Cauchy transform on `Lᵖ` data).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.2.
-/

public noncomputable section

open MeasureTheory Complex Set Metric Function TopologicalSpace Filter
open scoped ENNReal NNReal Real

namespace TauCeti

variable {F V W : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The Cauchy kernel against integrable data, `(w, z) ↦ (w - z)⁻¹ • f z`, is integrable on
`s × ℂ` for every set `s` of finite measure. This is what licenses Fubini's theorem for the
Cauchy transform of rough data. -/
theorem integrable_prod_sub_inv_smul {f : ℂ → F} (hf : Integrable f) {s : Set ℂ}
    (hs : volume s ≠ ∞) :
    Integrable (fun q : ℂ × ℂ ↦ (q.1 - q.2)⁻¹ • f q.2) ((volume.restrict s).prod volume) := by
  have hm : AEStronglyMeasurable (fun q : ℂ × ℂ ↦ (q.1 - q.2)⁻¹ • f q.2)
      ((volume.restrict s).prod volume) :=
    (measurable_fst.sub measurable_snd).inv.aestronglyMeasurable.smul
      hf.aestronglyMeasurable.comp_snd
  refine ⟨hm, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hm.eNorm]
  have hC : ENNReal.ofReal (2 * π) + volume s ≠ ∞ := by finiteness
  calc ∫⁻ z, ∫⁻ w in s, ‖(w - z)⁻¹ • f z‖ₑ
      ≤ ∫⁻ z, (ENNReal.ofReal (2 * π) + volume s) * ‖f z‖ₑ := by
        refine lintegral_mono fun z ↦ ?_
        simp_rw [eNorm_smul]
        rw [lintegral_mul_const' _ _ eNorm_ne_top]
        gcongr
        exact setLIntegral_enorm_sub_inv_le s z
    _ = (ENNReal.ofReal (2 * π) + volume s) * ∫⁻ z, ‖f z‖ₑ := lintegral_const_mul' _ _ hC
    _ < ∞ := ENNReal.mul_lt_top hC.lt_top hf.2

/-- The Cauchy transform of integrable data is integrable on every set of finite measure. -/
theorem integrableOn_cauchyTransform {f : ℂ → F} (hf : Integrable f) {s : Set ℂ}
    (hs : volume s ≠ ∞) : IntegrableOn (cauchyTransform f) s := by
  have h : cauchyTransform f = (π : ℂ)⁻¹ • fun w ↦ ∫ z, (w - z)⁻¹ • f z :=
    funext (cauchyTransform_apply f)
  rw [IntegrableOn, h]
  exact Integrable.smul ((π : ℂ)⁻¹) (integrable_prod_sub_inv_smul hf hs).integral_prod_left

/-- The Cauchy transform of integrable data is locally integrable. -/
theorem locallyIntegrable_cauchyTransform {f : ℂ → F} (hf : Integrable f) :
    LocallyIntegrable (cauchyTransform f) :=
  locallyIntegrable_iff.2 fun _ hk ↦ integrableOn_cauchyTransform hf hk.measure_lt_top.ne


/-- The transposed Cauchy kernel against `bar∂ ψ` returns `-π ψ`, for a compactly supported `C¹`
map `ψ` into a complex Banach space. -/
private theorem integral_sub_inv_smul_conjWirtingerDeriv [CompleteSpace V] {ψ : ℂ → V}
    (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ 1 ψ) (z : ℂ) :
    ∫ w, (w - z)⁻¹ • conjWirtingerDeriv ψ w 1 = -((π : ℂ) • ψ z) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := hc.cauchyTransform_conjWirtingerDeriv hψ z
  rw [cauchyTransform_apply, inv_smul_eq_iff₀ hπ] at h
  rw [← h, ← integral_neg]
  congr 1 with w
  rw [← neg_sub z w, inv_neg, neg_smul]

/-- **Integration by parts against an operator-valued Cauchy transform.** For integrable `f` with
values in continuous complex-linear maps and a compactly supported `C¹` map `ψ`,
`∫ (T f) (bar∂ ψ) = -∫ f ψ`. This is the weak form of `bar∂ (T f) = f` tested against vector
valued test maps, through the bilinear pairing of an operator with a vector. -/
theorem integral_cauchyTransform_apply_conjWirtingerDeriv [CompleteSpace V] [CompleteSpace W]
    {f : ℂ → V →L[ℂ] W} (hf : Integrable f) {ψ : ℂ → V} (hc : HasCompactSupport ψ)
    (hψ : ContDiff ℝ 1 ψ) :
    ∫ w, cauchyTransform f w (conjWirtingerDeriv ψ w 1) = -∫ z, f z (ψ z) := by
  set g : ℂ → V := fun w ↦ conjWirtingerDeriv ψ w 1 with hg_def
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg : Continuous g := hψ.continuous_conjWirtingerDeriv_apply 1
  have hgK (w : ℂ) (hw : w ∉ tsupport ψ) : g w = 0 := by
    simp [hg_def, conjWirtingerDeriv_of_notMem_tsupport hw]
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support
    (hc.mono' fun w hw ↦ by_contra fun h ↦ hw (hgK w h))
  set K := tsupport ψ
  have hK : volume K ≠ ⊤ := hc.isCompact.measure_lt_top.ne
  have hP := integrable_prod_sub_inv_smul hf hK
  have hint : Integrable (fun q : ℂ × ℂ ↦ ((q.1 - q.2)⁻¹ • f q.2) (g q.1))
      ((volume.restrict K).prod volume) := by
    refine Integrable.mono' (hP.norm.mul_const C) ?_
      (Eventually.of_forall fun q ↦ ContinuousLinearMap.le_opNorm_of_le _ (hC q.1))
    simpa using (ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂
      hP.aestronglyMeasurable hg.aestronglyMeasurable.comp_fst
  have hgi (z : ℂ) : Integrable (fun w ↦ (w - z)⁻¹ • g w) (volume.restrict K) := by
    have hk : IntegrableOn (fun w : ℂ ↦ (w - z)⁻¹) K :=
      ((locallyIntegrable_sub_inv z).integrableOn_isCompact hc.isCompact).neg.congr_fun
        (fun w _ ↦ by rw [Pi.neg_apply, ← inv_neg, neg_sub]) hc.isCompact.measurableSet
    exact hk.smul_of_top_left (memLp_top_of_bound hg.aestronglyMeasurable C (ae_of_all _ hC))
  calc ∫ w, cauchyTransform f w (g w)
      = ∫ w in K, cauchyTransform f w (g w) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by rw [hgK w hw, map_zero]).symm
    _ = ∫ w in K, (π : ℂ)⁻¹ • ∫ z, ((w - z)⁻¹ • f z) (g w) := by
        refine integral_congr_ae ?_
        filter_upwards [hP.prod_right_ae] with w hw
        rw [cauchyTransform_apply, smul_apply,
          ContinuousLinearMap.integral_apply hw]
    _ = (π : ℂ)⁻¹ • ∫ z, ∫ w in K, ((w - z)⁻¹ • f z) (g w) := by
        rw [integral_smul, integral_integral_swap hint]
    _ = (π : ℂ)⁻¹ • ∫ z, f z (-((π : ℂ) • ψ z)) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        simp only [smul_apply, ← (f z).map_smul]
        rw [(f z).integral_comp_comm (hgi z), setIntegral_eq_integral_of_forall_compl_eq_zero
          fun w hw ↦ by rw [hgK w hw, smul_zero], integral_sub_inv_smul_conjWirtingerDeriv hc hψ]
    _ = -∫ z, f z (ψ z) := by
        simp only [map_neg, map_smul, integral_neg, integral_smul, smul_neg, inv_smul_smul₀ hπ]

/-- The pairing of the Cauchy transform of integrable data with `bar∂` of a compactly supported
complex `C¹` function `ψ` is `-∫ ψ f`: the weak form of `bar∂ (T f) = f` against complex test
functions. -/
theorem integral_conjWirtingerDeriv_smul_cauchyTransform [CompleteSpace F] {f : ℂ → F}
    (hf : Integrable f) {ψ : ℂ → ℂ} (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ 1 ψ) :
    ∫ w, conjWirtingerDeriv ψ w 1 • cauchyTransform f w = -∫ z, ψ z • f z := by
  -- this is the operator-valued pairing for the maps `a ↦ a • f z`
  let L : F ≃L[ℂ] (ℂ →L[ℂ] F) := ContinuousLinearMap.toSpanSingletonCLE
  have hT (w : ℂ) : cauchyTransform (fun z ↦ L (f z)) w = L (cauchyTransform f w) := by
    simp only [cauchyTransform_apply, ← map_smul, L.integral_comp_comm]
  have h := integral_cauchyTransform_apply_conjWirtingerDeriv (L.integrable_comp_iff.2 hf) hc hψ
  simp only [hT] at h
  simpa only [L, ContinuousLinearMap.toSpanSingletonCLE_apply_apply] using h

/-- **Integration by parts against the Cauchy transform.** For integrable `f` and a compactly
supported real `C¹` function `φ`,
`∫ ∂ₛφ • T f + i ∫ ∂ₜφ • T f = -2 ∫ φ • f`, the weak form of `bar∂ (T f) = f`. -/
theorem integral_lineDeriv_smul_cauchyTransform_add_I_smul_eq_neg_two_smul_integral_smul
    [CompleteSpace F] {f : ℂ → F} (hf : Integrable f) {φ : ℂ → ℝ} (hc : HasCompactSupport φ)
    (hφ : ContDiff ℝ 1 φ) :
    (∫ w, lineDeriv ℝ φ w 1 • cauchyTransform f w) +
        I • (∫ w, lineDeriv ℝ φ w I • cauchyTransform f w) =
      -(2 : ℂ) • ∫ z, φ z • f z := by
  set ψ : ℂ → ℂ := fun z ↦ (φ z : ℂ)
  have hψ : ContDiff ℝ 1 ψ := ofRealCLM.contDiff.comp hφ
  have hψc : HasCompactSupport ψ := hc.comp_left ofReal_zero
  have hd (w : ℂ) (v : ℂ) : fderiv ℝ ψ w v = ((lineDeriv ℝ φ w v : ℝ) : ℂ) := by
    rw [fderiv_ofReal_comp_apply, (hφ.differentiable one_ne_zero w).lineDeriv_eq_fderiv]
  have hi (v : ℂ) : Integrable fun w ↦ ((lineDeriv ℝ φ w v : ℝ) : ℂ) • cauchyTransform f w := by
    refine (locallyIntegrable_cauchyTransform hf).integrable_smul_left_of_hasCompactSupport ?_ ?_
    · simp_rw [← hd]
      exact ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    · simp_rw [← hd]
      exact (hψc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ ↦ L v) rfl
  have hconj (w : ℂ) : conjWirtingerDeriv ψ w 1 =
      (2 : ℂ)⁻¹ * (((lineDeriv ℝ φ w 1 : ℝ) : ℂ) + I * ((lineDeriv ℝ φ w I : ℝ) : ℂ)) := by
    rw [conjWirtingerDeriv_ofReal_comp_apply_eq_lineDeriv (hφ.differentiable one_ne_zero w),
      smul_eq_mul, mul_one]
  simp_rw [← Complex.coe_smul]
  have hI : Integrable fun w ↦ I • ((lineDeriv ℝ φ w I : ℝ) : ℂ) • cauchyTransform f w :=
    (hi I).smul I
  rw [← integral_smul, ← integral_add (hi 1) hI]
  calc ∫ w, (((lineDeriv ℝ φ w 1 : ℝ) : ℂ) • cauchyTransform f w +
        I • ((lineDeriv ℝ φ w I : ℝ) : ℂ) • cauchyTransform f w)
      = ∫ w, (2 : ℂ) • (conjWirtingerDeriv ψ w 1 • cauchyTransform f w) := by
        congr 1 with w
        rw [hconj, smul_smul (2 : ℂ), ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul, add_smul,
          mul_smul]
    _ = -(2 : ℂ) • ∫ z, (φ z : ℂ) • f z := by
        rw [integral_smul, integral_conjWirtingerDeriv_smul_cauchyTransform hf hψc hψ, smul_neg,
          neg_smul]

/-- **`bar∂ (T f) = f` for integrable data.** The Cauchy transform of an integrable map into a
complex Banach space solves the Cauchy–Riemann equation `bar∂ (T f) = f` in the distributional
sense on every open subset of the plane. -/
theorem hasWeakConjWirtingerDerivOn_cauchyTransform [CompleteSpace F] {f : ℂ → F}
    (hf : Integrable f) (Ω : Opens ℂ) :
    HasWeakConjWirtingerDerivOn volume Ω (cauchyTransform f) f :=
  hasWeakConjWirtingerDerivOn_iff.2 ⟨inferInstance,
    (locallyIntegrable_cauchyTransform hf).locallyIntegrableOn _,
    hf.locallyIntegrable.locallyIntegrableOn _, fun φ ↦
      integral_lineDeriv_smul_cauchyTransform_add_I_smul_eq_neg_two_smul_integral_smul hf
        φ.hasCompactSupport (φ.contDiff.of_le (by simp))⟩

/-- **`bar∂ (T f) = f` for compactly supported `Lᵖ` data.** For `1 ≤ p ≤ ∞` and `f` in `Lᵖ` with
support in a closed disc, the Cauchy transform solves `bar∂ (T f) = f` distributionally on every
open subset of the plane. -/
theorem hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp [CompleteSpace F] {f : ℂ → F}
    {c : ℂ} {r : ℝ≥0} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p (volume.restrict (closedBall c (r : ℝ))))
    (hs : support f ⊆ closedBall c (r : ℝ)) (Ω : Opens ℂ) :
    HasWeakConjWirtingerDerivOn volume Ω (cauchyTransform f) f := by
  have : IsFiniteMeasure (volume.restrict (closedBall c (r : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h : Integrable ((closedBall c (r : ℝ)).indicator f) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hf.integrable hp)
  rw [indicator_eq_self.2 hs] at h
  exact hasWeakConjWirtingerDerivOn_cauchyTransform h Ω

/-- The conjugate Wirtinger derivative of the test map `φ ξ`, for a real `C¹` function `φ` whose
topological support lies in an open set on which `ξ` is `C¹`, is `φ bar∂ξ + (bar∂φ) ξ` with
`bar∂φ` written through the directional derivatives of `φ`. Both sides vanish off the support
of `φ`, so the identity holds on the whole plane. -/
private theorem conjWirtingerDeriv_ofReal_smul_apply_one {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφΩ : tsupport φ ⊆ Ω) {ξ : ℂ → V}
    (hξ : ContDiffOn ℝ 1 ξ Ω) (z : ℂ) :
    conjWirtingerDeriv (fun z ↦ (φ z : ℂ) • ξ z) z 1 = (φ z : ℂ) • conjWirtingerDeriv ξ z 1 +
      ((2 : ℂ)⁻¹ * (((lineDeriv ℝ φ z 1 : ℝ) : ℂ) + I * ((lineDeriv ℝ φ z I : ℝ) : ℂ))) • ξ z := by
  have hφz := hφ.differentiable one_ne_zero z
  by_cases hz : z ∈ Ω
  · rw [conjWirtingerDeriv_smul_apply hφz.ofReal_comp
      ((hξ.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz)),
      conjWirtingerDeriv_ofReal_comp_apply_eq_lineDeriv hφz, smul_eq_mul, mul_one]
  · have hz' : z ∉ tsupport φ := fun h ↦ hz (hφΩ h)
    have hzψ : z ∉ tsupport fun z ↦ (φ z : ℂ) • ξ z := fun h ↦
      hz' (tsupport_comp_subset ofReal_zero φ (tsupport_smul_subset_left _ _ h))
    rw [conjWirtingerDeriv_of_notMem_tsupport hzψ]
    simp [image_eq_zero_of_notMem_tsupport hz', hφz.lineDeriv_eq_fderiv,
      fderiv_of_notMem_tsupport ℝ hz']

/-- The pointwise identity behind the Leibniz rule: against a continuous linear map `A`,
`∂ₛφ • A ξ + i ∂ₜφ • A ξ = 2 A (bar∂ (φ ξ)) - 2 φ A (bar∂ξ)`. -/
private theorem lineDeriv_smul_add_I_smul_lineDeriv_smul_eq {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφΩ : tsupport φ ⊆ Ω) {ξ : ℂ → V}
    (hξ : ContDiffOn ℝ 1 ξ Ω) (A : V →L[ℂ] W) (z : ℂ) :
    lineDeriv ℝ φ z 1 • A (ξ z) + I • lineDeriv ℝ φ z I • A (ξ z) =
      (2 : ℂ) • A (conjWirtingerDeriv (fun z ↦ (φ z : ℂ) • ξ z) z 1) -
        (2 : ℂ) • (φ z • A (conjWirtingerDeriv ξ z 1)) := by
  rw [conjWirtingerDeriv_ofReal_smul_apply_one hΩ hφ hφΩ hξ z, map_add, map_smul, map_smul]
  simp_rw [← Complex.coe_smul]
  module

/-- **The Leibniz rule for a Cauchy transform applied to a `C¹` map.** For integrable `f` with
values in continuous complex-linear maps and a map `ξ` of class `C¹` on an open set `Ω`, the map
`z ↦ (T f z) (ξ z)` has weak conjugate Wirtinger derivative `f ξ + (T f) (bar∂ ξ)` on `Ω`. Only
the weak `bar∂`-derivative `f` of `T f` enters, not its full weak derivative. -/
theorem hasWeakConjWirtingerDerivOn_cauchyTransform_apply [CompleteSpace V] [CompleteSpace W]
    {f : ℂ → V →L[ℂ] W} (hf : Integrable f) {Ω : Opens ℂ} {ξ : ℂ → V}
    (hξ : ContDiffOn ℝ 1 ξ Ω) :
    HasWeakConjWirtingerDerivOn volume Ω (fun z ↦ cauchyTransform f z (ξ z))
      (fun z ↦ f z (ξ z) + cauchyTransform f z (conjWirtingerDeriv ξ z 1)) := by
  have hΩ := Ω.isOpen.isLocallyClosed
  have hT := (locallyIntegrable_cauchyTransform hf).locallyIntegrableOn (Ω : Set ℂ)
  have hu := hT.clm_apply_continuousOn hΩ hξ.continuousOn
  have hfξ := (hf.locallyIntegrable.locallyIntegrableOn (Ω : Set ℂ)).clm_apply_continuousOn hΩ
    hξ.continuousOn
  have hTd := hT.clm_apply_continuousOn hΩ
    (hξ.conjWirtingerDeriv_apply_of_isOpen (m := 0) Ω.isOpen (by simp) 1).continuousOn
  refine hasWeakConjWirtingerDerivOn_iff.2 ⟨inferInstance, hu, hfξ.add hTd, fun φ ↦ ?_⟩
  -- the test map `ψ = φ ξ` is `C¹` on the whole plane, with compact support in `Ω`
  have hφ : ContDiff ℝ 1 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  set ψ : ℂ → V := fun z ↦ ((φ : ℂ → ℝ) z : ℂ) • ξ z with hψ_def
  have hφΩ : tsupport (fun z ↦ ((φ : ℂ → ℝ) z : ℂ)) ⊆ Ω :=
    (tsupport_comp_subset ofReal_zero _).trans φ.tsupport_subset
  have hψ : ContDiff ℝ 1 ψ := by
    simpa only [hψ_def, Complex.coe_smul] using
      hξ.contDiff_smul_of_tsupport_subset Ω.isOpen hφ.contDiffOn φ.tsupport_subset
  have hψc : HasCompactSupport ψ := (φ.hasCompactSupport.comp_left ofReal_zero).smul_right
  have hi1 := integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ 1
  have hiI := integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ I
  have hiψ : Integrable fun z ↦ cauchyTransform f z (conjWirtingerDeriv ψ z 1) :=
    ((hT.clm_apply_continuousOn hΩ (hψ.continuous_conjWirtingerDeriv_apply 1).continuousOn
      ).integrableOn_compact_subset ((tsupport_smul_subset_left _ _).trans hφΩ) hψc.isCompact
      ).integrable_of_forall_notMem_eq_zero fun z hz ↦ by
        rw [conjWirtingerDeriv_of_notMem_tsupport hz, zero_apply, map_zero]
  have hiφ := φ.integrable_smul hTd
  have hiφ' := φ.integrable_smul hfξ
  have hfψ : ∫ z, f z (ψ z) = ∫ z, (φ : ℂ → ℝ) z • f z (ξ z) := by
    congr 1 with z
    rw [hψ_def, map_smul, ← Complex.coe_smul]
  calc (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • cauchyTransform f z (ξ z)) +
        I • ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • cauchyTransform f z (ξ z)
      = ∫ z, ((2 : ℂ) • cauchyTransform f z (conjWirtingerDeriv ψ z 1) -
          (2 : ℂ) • ((φ : ℂ → ℝ) z • cauchyTransform f z (conjWirtingerDeriv ξ z 1))) := by
        have hiI' : Integrable fun z ↦
            I • lineDeriv ℝ (φ : ℂ → ℝ) z I • cauchyTransform f z (ξ z) := hiI.smul I
        rw [← integral_smul, ← integral_add hi1 hiI']
        exact integral_congr_ae (Eventually.of_forall fun z ↦
          lineDeriv_smul_add_I_smul_lineDeriv_smul_eq Ω.isOpen hφ φ.tsupport_subset hξ _ z)
    _ = -(2 : ℂ) • ∫ z, (φ : ℂ → ℝ) z • (f z (ξ z) +
          cauchyTransform f z (conjWirtingerDeriv ξ z 1)) := by
        have h1 : Integrable fun z ↦ (2 : ℂ) • cauchyTransform f z (conjWirtingerDeriv ψ z 1) :=
          hiψ.smul _
        have h2 : Integrable fun z ↦
            (2 : ℂ) • ((φ : ℂ → ℝ) z • cauchyTransform f z (conjWirtingerDeriv ξ z 1)) :=
          hiφ.smul _
        rw [integral_sub h1 h2, integral_smul, integral_smul,
          integral_cauchyTransform_apply_conjWirtingerDeriv hf hψc hψ, hfψ]
        simp only [smul_add]
        rw [integral_add hiφ' hiφ]
        module


/-- **Representation of weak solutions of `bar∂ u = f`.** A distributional solution of
`bar∂ u = f` on `Ω`, with integrable `f` and finite-dimensional complex coefficients, agrees almost
everywhere on `Ω` with the Cauchy transform of `f` plus a holomorphic function. -/
theorem HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq_cauchyTransform_add
    [FiniteDimensional ℂ F] {Ω : Opens ℂ} {u f : ℂ → F}
    (hu : HasWeakConjWirtingerDerivOn volume Ω u f) (hf : Integrable f) :
    ∃ v : ℂ → F, DifferentiableOn ℂ v Ω ∧ u =ᵐ[volume.restrict Ω] cauchyTransform f + v := by
  have := FiniteDimensional.completeSpace ℂ F
  have h := hu.sub (hasWeakConjWirtingerDerivOn_cauchyTransform hf Ω)
  rw [sub_self] at h
  obtain ⟨v, hv, huv⟩ := h.exists_differentiableOn_ae_eq
  refine ⟨v, hv, huv.mono fun z hz ↦ ?_⟩
  rw [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel]

end TauCeti
