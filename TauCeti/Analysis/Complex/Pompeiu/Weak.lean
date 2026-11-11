/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Weyl
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Complex.CauchyKernel

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
  operator-valued `f` and a compactly supported vector-valued `C¹` map `ψ`.
* `TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_apply`: the Leibniz rule
  `bar∂ ((T f) ξ) = f ξ + (T f) (bar∂ξ)` for operator-valued `f` and a `C¹` map `ξ`.
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

open MeasureTheory Complex Set Metric Function TopologicalSpace
open scoped ENNReal NNReal Real

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

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
  rw [HasFiniteIntegral, lintegral_prod_symm _ hm.enorm]
  have hC : ENNReal.ofReal (2 * π) + volume s ≠ ∞ := by finiteness
  calc ∫⁻ z, ∫⁻ w in s, ‖(w - z)⁻¹ • f z‖ₑ
      ≤ ∫⁻ z, (ENNReal.ofReal (2 * π) + volume s) * ‖f z‖ₑ := by
        refine lintegral_mono fun z ↦ ?_
        simp_rw [enorm_smul]
        rw [lintegral_mul_const' _ _ enorm_ne_top]
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

/-- For a compactly supported `C¹` map `ψ`, the transposed Cauchy kernel against `bar∂ ψ` returns
`-π ψ`: this is the left-inverse identity `T (bar∂ ψ) = ψ` with the kernel `(w - z)⁻¹` in place of
`(z - w)⁻¹`. -/
private theorem integral_conjWirtingerDeriv_mul_sub_inv {ψ : ℂ → ℂ} (hc : HasCompactSupport ψ)
    (hψ : ContDiff ℝ 1 ψ) (z : ℂ) :
    ∫ w, conjWirtingerDeriv ψ w 1 * (w - z)⁻¹ = -((π : ℂ) * ψ z) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := hc.cauchyTransform_conjWirtingerDeriv hψ z
  rw [cauchyTransform_apply, inv_smul_eq_iff₀ hπ, smul_eq_mul] at h
  rw [← h, ← integral_neg]
  congr 1 with w
  rw [smul_eq_mul, ← neg_sub z w, inv_neg, mul_neg, mul_comm]

/-- The pairing of the Cauchy transform of integrable data with `bar∂` of a compactly supported
complex `C¹` function `ψ` is `-∫ ψ f`: the weak form of `bar∂ (T f) = f` against complex test
functions. -/
theorem integral_conjWirtingerDeriv_smul_cauchyTransform [CompleteSpace F] {f : ℂ → F}
    (hf : Integrable f) {ψ : ℂ → ℂ} (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ 1 ψ) :
    ∫ w, conjWirtingerDeriv ψ w 1 • cauchyTransform f w = -∫ z, ψ z • f z := by
  set g : ℂ → ℂ := fun w ↦ conjWirtingerDeriv ψ w 1 with hg_def
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg : Continuous g := by
    simp only [hg_def, conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
    have hd := hψ.continuous_fderiv one_ne_zero
    fun_prop
  have hgK (w : ℂ) (hw : w ∉ tsupport ψ) : g w = 0 := by
    simp [hg_def, conjWirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hw]
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support
    (hc.mono' fun w hw ↦ by_contra fun h ↦ hw (hgK w h))
  have hK : volume (tsupport ψ) ≠ ∞ := hc.isCompact.measure_lt_top.ne
  have hint : Integrable (uncurry fun w z ↦ g w • ((w - z)⁻¹ • f z))
      ((volume.restrict (tsupport ψ)).prod volume) :=
    (integrable_prod_sub_inv_smul hf hK).bdd_smul C
      (hg.aestronglyMeasurable.comp_fst) (Filter.Eventually.of_forall fun q ↦ hC q.1)
  calc ∫ w, g w • cauchyTransform f w
      = ∫ w in tsupport ψ, g w • cauchyTransform f w := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ ?_).symm
        rw [hgK w hw, zero_smul]
    _ = (π : ℂ)⁻¹ • ∫ w in tsupport ψ, ∫ z, g w • ((w - z)⁻¹ • f z) := by
        rw [← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
        dsimp only
        rw [cauchyTransform_apply, integral_smul, smul_comm]
    _ = (π : ℂ)⁻¹ • ∫ z, ∫ w in tsupport ψ, g w • ((w - z)⁻¹ • f z) := by
        rw [integral_integral_swap hint]
    _ = (π : ℂ)⁻¹ • ∫ z, (-((π : ℂ) * ψ z)) • f z := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
        simp only [smul_smul]
        rw [integral_smul_const, setIntegral_eq_integral_of_forall_compl_eq_zero
          fun w hw ↦ by rw [hgK w hw, zero_mul],
          integral_conjWirtingerDeriv_mul_sub_inv hc hψ z]
    _ = -∫ z, ψ z • f z := by
        simp only [neg_smul, integral_neg, smul_neg, ← smul_smul, integral_smul,
          inv_smul_smul₀ hπ]

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
    simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, hd]
  have hreal (r : ℝ) (v : F) : r • v = (r : ℂ) • v := RCLike.real_smul_eq_coe_smul (K := ℂ) r v
  simp_rw [hreal]
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

section Operator

open Filter
open scoped ContDiff Distributions

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Applying a locally integrable family of continuous linear maps to a continuous map gives a
locally integrable map. -/
private theorem locallyIntegrable_clm_apply {L : ℂ → V →L[ℂ] W} (hL : LocallyIntegrable L)
    {u : ℂ → V} (hu : Continuous u) : LocallyIntegrable fun z ↦ L z (u z) := by
  refine locallyIntegrable_iff.2 fun k hk ↦ ?_
  obtain ⟨B, hB⟩ := hk.exists_bound_of_continuousOn hu.continuousOn
  have hLk := hL.integrableOn_isCompact hk
  refine Integrable.mono' (hLk.norm.mul_const B) ?_
    ((ae_restrict_iff' hk.measurableSet).2 (Eventually.of_forall fun z hz ↦
      (L z).le_opNorm_of_le (hB z hz)))
  simpa using (ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂
    hLk.aestronglyMeasurable hu.aestronglyMeasurable

/-- The conjugate Wirtinger derivative of a `C¹` map, in a fixed direction, is continuous. -/
private theorem continuous_conjWirtingerDeriv_apply {ψ : ℂ → V} (hψ : ContDiff ℝ 1 ψ) (v : ℂ) :
    Continuous fun w ↦ conjWirtingerDeriv ψ w v := by
  simp only [conjWirtingerDeriv_apply]
  have hd := hψ.continuous_fderiv one_ne_zero
  fun_prop

/-- The conjugate Wirtinger derivative of a map vanishes off its topological support. -/
private theorem conjWirtingerDeriv_apply_of_notMem_tsupport {ψ : ℂ → V} {w : ℂ}
    (hw : w ∉ tsupport ψ) (v : ℂ) : conjWirtingerDeriv ψ w v = 0 := by
  simp [conjWirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hw]

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
  have hg : Continuous g := continuous_conjWirtingerDeriv_apply hψ 1
  have hgK (w : ℂ) (hw : w ∉ tsupport ψ) : g w = 0 :=
    conjWirtingerDeriv_apply_of_notMem_tsupport hw 1
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

/-- **The Leibniz rule for a Cauchy transform applied to a `C¹` map.** For integrable `f` with
values in continuous complex-linear maps and a `C¹` map `ξ`, the map `z ↦ (T f z) (ξ z)` has weak
conjugate Wirtinger derivative `f ξ + (T f) (bar∂ ξ)` on every open set. Only the weak
`bar∂`-derivative `f` of `T f` enters, not its full weak derivative. -/
theorem hasWeakConjWirtingerDerivOn_cauchyTransform_apply [CompleteSpace V] [CompleteSpace W]
    {f : ℂ → V →L[ℂ] W} (hf : Integrable f) {ξ : ℂ → V} (hξ : ContDiff ℝ 1 ξ) (Ω : Opens ℂ) :
    HasWeakConjWirtingerDerivOn volume Ω (fun z ↦ cauchyTransform f z (ξ z))
      (fun z ↦ f z (ξ z) + cauchyTransform f z (conjWirtingerDeriv ξ z 1)) := by
  have hT := locallyIntegrable_cauchyTransform hf
  have hdξ := continuous_conjWirtingerDeriv_apply hξ 1
  have hu := locallyIntegrable_clm_apply hT hξ.continuous
  have hfξ := locallyIntegrable_clm_apply hf.locallyIntegrable hξ.continuous
  have hTd := locallyIntegrable_clm_apply hT hdξ
  refine hasWeakConjWirtingerDerivOn_iff.2 ⟨inferInstance, hu.locallyIntegrableOn _,
    (hfξ.add hTd).locallyIntegrableOn _, fun φ ↦ ?_⟩
  -- the test map `ψ = φ ξ`, whose `bar∂` is `φ bar∂ξ + (bar∂φ) ξ`
  set ψ : ℂ → V := fun z ↦ ((φ : ℂ → ℝ) z : ℂ) • ξ z with hψ_def
  have hφ : ContDiff ℝ 1 (fun z ↦ ((φ : ℂ → ℝ) z : ℂ)) :=
    ofRealCLM.contDiff.comp (φ.contDiff.of_le (by simp))
  have hψ : ContDiff ℝ 1 ψ := hφ.smul hξ
  have hψc : HasCompactSupport ψ := (φ.hasCompactSupport.comp_left ofReal_zero).smul_right
  have hφ₁ : ContDiff ℝ 1 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hd (w v : ℂ) : fderiv ℝ (fun z ↦ ((φ : ℂ → ℝ) z : ℂ)) w v =
      ((lineDeriv ℝ (φ : ℂ → ℝ) w v : ℝ) : ℂ) := by
    rw [fderiv_ofReal_comp_apply, (hφ₁.differentiable one_ne_zero w).lineDeriv_eq_fderiv]
  have hdψ (z : ℂ) : conjWirtingerDeriv ψ z 1 = ((φ : ℂ → ℝ) z : ℂ) • conjWirtingerDeriv ξ z 1 +
      ((2 : ℂ)⁻¹ * (((lineDeriv ℝ (φ : ℂ → ℝ) z 1 : ℝ) : ℂ) +
        I * ((lineDeriv ℝ (φ : ℂ → ℝ) z I : ℝ) : ℂ))) • ξ z := by
    rw [conjWirtingerDeriv_smul_apply (hφ.differentiable one_ne_zero z)
      (hξ.differentiable one_ne_zero z)]
    simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, hd]
  have hreal (r : ℝ) (v : W) : r • v = (r : ℂ) • v := RCLike.real_smul_eq_coe_smul (K := ℂ) r v
  have hi1 := integrable_lineDeriv_smul_of_locallyIntegrableOn (hu.locallyIntegrableOn Ω) φ 1
  have hiI := integrable_lineDeriv_smul_of_locallyIntegrableOn (hu.locallyIntegrableOn Ω) φ I
  have hiψ : Integrable fun z ↦ cauchyTransform f z (conjWirtingerDeriv ψ z 1) :=
    ((locallyIntegrable_clm_apply hT (continuous_conjWirtingerDeriv_apply hψ 1)
      ).integrableOn_isCompact hψc.isCompact).integrable_of_forall_notMem_eq_zero fun z hz ↦ by
        rw [conjWirtingerDeriv_apply_of_notMem_tsupport hz, map_zero]
  have hiφ := φ.integrable_smul (hTd.locallyIntegrableOn Ω)
  have hiφ' := φ.integrable_smul (hfξ.locallyIntegrableOn Ω)
  have hpt (z : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) z 1 • cauchyTransform f z (ξ z) +
      I • lineDeriv ℝ (φ : ℂ → ℝ) z I • cauchyTransform f z (ξ z) =
        (2 : ℂ) • cauchyTransform f z (conjWirtingerDeriv ψ z 1) -
          (2 : ℂ) • ((φ : ℂ → ℝ) z • cauchyTransform f z (conjWirtingerDeriv ξ z 1)) := by
    rw [hdψ, map_add, map_smul, map_smul, hreal, hreal, hreal]
    module
  have hfψ : ∫ z, f z (ψ z) = ∫ z, (φ : ℂ → ℝ) z • f z (ξ z) := by
    congr 1 with z
    rw [hψ_def, map_smul, hreal]
  calc (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • cauchyTransform f z (ξ z)) +
        I • ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • cauchyTransform f z (ξ z)
      = ∫ z, ((2 : ℂ) • cauchyTransform f z (conjWirtingerDeriv ψ z 1) -
          (2 : ℂ) • ((φ : ℂ → ℝ) z • cauchyTransform f z (conjWirtingerDeriv ξ z 1))) := by
        have hiI' : Integrable fun z ↦
            I • lineDeriv ℝ (φ : ℂ → ℝ) z I • cauchyTransform f z (ξ z) := hiI.smul I
        rw [← integral_smul, ← integral_add hi1 hiI']
        exact integral_congr_ae (Eventually.of_forall hpt)
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

end Operator

/-- **Representation of weak solutions of `bar∂ u = f`.** A distributional solution of
`bar∂ u = f` on `Ω`, with integrable `f` and finite-dimensional complex coefficients, agrees almost
everywhere on `Ω` with the Cauchy transform of `f` plus a holomorphic function. -/
theorem HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq_cauchyTransform_add
    [FiniteDimensional ℂ F] {Ω : Opens ℂ} {u f : ℂ → F}
    (hu : HasWeakConjWirtingerDerivOn volume Ω u f) (hf : Integrable f) :
    ∃ v : ℂ → F, DifferentiableOn ℂ v Ω ∧ u =ᵐ[volume.restrict Ω] cauchyTransform f + v := by
  have := FiniteDimensional.complete ℂ F
  have h := hu.sub (hasWeakConjWirtingerDerivOn_cauchyTransform hf Ω)
  rw [sub_self] at h
  obtain ⟨v, hv, huv⟩ := h.exists_differentiableOn_ae_eq
  refine ⟨v, hv, huv.mono fun z hz ↦ ?_⟩
  rw [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel]

end TauCeti
