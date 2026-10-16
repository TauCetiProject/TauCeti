/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Coordinates
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactly supported exact top forms on a vector space

A compactly supported C1 form has an integrable exterior derivative whose top-degree
coefficient integrates to zero against the Haar measure of any basis. The coordinate proof
uses a bounding box: compact support eliminates all its boundary faces.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

private theorem integral_divergence_eq_zero {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) ∧
      (∫ x, ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) = 0 := by
  let D (x : Fin (n + 1) → ℝ) := ∑ i, fderiv ℝ f x (Pi.single i 1) i
  have hDc : Continuous D := continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDcompact : HasCompactSupport D := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hn
    exact hx (by simp [D, fderiv_of_notMem_tsupport ℝ hn])
  have hDi : Integrable D := hDc.integrable_of_hasCompactSupport hDcompact
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let a : Fin (n + 1) → ℝ := fun _ ↦ -R
  let b : Fin (n + 1) → ℝ := fun _ ↦ R
  have hab : a ≤ b := fun _ ↦ neg_le_self hR.le
  have hzero {x : Fin (n + 1) → ℝ} (hn : R ≤ ‖x‖) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx ↦ (hbound x hx).not_ge hn)
  have hDzero {x : Fin (n + 1) → ℝ} (hx : x ∉ Icc a b) : D x = 0 := by
    have hn : R ≤ ‖x‖ := le_of_not_gt fun hn ↦ hx ⟨fun i ↦
      (abs_lt.mp (lt_of_le_of_lt (norm_le_pi_norm x i) hn)).1.le, fun i ↦
      (abs_lt.mp (lt_of_le_of_lt (norm_le_pi_norm x i) hn)).2.le⟩
    have ht : x ∉ tsupport f := fun hx ↦ (hbound x hx).not_ge hn
    simp [D, fderiv_of_notMem_tsupport ℝ ht]
  have hface (i : Fin (n + 1)) (t : ℝ) (ht : |t| = R) (y : Fin n → ℝ) :
      f (i.insertNth t y) i = 0 := by
    apply congrFun (hzero ?_) i
    have h := norm_le_pi_norm (i.insertNth (α := fun _ ↦ ℝ) t y) i
    simpa only [Fin.insertNth_apply_same, Real.norm_eq_abs, ht] using h
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hab f
    (fderiv ℝ f) ∅ countable_empty hf.continuous.continuousOn
    (fun x _ ↦ (hf.differentiable one_ne_zero x).hasFDerivAt) hDi.integrableOn
  refine ⟨hDi, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hDzero hx)]
  rw [hdiv]
  simp only [a, b, hface _ R (abs_of_pos hR),
    hface _ (-R) (by rw [abs_neg, abs_of_pos hR]), integral_zero, sub_self,
    Finset.sum_const_zero]

private theorem integral_extDeriv_coordinate_eq_zero {n : ℕ}
    {ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    Integrable (fun x ↦ extDeriv ω x (Pi.basisFun ℝ (Fin (n + 1)))) ∧
      (∫ x, extDeriv ω x (Pi.basisFun ℝ (Fin (n + 1)))) = 0 := by
  let e := Pi.basisFun ℝ (Fin (n + 1))
  let L := ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := ℝ) e
  have hr := integral_divergence_eq_zero (L.contDiff.comp hω) (hc.comp_left L.map_zero)
  have hd (x) : (∑ i : Fin (n + 1),
      fderiv ℝ (L ∘ ω) x (Pi.single i 1) i) = extDeriv ω x e := by
    simpa only [fderivWithin_univ, extDerivWithin_univ, e, Pi.basisFun_apply] using
      DifferentiableWithinAt.sum_fderivWithin_signedRemoveNth
        ((hω.differentiable one_ne_zero x).differentiableWithinAt (s := Set.univ))
        uniqueDiffWithinAt_univ e
  simpa only [hd] using hr

/-- A compactly supported C1 form has an integrable exterior derivative, and the top-degree
coefficient integrates to zero for every basis and its normalized Haar measure. -/
theorem _root_.Module.Basis.integral_extDeriv_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) ℝ E) {ω : E → E [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    Integrable (fun x ↦ extDeriv ω x b) b.addHaar ∧
      (∫ x, extDeriv ω x b ∂b.addHaar) = 0 := by
  let L := b.equivFun.symm.toContinuousLinearEquiv
  let C := ContinuousAlternatingMap.compContinuousLinearMapCLM (F := ℝ) (ι := Fin n)
    L.toContinuousLinearMap
  let η := C ∘ ω ∘ L
  have hη : ContDiff ℝ 1 η := C.contDiff.comp (hω.comp L.contDiff)
  have hcη : HasCompactSupport η :=
    (hc.comp_homeomorph L.toHomeomorph).comp_left C.map_zero
  have hr := integral_extDeriv_coordinate_eq_zero hη hcη
  have hmap : (Pi.basisFun ℝ (Fin (n + 1))).map L.toLinearEquiv = b := by
    ext i
    simp [L]
  have hp : MeasurePreserving L volume b.addHaar := by
    refine ⟨L.continuous.measurable, ?_⟩
    rw [← Module.Basis.addHaar_basisFun, Module.Basis.map_addHaar, hmap]
  have hd (x) : extDeriv η x (Pi.basisFun ℝ (Fin (n + 1))) = extDeriv ω (L x) b := by
    have h := L.toContinuousLinearMap.extDerivWithin_pullback
      (uniqueDiffWithinAt_univ) ((hω.differentiable one_ne_zero) (L x)).differentiableWithinAt
      (mapsTo_univ _ _)
    simp only [extDerivWithin_univ] at h
    have he := congrArg (fun A ↦ A (Pi.basisFun ℝ (Fin (n + 1)))) h
    change extDeriv η x (Pi.basisFun ℝ (Fin (n + 1))) =
      extDeriv ω (L x) (fun i ↦ L (Pi.basisFun ℝ (Fin (n + 1)) i)) at he
    convert he using 1
    exact congrArg (fun b : Module.Basis (Fin (n + 1)) ℝ E ↦ extDeriv ω (L x) b) hmap.symm
  have he := L.toHomeomorph.measurableEmbedding
  refine ⟨(hp.integrable_comp_emb he (g := fun x ↦ extDeriv ω x b)).mp (hr.1.congr (by
    filter_upwards [] with x using hd x)), ?_⟩
  rw [← hp.integral_comp he (fun x ↦ extDeriv ω x b)]
  simpa only [← hd] using hr.2

end TauCeti
