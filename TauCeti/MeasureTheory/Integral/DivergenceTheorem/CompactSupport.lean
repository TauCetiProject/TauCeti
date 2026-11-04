/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Compactly supported divergence on a vector space

This specializes Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
to a globally `C¹`, compactly supported vector field. A bounding box contains its support,
so every boundary flux vanishes and the full-space divergence integral is zero.

The argument needs only differentiability and an integrable divergence
(`MeasureTheory.integral_divergence_eq_zero_of_differentiable`). Transporting along the
coordinates `ℝ² ≃ ℂ` gives the planar statement
`MeasureTheory.integral_fderiv_one_add_fderiv_I_eq_zero`.
-/

public section

noncomputable section

open Set

namespace MeasureTheory

/-- **Divergence theorem for compactly supported differentiable fields.** If a coordinate
vector field is differentiable with compact support and its divergence is integrable, then the
divergence has zero integral on the whole space. No continuity of the derivative is assumed. -/
theorem integral_divergence_eq_zero_of_differentiable {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (hf : Differentiable ℝ f) (hc : HasCompactSupport f)
    (hi : Integrable (fun x ↦ ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i)) :
    ∫ x, ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i = 0 := by
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let a : Fin (n + 1) → ℝ := fun _ ↦ -R
  let b : Fin (n + 1) → ℝ := fun _ ↦ R
  have hab : a ≤ b := fun _ ↦ neg_le_self hR.le
  have hzero {x : Fin (n + 1) → ℝ} (hn : R ≤ ‖x‖) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx ↦ (hbound x hx).not_ge hn)
  have hDzero {x : Fin (n + 1) → ℝ} (hx : x ∉ Icc a b) :
      ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i = 0 := by
    have hn : R ≤ ‖x‖ := le_of_not_gt fun hn ↦ hx ⟨fun i ↦
      (abs_lt.mp (lt_of_le_of_lt (norm_le_pi_norm x i) hn)).1.le, fun i ↦
      (abs_lt.mp (lt_of_le_of_lt (norm_le_pi_norm x i) hn)).2.le⟩
    have ht : x ∉ tsupport f := fun hx ↦ (hbound x hx).not_ge hn
    simp [fderiv_of_notMem_tsupport ℝ ht]
  have hface (i : Fin (n + 1)) (t : ℝ) (ht : |t| = R) (y : Fin n → ℝ) :
      f (i.insertNth t y) i = 0 := by
    apply congrFun (hzero ?_) i
    have h := norm_le_pi_norm (i.insertNth (α := fun _ ↦ ℝ) t y) i
    simpa only [Fin.insertNth_apply_same, Real.norm_eq_abs, ht] using h
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hab f
    (fderiv ℝ f) ∅ countable_empty hf.continuous.continuousOn
    (fun x _ ↦ (hf x).hasFDerivAt) hi.integrableOn
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hDzero hx)]
  rw [hdiv]
  simp only [a, b, hface _ R (abs_of_pos hR),
    hface _ (-R) (by rw [abs_neg, abs_of_pos hR]), integral_zero, sub_self,
    Finset.sum_const_zero]

/-- The divergence of a globally `C¹`, compactly supported coordinate vector field is
integrable and has zero integral on the whole space. -/
theorem integral_divergence_eq_zero {n : ℕ}
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
  exact ⟨hDi, integral_divergence_eq_zero_of_differentiable (hf.differentiable one_ne_zero) hc hDi⟩

open Complex in
/-- **Divergence theorem in the plane for compactly supported differentiable fields.** If
`f, g : ℂ → ℝ` are differentiable with compact support and the divergence `∂ₓ f + ∂ᵧ g` is
integrable, then its integral vanishes. No continuity of the derivatives is assumed. -/
theorem integral_fderiv_one_add_fderiv_I_eq_zero {f g : ℂ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hi : Integrable (fun z ↦ fderiv ℝ f z 1 + fderiv ℝ g z I)) :
    ∫ z, fderiv ℝ f z 1 + fderiv ℝ g z I = 0 := by
  -- Transport along the coordinates `ℝ² ≃ ℂ`, `p ↦ p 0 + p 1 * I`, which preserve volume.
  let L : (Fin 2 → ℝ) ≃L[ℝ] ℂ := basisOneI.equivFun.toContinuousLinearEquiv.symm
  have hL : (L : (Fin 2 → ℝ) → ℂ) = measurableEquivPi.symm := rfl
  let F : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun p ↦ ![f (L p), g (L p)]
  have hF : Differentiable ℝ F := differentiable_pi.2 fun i ↦ by
    fin_cases i
    exacts [hf.comp L.differentiable, hg.comp L.differentiable]
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact
      (L.toHomeomorph.isCompact_preimage.2 (hfc.union hgc)) fun p hp ↦ ?_
    by_contra hn
    simp only [Set.mem_preimage, Set.mem_union, not_or] at hn
    have hf0 : f (L p) = 0 := image_eq_zero_of_notMem_tsupport hn.1
    have hg0 : g (L p) = 0 := image_eq_zero_of_notMem_tsupport hn.2
    exact hp (by simp [F, hf0, hg0])
  have hdivF (p : Fin 2 → ℝ) : ∑ i : Fin 2, fderiv ℝ F p (Pi.single i 1) i =
      fderiv ℝ f (L p) 1 + fderiv ℝ g (L p) I := by
    -- Componentwise derivatives; `ContinuousLinearMap.proj` applies the coordinate.
    have hcomp (i : Fin 2) (v : Fin 2 → ℝ) :
        fderiv ℝ F p v i = fderiv ℝ (fun q ↦ F q i) p v := by
      rw [(hasFDerivAt_pi'.1 (hF p).hasFDerivAt i).fderiv]; rfl
    simp only [Fin.sum_univ_two, hcomp]
    have h0 : L (Pi.single 0 1) = 1 := by rw [hL]; simp
    have h1 : L (Pi.single 1 1) = I := by rw [hL]; simp
    -- The coordinates of `F` are `f ∘ L` and `g ∘ L`.
    change fderiv ℝ (f ∘ L) p _ + fderiv ℝ (g ∘ L) p _ = _
    simp only [L.comp_right_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      h0, h1]
  have h : ∫ p : Fin 2 → ℝ, fderiv ℝ f (L p) 1 + fderiv ℝ g (L p) I = 0 := by
    simpa only [hdivF] using integral_divergence_eq_zero_of_differentiable hF hFc (by
      simp only [hdivF, hL]
      exact (volume_preserving_equiv_pi.symm.integrable_comp_emb
        measurableEquivPi.symm.measurableEmbedding).2 hi)
  rw [hL] at h
  exact (volume_preserving_equiv_pi.symm.integral_comp measurableEquivPi.symm.measurableEmbedding
    (fun z ↦ fderiv ℝ f z 1 + fderiv ℝ g z I)).symm.trans h

end MeasureTheory
