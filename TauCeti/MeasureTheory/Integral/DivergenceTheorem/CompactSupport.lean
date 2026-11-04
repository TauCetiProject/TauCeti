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

In the plane `ℂ` the same argument needs only differentiability and an integrable divergence
(`MeasureTheory.integral_fderiv_one_add_fderiv_I_eq_zero`), through Mathlib's rectangle
divergence theorem on `ℝ × ℝ`.
-/

public section

noncomputable section

open Set

namespace MeasureTheory

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

open Complex in
/-- **Divergence theorem in the plane for compactly supported differentiable fields.** If
`f, g : ℂ → ℝ` are differentiable with compact support and the divergence `∂ₓ f + ∂ᵧ g` is
integrable, then its integral vanishes. No continuity of the derivatives is assumed. -/
theorem integral_fderiv_one_add_fderiv_I_eq_zero {f g : ℂ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hi : Integrable (fun z ↦ fderiv ℝ f z 1 + fderiv ℝ g z I)) :
    ∫ z, fderiv ℝ f z 1 + fderiv ℝ g z I = 0 := by
  set D : ℂ → ℝ := fun z ↦ fderiv ℝ f z 1 + fderiv ℝ g z I
  obtain ⟨R₁, hR₁, hb₁⟩ := hfc.isBounded.exists_pos_norm_lt
  obtain ⟨R₂, hR₂, hb₂⟩ := hgc.isBounded.exists_pos_norm_lt
  set R := max R₁ R₂
  have hR : 0 < R := lt_max_of_lt_left hR₁
  have hfz {z : ℂ} (hz : R ≤ ‖z‖) : z ∉ tsupport f := fun h ↦
    (hb₁ z h).not_ge ((le_max_left _ _).trans hz)
  have hgz {z : ℂ} (hz : R ≤ ‖z‖) : z ∉ tsupport g := fun h ↦
    (hb₂ z h).not_ge ((le_max_right _ _).trans hz)
  -- Transport to `ℝ × ℝ`, where Mathlib's rectangle divergence theorem applies.
  let e : ℝ × ℝ → ℂ := fun p ↦ p.1 + p.2 * I
  have he : e = equivRealProdCLM.symm := funext fun p ↦ (equivRealProdCLM_symm_apply p).symm
  have hem : (measurableEquivRealProd.symm : ℝ × ℝ → ℂ) = e :=
    funext fun p ↦ mk_eq_add_mul_I _ _
  have hnorm (p : ℝ × ℝ) : max |p.1| |p.2| ≤ ‖e p‖ := by
    refine max_le ?_ ?_
    · simpa [e] using abs_re_le_norm (e p)
    · simpa [e] using abs_im_le_norm (e p)
  have hF (p : ℝ × ℝ) : HasFDerivAt (fun p ↦ f (e p))
      ((fderiv ℝ f (e p)).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)) p := by
    rw [he]; exact (hf _).hasFDerivAt.comp p equivRealProdCLM.symm.hasFDerivAt
  have hG (p : ℝ × ℝ) : HasFDerivAt (fun p ↦ g (e p))
      ((fderiv ℝ g (e p)).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)) p := by
    rw [he]; exact (hg _).hasFDerivAt.comp p equivRealProdCLM.symm.hasFDerivAt
  have hDe (p : ℝ × ℝ) : (fderiv ℝ f (e p)).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (1, 0) +
      (fderiv ℝ g (e p)).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (0, 1) = D (e p) := by
    simp [D, equivRealProdCLM_symm_apply]
  have hint : ∫ z, D z = ∫ p : ℝ × ℝ, D (e p) := by
    rw [← volume_preserving_equiv_real_prod.symm.integral_comp
      measurableEquivRealProd.symm.measurableEmbedding, hem]
  have hiR : Integrable (fun p : ℝ × ℝ ↦ D (e p)) := by
    have := (volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      measurableEquivRealProd.symm.measurableEmbedding).2 hi
    rwa [hem] at this
  have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_of_le (fun p ↦ f (e p))
    (fun p ↦ g (e p)) _ _ (-R, -R) (R, R) ⟨neg_le_self hR.le, neg_le_self hR.le⟩
    (Continuous.continuousOn (by
      rw [he]; exact hf.continuous.comp equivRealProdCLM.symm.continuous))
    (Continuous.continuousOn (by
      rw [he]; exact hg.continuous.comp equivRealProdCLM.symm.continuous))
    (fun p _ ↦ hF p) (fun p _ ↦ hG p) (by simpa only [hDe] using hiR.integrableOn)
  -- Both fields vanish on the boundary of the square `[-R, R]²`.
  have hfe {p : ℝ × ℝ} (h : |p.1| = R ∨ |p.2| = R) : f (e p) = 0 :=
    image_eq_zero_of_notMem_tsupport (hfz (h.elim (fun h ↦ h ▸ (le_max_left _ _).trans (hnorm p))
      (fun h ↦ h ▸ (le_max_right _ _).trans (hnorm p))))
  have hge {p : ℝ × ℝ} (h : |p.1| = R ∨ |p.2| = R) : g (e p) = 0 :=
    image_eq_zero_of_notMem_tsupport (hgz (h.elim (fun h ↦ h ▸ (le_max_left _ _).trans (hnorm p))
      (fun h ↦ h ▸ (le_max_right _ _).trans (hnorm p))))
  have habs : |R| = R := abs_of_pos hR
  have habs' : |-R| = R := by rw [abs_neg, habs]
  simp only [hDe] at hdiv
  rw [hint, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-R, -R) (R, R)), hdiv]
  · simp [hfe, hge, habs, habs']
  · intro p hp
    have hp' : R ≤ max |p.1| |p.2| := by
      by_contra! h
      exact hp ⟨⟨by linarith [neg_abs_le p.1, (max_lt_iff.1 h).1],
        by linarith [neg_abs_le p.2, (max_lt_iff.1 h).2]⟩,
        ⟨by linarith [le_abs_self p.1, (max_lt_iff.1 h).1],
        by linarith [le_abs_self p.2, (max_lt_iff.1 h).2]⟩⟩
    simp only [D, fderiv_of_notMem_tsupport ℝ (hfz (hp'.trans (hnorm p))),
      fderiv_of_notMem_tsupport ℝ (hgz (hp'.trans (hnorm p))), zero_apply, add_zero]

end MeasureTheory
