/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Basic

/-!
# Interchanging the summands of a smooth connected sum

The connected sums of two circle embeddings in connected-sum position, in either order,
are smoothly isotopic. A half-turn in the distinguished complex plane exchanges the two
hemispheres, while rotating the circle parameter by a half-turn keeps its orientation.
The simultaneous motion is through smooth embeddings in every sphere dimension, and its collared
trace gives a concordance between the two connected sums.

The conclusion concerns the parametrized embeddings, not just their images. It supplies the
commutativity input for connected sum on knot classes, without asserting that arbitrary knots
have been put in connected-sum position or that the operation is independent of that choice.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (connected sum).
* C. Livingston, *A survey of classical knot concordance*, Section 2 (the concordance group).

The construction uses Mathlib's hyperplane reflections and circle exponential, and Tau Ceti's
connected-sum convention from `TauCeti.KnotTheory.ConnectedSum.Basic`.
-/

public noncomputable section

open Metric Module Set Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti.SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] (ι : ℂ →ₗᵢ[ℝ] E)

/-- A half-turn of the sphere and a half-turn of the circle parameter exchange the two
summands exactly, including at the two joining points. -/
theorem rotate_transDiffeomorph_connectedSum {K₁ K₂ :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    rotate ((connectedSum K₁ K₂ h₁ h₂).transDiffeomorph
      ((LinearMap.range ι.toLinearMap)ᗮ.reflection.unitSphereDiffeomorph
        (n := n) (k := n) ∞)) (-1) = connectedSum K₂ K₁ h₂ h₁ := by
  ext z : 2
  simp only [rotate_apply, neg_one_mul, SmoothEmbedding.transDiffeomorph_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply]
  rcases lt_trichotomy (z : ℂ).im 0 with hz | hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ (by simpa using hz.le),
      coe_connectedSum_apply_of_im_neg _ _ hz]
  · have hnz : ((-z : Circle) : ℂ).im = 0 := by simp [hz]
    simp only [connectedSum_apply_of_im_nonneg _ _ hnz.ge,
      connectedSum_apply_of_im_nonneg _ _ hz.ge,
      h₁.apply_eq hnz.le, h₂.apply_eq hz.le, coe_greatCircle_apply,
      coe_greatCircle_apply, Circle.coe_neg, map_neg]
    rw [Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg
      (K := ι.range) (v := ι (z : ℂ)) ⟨(z : ℂ), rfl⟩, neg_neg]
  · rw [coe_connectedSum_apply_of_im_neg _ _ (by simpa using hz),
      neg_neg, Submodule.reflection_reflection,
      connectedSum_apply_of_im_nonneg _ _ hz.le]

/-- Connected sum of knots in connected-sum position is commutative up to a jointly smooth
isotopy through parametrized embeddings. No change of the knots' orientations is made. -/
theorem smoothIsotopic_connectedSum_comm {K₁ K₂ :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    SmoothIsotopic (connectedSum K₁ K₂ h₁ h₂).toContMDiffMap
      (connectedSum K₂ K₁ h₂ h₁).toContMDiffMap := by
  apply smoothIsotopic_def.mpr
  obtain ⟨R, hR, hR0, hR1⟩ := ι.exists_contDiff_path_reflection_orthogonal_range
  let K := connectedSum K₁ K₂ h₁ h₂
  let a : unitInterval → Circle := fun t => Circle.exp (Real.pi * t)
  have ha : ContMDiff (𝓡∂ 1) (𝓡 1) ∞ a :=
    contMDiff_circleExp.comp
      (contMDiff_const.mul (contMDiff_subtypeVal_Icc (x := 0) (y := 1)))
  have ha0 : a 0 = 1 := by simp [a]
  have ha1 : a 1 = -1 := by
    apply Subtype.ext
    simp [a, Circle.coe_exp, Complex.exp_pi_mul_I]
  let F : unitInterval × Circle → sphere (0 : E) 1 := fun p =>
    (R p.1).unitSphereDiffeomorph (n := n) (k := n) ∞ (K (a p.1 * p.2))
  have hs : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) (𝓡 n) ∞ F := by
    have hK : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, E) ∞
        (fun p : unitInterval × Circle => (K (a p.1 * p.2) : E)) :=
      contMDiff_coe_sphere.comp
        (K.contMDiff.comp ((ha.comp contMDiff_fst).mul contMDiff_snd))
    have ht : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ) ∞
        (fun p : unitInterval × Circle => (p.1 : ℝ)) :=
      (contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_fst
    have hambient := hR.comp_contMDiff (ht.prodMk_space hK)
    have hcoe : (fun p => (F p : E)) =
        (fun p => R (p.1 : ℝ) (K (a p.1 * p.2))) := by
      funext p
      exact LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply _ _
    have hmem (p : unitInterval × Circle) : (F p : E) ∈ sphere (0 : E) 1 := (F p).property
    simp only [Function.comp_def] at hambient
    rw [← hcoe] at hambient
    exact hambient.codRestrict_sphere hmem
  refine ⟨{ toContMDiffMap := ⟨F, hs⟩
            map_zero_left := ?_
            map_one_left := ?_
            isSmoothEmbedding := ?_ }⟩
  · intro z
    apply Subtype.ext
    simp [F, ha0, hR0, K]
  · intro z
    have heq := congrArg (fun L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) => (L z : E))
      (rotate_transDiffeomorph_connectedSum ι h₁ h₂)
    apply Subtype.ext
    simpa [F, ha1, hR1, K] using heq
  · intro t
    have hslice := (K.rotate (a t)).transDiffeomorph
      ((R t).unitSphereDiffeomorph (n := n) (k := n) ∞) |>.isSmoothEmbedding
    simpa only [SmoothEmbedding.coe_transDiffeomorph, Function.comp_def,
      rotate_apply, F, ContMDiffMap.coeFn_mk] using hslice

/-- Connected sum of knots in connected-sum position is commutative up to smooth concordance. -/
theorem concordant_connectedSum_comm {K₁ K₂ :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₂ K₁ h₂ h₁) := by
  obtain ⟨F⟩ := smoothIsotopic_def.mp (smoothIsotopic_connectedSum_comm ι h₁ h₂)
  exact SmoothEmbedding.Concordant.of_concordance
    (SmoothEmbedding.Concordance.ofSmoothIsotopy F (by simp) le_rfl)

end TauCeti.SmoothCircleEmbedding
