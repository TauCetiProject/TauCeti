/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Basic

/-!
# Interchanging the summands of a smooth connected sum

Turning a knot over, moving it by the half-turn in the distinguished complex plane `ι ℂ` and
rotating its circle parameter by a half-turn (`TauCeti.SmoothCircleEmbedding.turnOver`), is the end
of a smooth isotopy through parametrized embeddings, in every sphere dimension
(`TauCeti.SmoothCircleEmbedding.smoothIsotopic_turnOver`): the half-turn is joined to the identity
by rotations, and the parameter is rotated alongside. Its collared trace is a concordance.

Two consequences for knots in connected-sum position:

* the connected sum with the great circle on the left is the turned-over knot, so **the great
  circle is a left unit up to concordance**
  (`TauCeti.SmoothCircleEmbedding.concordant_greatCircle_connectedSum`); it is a right unit on the
  nose (`TauCeti.SmoothCircleEmbedding.connectedSum_greatCircle`);
* the half-turn exchanges the two hemispheres, so turning `K₁ # K₂` over gives `K₂ # K₁`, and **the
  connected sum is commutative** up to smooth isotopy and concordance
  (`TauCeti.SmoothCircleEmbedding.smoothIsotopic_connectedSum_comm`,
  `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_comm`).

The conclusions concern the parametrized embeddings, not just their images. They supply the unit
and commutativity inputs for connected sum on concordance classes, without asserting that the
operation is independent of the choice of representatives in connected-sum position.

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
theorem turnOver_connectedSum {K₁ K₂ :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    turnOver ι (connectedSum K₁ K₂ h₁ h₂) = connectedSum K₂ K₁ h₂ h₁ := by
  ext z : 2
  simp only [coe_turnOver_apply]
  rcases lt_trichotomy (z : ℂ).im 0 with hz | hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ (by simpa using hz.le),
      coe_connectedSum_apply_of_im_neg _ _ hz]
  · have hnz : ((-z : Circle) : ℂ).im = 0 := by simp [hz]
    rw [connectedSum_apply_of_im_nonneg _ _ hnz.ge,
      connectedSum_apply_of_im_nonneg _ _ hz.ge,
      h₁.apply_eq hnz.le, h₂.apply_eq hz.le, reflection_greatCircle_neg, coe_greatCircle_apply]
  · rw [coe_connectedSum_apply_of_im_neg _ _ (by simpa using hz),
      neg_neg, Submodule.reflection_reflection,
      connectedSum_apply_of_im_nonneg _ _ hz.le]

/-- **A knot is smoothly isotopic to its turned-over copy**: `K` and `turnOver ι K`, the knot moved
by the half-turn in the plane `ι ℂ` and reparametrized by `z ↦ -z`, are joined by a jointly smooth
isotopy through parametrized embeddings. -/
theorem smoothIsotopic_turnOver (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothIsotopic K.toContMDiffMap (turnOver ι K).toContMDiffMap := by
  apply smoothIsotopic_def.mpr
  obtain ⟨R, hR, hR0, hR1⟩ := ι.exists_contDiff_path_reflection_orthogonal_range
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
    simp [F, ha0, hR0]
  · intro z
    apply Subtype.ext
    simp [F, ha1, hR1]
  · intro t
    have hslice := (K.rotate (a t)).transDiffeomorph
      ((R t).unitSphereDiffeomorph (n := n) (k := n) ∞) |>.isSmoothEmbedding
    simpa only [SmoothEmbedding.coe_transDiffeomorph, Function.comp_def,
      rotate_apply, F, ContMDiffMap.coeFn_mk] using hslice

/-- **Turning a knot over does not change its concordance class.** -/
theorem concordant_turnOver (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothEmbedding.Concordant K (turnOver ι K) :=
  SmoothEmbedding.Concordant.of_smoothIsotopic (smoothIsotopic_turnOver ι K) (by simp) le_rfl

/-- **The great circle is a left unit up to concordance**: the connected sum of the great circle
with a knot `K` in connected-sum position is concordant to `K`. On the right the great circle is a
unit on the nose (`TauCeti.SmoothCircleEmbedding.connectedSum_greatCircle`). -/
theorem concordant_greatCircle_connectedSum {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₀ : IsConnectedSumPosition ι (greatCircle ι)) (h : IsConnectedSumPosition ι K) :
    SmoothEmbedding.Concordant (connectedSum (greatCircle ι) K h₀ h) K := by
  have hK : connectedSum (greatCircle ι) K h₀ h = turnOver ι K := by
    ext z : 2
    simp [greatCircle_connectedSum]
  exact hK ▸ (concordant_turnOver ι K).symm

/-- Connected sum of knots in connected-sum position is commutative up to a jointly smooth
isotopy through parametrized embeddings. No change of the knots' orientations is made. -/
theorem smoothIsotopic_connectedSum_comm {K₁ K₂ :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    SmoothIsotopic (connectedSum K₁ K₂ h₁ h₂).toContMDiffMap
      (connectedSum K₂ K₁ h₂ h₁).toContMDiffMap :=
  turnOver_connectedSum ι h₁ h₂ ▸ smoothIsotopic_turnOver ι _

/-- Connected sum of knots in connected-sum position is commutative up to smooth concordance. -/
theorem concordant_connectedSum_comm {K₁ K₂ :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₂ K₁ h₂ h₁) := by
  exact SmoothEmbedding.Concordant.of_smoothIsotopic
    (smoothIsotopic_connectedSum_comm ι h₁ h₂) (by simp) le_rfl

end TauCeti.SmoothCircleEmbedding
