/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Maps approximating linear maps on ultrametric closed balls

A map `g` approximating the identity on a closed ball `closedBall x r` of a complete ultrametric
normed space, with a constant `c < 1`, maps that ball onto `closedBall (g x) r`: the inclusion is
the strong triangle inequality, and every point of the target ball is reached by the contraction
`y ↦ y - g y + w`. Composing with a linear equivalence `A`, a map approximating `A` on a closed
ball maps it onto a translate of the linear image of a ball.

## Main results

* `ApproximatesLinearOn.image_closedBall_eq_of_isUltrametricDist`: a map approximating the
  identity on an ultrametric closed ball with constant `c < 1` maps it onto the closed ball of the
  same radius around the image of the centre.
* `ApproximatesLinearOn.image_closedBall_eq_vadd_image_of_isUltrametricDist`: a map approximating
  a linear equivalence `A` on an ultrametric closed ball maps it onto `f x +ᵥ A '' closedBall 0 r`.
-/

public section

open Set Metric
open scoped NNReal Pointwise

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ApproximatesLinearOn

/-- **A map close to the identity on an ultrametric closed ball maps it onto a closed ball.** If
`g` approximates the identity on `closedBall x r` with constant `c < 1`, in a complete ultrametric
normed space, then `g` maps `closedBall x r` onto `closedBall (g x) r`. -/
theorem image_closedBall_eq_of_isUltrametricDist [IsUltrametricDist E] [CompleteSpace E]
    {g : E → E} {x : E} {r : ℝ} {c : ℝ≥0}
    (hg : ApproximatesLinearOn g (ContinuousLinearMap.id 𝕜 E) (closedBall x r) c) (hc : c < 1) :
    g '' closedBall x r = closedBall (g x) r := by
  have hg' : ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r,
      ‖g y - g z - (y - z)‖ ≤ c * ‖y - z‖ := fun y hy z hz ↦ by simpa using hg y hy z hz
  have hcle : ∀ t : ℝ, 0 ≤ t → c * t ≤ t := fun t ht ↦
    mul_le_of_le_one_left ht (mod_cast hc.le)
  refine Subset.antisymm ?_ fun w hw ↦ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have h := hg' y hy x (mem_closedBall_self (dist_nonneg.trans hy))
    rw [mem_closedBall_iff_norm] at hy ⊢
    calc ‖g y - g x‖ = ‖(y - x) + (g y - g x - (y - x))‖ := by abel_nf
      _ ≤ max ‖y - x‖ ‖g y - g x - (y - x)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le hy (h.trans ((hcle _ (norm_nonneg _)).trans hy))
  -- The target point `w` is the image of the fixed point of `y ↦ y - g y + w`.
  have hr : 0 ≤ r := dist_nonneg.trans hw
  have hx : x ∈ closedBall x r := mem_closedBall_self hr
  have hmaps : MapsTo (fun y ↦ y - g y + w) (closedBall x r) (closedBall x r) := fun y hy ↦ by
    have h := hg' y hy x hx
    rw [mem_closedBall_iff_norm] at hy hw ⊢
    calc ‖y - g y + w - x‖ = ‖(w - g x) + -(g y - g x - (y - x))‖ := by abel_nf
      _ ≤ max ‖w - g x‖ ‖-(g y - g x - (y - x))‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := by
        rw [norm_neg]
        exact max_le hw (h.trans ((hcle _ (norm_nonneg _)).trans hy))
  have : CompleteSpace (closedBall x r) := isClosed_closedBall.completeSpace_coe
  have : Nonempty (closedBall x r) := ⟨⟨x, hx⟩⟩
  have hT : ContractingWith c (hmaps.restrict _ _ _) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    calc ‖(y : E) - g y + w - ((z : E) - g z + w)‖ = ‖g y - g z - ((y : E) - z)‖ := by
          rw [← norm_neg]; abel_nf
      _ ≤ c * ‖(y : E) - z‖ := hg' y y.property z z.property
  obtain ⟨y, hy⟩ : ∃ y : closedBall x r, hmaps.restrict _ _ _ y = y :=
    ⟨_, ContractingWith.fixedPoint_isFixedPt hT⟩
  refine ⟨y, y.property, ?_⟩
  have h := congrArg Subtype.val hy
  simp only [MapsTo.val_restrict_apply] at h
  calc g y = g y + ((y : E) - g y + w - y) := by rw [h, sub_self, add_zero]
    _ = w := by abel

/-- **The image of an ultrametric closed ball under a map close to a linear equivalence.** If `f`
approximates a linear equivalence `A` on `closedBall x r`, in a complete ultrametric normed space,
with a constant `c` such that `‖A⁻¹‖ c < 1`, then `f` maps `closedBall x r` onto
`f x +ᵥ A '' closedBall 0 r`. -/
theorem image_closedBall_eq_vadd_image_of_isUltrametricDist [IsUltrametricDist E]
    [CompleteSpace E] {f : E → F} {A : E ≃L[𝕜] F} {x : E} {r : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x r) c)
    (hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c < 1) :
    f '' closedBall x r = f x +ᵥ A '' closedBall 0 r := by
  have hg : ApproximatesLinearOn (A.symm ∘ f) (ContinuousLinearMap.id 𝕜 E) (closedBall x r)
      (‖(A.symm : F →L[𝕜] E)‖₊ * c) := fun y hy z hz ↦ by
    have h : A.symm (f y) - A.symm (f z) - (y - z) = A.symm (f y - f z - A (y - z)) := by
      simp
    simp only [Function.comp_apply, ContinuousLinearMap.id_apply, h, NNReal.coe_mul, coe_nnNorm,
      mul_assoc]
    exact (ContinuousLinearMap.le_opNorm (A.symm : F →L[𝕜] E) _).trans
      (mul_le_mul_of_nonneg_left (hf y hy z hz) (norm_nonneg _))
  have himage := hg.image_closedBall_eq_of_isUltrametricDist hc
  have hf_eq : f = A ∘ (A.symm ∘ f) := by ext; simp
  rw [hf_eq, image_comp, himage, ← vadd_closedBall_zero, image_vadd_distrib]
  simp

end ApproximatesLinearOn
