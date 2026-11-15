/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.Leaf
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
import TauCeti.Geometry.Manifold.ContMDiff.Curve

/-!
# Horizontal maps have image in one leaf

A horizontal `C¹` map from a preconnected manifold to a foliated manifold has its image in one
leaf. This applies in particular to connected integral-manifold parametrizations. The source
and ambient models may have boundary or corners; neither finite dimensionality nor a separation
axiom is needed.

## Main results

* `TauCeti.Foliation.joinedByTangentCurve_of_isHorizontalMap`: any two image points of a
  horizontal map from a preconnected manifold are joined by a tangent curve.
* `TauCeti.Foliation.range_subset_leaf_of_isHorizontalMap`: the image of that map lies in
  the leaf through each of its image points.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 19.21 and Lemma 19.22, pp. 502–505 (connected integral manifolds and maximal leaves).
-/

public section

open Set
open TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti.Foliation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {k : ℕ} [IsManifold I (n + 1) M] (F : Foliation I n M k)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [PreconnectedSpace N] {f : N → M}

/-- Any two image points of a horizontal `C¹` map from a preconnected manifold are joined by a
curve tangent to the foliation. -/
theorem joinedByTangentCurve_of_isHorizontalMap
    (hf : IsHorizontalMap J F.distribution f) (hfd : ContMDiff J I 1 f) (x y : N) :
    F.JoinedByTangentCurve (f x) (f y) := by
  obtain ⟨γ, hγ, h₀, h₁⟩ := exists_contMDiff_curve (I := J) (n := 1) x y
  refine joinedByTangentCurve_iff.mpr ⟨f ∘ γ, (hfd.comp hγ).contMDiffOn, ?_, ?_, ?_⟩
  · intro t ht
    rw [curveVelocityWithin_map (hfd.mdifferentiable one_ne_zero (γ t))
      (uniqueDiffOn_Icc zero_lt_one t ht)
      ((hγ.mdifferentiable one_ne_zero t).mdifferentiableWithinAt)]
    exact hf.mfderiv_mem _ _
  · simp only [Function.comp_apply, h₀ 0 le_rfl]
  · simp only [Function.comp_apply, h₁ 1 le_rfl]

/-- The image of a horizontal `C¹` map from a preconnected manifold is contained in the leaf
through each of its image points. -/
theorem range_subset_leaf_of_isHorizontalMap
    (hf : IsHorizontalMap J F.distribution f) (hfd : ContMDiff J I 1 f) (x : N) :
    range f ⊆ F.leaf (f x) := by
  rintro _ ⟨y, rfl⟩
  exact mem_leaf.mpr (F.joinedByTangentCurve_of_isHorizontalMap hf hfd x y).sameLeaf

end TauCeti.Foliation
