/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Components

/-!
# Moment maps on the fixed-point set

Let a Lie group `G` act smoothly on a manifold `M` with a two-form `σ`, and let
`μ : M → 𝔤*` be a moment map, so that `dμ^ξ = ι_{ξ_M} σ` for every component `μ^ξ = ⟨μ, ξ⟩`. At a
point `x` of the fixed-point set `M^G` every fundamental vector field `ξ_M` vanishes, so every
component of `μ` is critical at `x`
(`TauCeti.SmoothTwoForm.IsMomentMap.fixedPoints_subset_criticalPoints`). For a nondegenerate `σ`
and a generator `ξ` of a dense one-parameter subgroup this inclusion is an equality
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints_of_eq_top`).

If the action preserves a smooth Riemannian metric, for instance if `G` is compact, the fixed-point
set is an embedded submanifold, possibly with components of different dimensions, and a function
whose differential vanishes along it is locally constant on it
(`TauCeti.isLocallyConstant_domRestrict_fixedPoints`). Hence:

* if the action preserves a smooth Riemannian metric, every component `μ^ξ` is locally constant
  on `M^G` (`TauCeti.SmoothTwoForm.IsMomentMap.isLocallyConstant_domRestrict_fixedPoints`);
* for a compact group acting on a σ-compact manifold, every component `μ^ξ` is locally constant
  on `M^G`
  (`TauCeti.SmoothTwoForm.IsMomentMap.isLocallyConstant_domRestrict_fixedPoints_of_compactSpace`),
  so `μ` is constant on each connected component of `M^G`
  (`TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isPreconnected`);
* for a compact group acting on a compact manifold, `M^G` has finitely many connected components
  (`TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`), and `μ` takes only finitely
  many values on `M^G` (`TauCeti.SmoothTwoForm.IsMomentMap.finite_image_fixedPoints`).

So for a torus acting on a compact symplectic manifold, the convex hull of the images of the fixed
components is the convex hull of a finite set, a polytope. This is the set which the convexity
theorem of Atiyah and Guillemin–Sternberg identifies with the image of `μ`. Neither closedness
nor nondegeneracy of `σ` is used, and `μ` need not be equivariant.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.isLocallyConstant_domRestrict_fixedPoints`,
  `TauCeti.SmoothTwoForm.IsMomentMap.isLocallyConstant_domRestrict_fixedPoints_of_compactSpace`:
  a moment map is locally constant on the fixed-point set, for an action preserving a smooth
  Riemannian metric and for a compact group.
* `TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isPreconnected`: for a compact group acting on a
  σ-compact manifold, a moment map is constant on each connected subset of the fixed-point set.
* `TauCeti.SmoothTwoForm.IsMomentMap.finite_image_fixedPoints`: for a compact group acting on a
  compact manifold, a moment map has finite image on the fixed-point set.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the moment map is constant on each of the finitely many fixed components).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 27.1.
-/

public section

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

section Riemannian

variable [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M]

/-- **A moment map is locally constant on the fixed-point set.** For a smooth action preserving a
smooth Riemannian metric, every component `μ^ξ` of a moment map is locally constant on the
fixed-point set `M^G`, so it is constant on each connected component of `M^G`. -/
theorem isLocallyConstant_domRestrict_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
    [IsContMDiffRiemannianBundle I' ∞ E' (fun x : M ↦ TangentSpace I' x)]
    (hG : ∀ (g : G) (x : M) (u w : TangentSpace I' x),
      inner ℝ (mfderiv I' I' (g • ·) x u) (mfderiv I' I' (g • ·) x w) = inner ℝ u w)
    (ξ : GroupLieAlgebra I G) :
    IsLocallyConstant ((MulAction.fixedPoints G M).domRestrict fun y ↦ μ y ξ) :=
  have : ContMDiffConstSMul I' ∞ G M := ContMDiffSMul.contMDiffConstSMul I
  TauCeti.isLocallyConstant_domRestrict_fixedPoints hG fun _ hx ↦
    h.hasMFDerivAt_zero_of_mem_fixedPoints ξ hx

variable [CompactSpace G] [T2Space G]

/-- **A moment map of a compact group is locally constant on the fixed-point set.** For a smooth
action of a compact Lie group on a σ-compact manifold, every component `μ^ξ` of a moment map is
locally constant on the fixed-point set `M^G`. -/
theorem isLocallyConstant_domRestrict_fixedPoints_of_compactSpace [SigmaCompactSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (ξ : GroupLieAlgebra I G) :
    IsLocallyConstant ((MulAction.fixedPoints G M).domRestrict fun y ↦ μ y ξ) :=
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  TauCeti.isLocallyConstant_domRestrict_fixedPoints_of_compactSpace I fun _ hx ↦
    h.hasMFDerivAt_zero_of_mem_fixedPoints ξ hx

/-- **A moment map of a compact group is constant on each fixed component.** Any two points of a
preconnected subset of the fixed-point set `M^G`, such as a connected component of `M^G`, have the
same image under a moment map. -/
theorem apply_eq_of_isPreconnected [SigmaCompactSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {C : Set M}
    (hC : IsPreconnected C) (hCG : C ⊆ MulAction.fixedPoints G M) {x y : M} (hx : x ∈ C)
    (hy : y ∈ C) : μ x = μ y := by
  have hC' : IsPreconnected (Subtype.val ⁻¹' C : Set (MulAction.fixedPoints G M)) := by
    rwa [← IsInducing.subtypeVal.isPreconnected_image,
      image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
  exact LinearMap.ext fun ξ ↦
    (h.isLocallyConstant_domRestrict_fixedPoints_of_compactSpace ξ).apply_eq_of_isPreconnected hC'
      (x := ⟨x, hCG hx⟩) (y := ⟨y, hCG hy⟩) hx hy

/-- **A moment map of a compact group takes finitely many values on the fixed-point set** of a
compact manifold: it is constant on each of the finitely many connected components of `M^G`. -/
theorem finite_image_fixedPoints [CompactSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) :
    (μ '' MulAction.fixedPoints G M).Finite := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := finite_connectedComponents_fixedPoints_of_compactSpace I' I G (M := M)
  -- `μ` factors through the connected components of `M^G`.
  have hμ : ∀ x y : MulAction.fixedPoints G M,
      connectedComponent x = connectedComponent y → μ x = μ y := fun x y hxy ↦
    h.apply_eq_of_isPreconnected (isPreconnected_connectedComponent.image _
      continuous_subtypeVal.continuousOn) (image_subset_iff.2 fun z _ ↦ z.property)
      (mem_image_of_mem _ mem_connectedComponent)
      (mem_image_of_mem _ (connectedComponent_eq_iff_mem.1 hxy.symm))
  refine (finite_range fun c : ConnectedComponents (MulAction.fixedPoints G M) ↦
    μ (ConnectedComponents.surjective_coe c).choose).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨.mk ⟨x, hx⟩, hμ _ _ (ConnectedComponents.coe_eq_coe.1
    (ConnectedComponents.surjective_coe _).choose_spec)⟩

end Riemannian

end TauCeti.SmoothTwoForm.IsMomentMap
