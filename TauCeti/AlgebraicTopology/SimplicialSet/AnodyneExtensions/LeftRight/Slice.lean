/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice

/-!
# Relative slices and coslices of inner fibrations

The relative slice map of an inner fibration along a monomorphism is a right fibration
(`SSet.slice.rightFibration_restrictionMap`, HTT Proposition 2.1.2.1); dually, the relative
coslice map is a left fibration (`SSet.coslice.leftFibration_restrictionMap`). Along a left
anodyne extension the relative slice map is a trivial fibration (`SSet.slice.rlp_restrictionMap`),
and along a right anodyne extension so is the relative coslice map
(`SSet.coslice.rlp_restrictionMap`).

Through the universal properties of slices and coslices, lifting problems, ranging over all
diagrams, correspond to extension problems along the pushout-join of `j : A ⟶ B` and
`i : L ⟶ K`. For a fixed slice diagram `σ : K ⟶ X`, the map `A ⋆ K ⟶ X` must restrict to `σ`
on `K`; for a fixed coslice diagram `τ : B ⟶ X`, the map `B ⋆ L ⟶ X` must restrict to `τ` on `B`.
The join horn filtration makes the pushout-join of a right horn and a boundary, or a boundary
and a left horn, inner anodyne. Reduction to boundaries proves the generating-horn cases;
the lifting correspondence then gives the relative fibration instances and the general
anodyne cases.

The reduction to boundary inclusions and inner anodyne pushout-joins follows the proof of
Mathlib's `SSet.innerFibration_pullbackObjObjπ` by Jack McKoen and Joël Riou, with slices and
coslices playing the role of the internal hom.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3 and Proposition 2.1.2.1.
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

variable {A B K L X S : SSet.{u}}

/-! ### Relative slices and coslices of inner fibrations -/

namespace coslice

/-- If `p` lifts against the union-join of a subcomplex with every boundary, its relative
coslice map along that subcomplex lifts against every monomorphism. -/
theorem hasLiftingProperty_restrictionMap_of_unionJoin (Λ : K.Subcomplex) (p : X ⟶ S)
    (h : ∀ n, HasLiftingProperty (Subcomplex.unionJoin Λ ∂Δ[n]).ι p)
    (τ : K ⟶ X) (j : A ⟶ B) [Mono j] :
    HasLiftingProperty j (restrictionMap Λ.ι p τ) := by
  suffices (monomorphisms SSet.{u}).rlp (restrictionMap Λ.ι p τ) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := h n
  exact (forall_hasLiftingProperty_restrictionMap_iff_of_isPushout Λ.ι ∂Δ[n].ι p
    (Subcomplex.unionJoin.isPushout _ _) (Subcomplex.unionJoin.ι₁_ι _ _)
    (Subcomplex.unionJoin.ι₂_ι _ _)).2 inferInstance τ

end coslice

namespace slice

/-- If `p` lifts against the union-join of every boundary with a subcomplex, its relative
slice map along that subcomplex lifts against every monomorphism. -/
theorem hasLiftingProperty_restrictionMap_of_unionJoin (Λ : K.Subcomplex) (p : X ⟶ S)
    (h : ∀ n, HasLiftingProperty (Subcomplex.unionJoin ∂Δ[n] Λ).ι p)
    (σ : K ⟶ X) (j : A ⟶ B) [Mono j] :
    HasLiftingProperty j (restrictionMap Λ.ι p σ) := by
  suffices (monomorphisms SSet.{u}).rlp (restrictionMap Λ.ι p σ) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := h n
  exact (forall_hasLiftingProperty_restrictionMap_iff_of_isPushout ∂Δ[n].ι Λ.ι p
    (Subcomplex.unionJoin.isPushout _ _) (Subcomplex.unionJoin.ι₁_ι _ _)
    (Subcomplex.unionJoin.ι₂_ι _ _)).2 inferInstance σ

/-- **The relative slice map of an inner fibration is a right fibration** (HTT
Proposition 2.1.2.1): for an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K` and a
diagram `σ : K ⟶ X`, the map `X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` is a right
fibration. -/
instance rightFibration_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K) [Mono i]
    (σ : K ⟶ X) : RightFibration (restrictionMap i p σ) :=
  (rightFibration_iff_hasLiftingProperty _).2 fun _ _ hk ↦
    (forall_hasLiftingProperty_restrictionMap_iff _ i p).2
      (fun τ ↦ coslice.hasLiftingProperty_restrictionMap_of_unionJoin _ p
        (fun n ↦ join.innerAnodyneExtensions_unionJoin_horn_boundary n hk p
          (mem_innerFibrations p)) τ i) σ

end slice

namespace coslice

/-- **The relative coslice map of an inner fibration is a left fibration**, dually to HTT
Proposition 2.1.2.1: for an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K` and a
diagram `τ : K ⟶ X`, the map `X_{τ/} ⟶ X_{i ≫ τ/} ×_{S_{i ≫ τ ≫ p/}} S_{τ ≫ p/}` is a left
fibration. -/
instance leftFibration_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K) [Mono i]
    (τ : K ⟶ X) : LeftFibration (restrictionMap i p τ) :=
  (leftFibration_iff_hasLiftingProperty _).2 fun _ _ hk ↦
    (slice.forall_hasLiftingProperty_restrictionMap_iff i _ p).1
      (fun σ ↦ slice.hasLiftingProperty_restrictionMap_of_unionJoin _ p
        (fun n ↦ join.innerAnodyneExtensions_unionJoin_boundary_horn n hk p
          (mem_innerFibrations p)) σ i) τ

end coslice

namespace slice

/-- The relative slice map of an inner fibration along a left anodyne extension is a trivial
fibration. -/
lemma rlp_restrictionMap (i : L ⟶ K) (hi : leftAnodyneExtensions i) (p : X ⟶ S)
    [InnerFibration p] (σ : K ⟶ X) :
    (monomorphisms SSet.{u}).rlp (restrictionMap i p σ) := by
  intro A B j hj
  have : Mono j := hj
  exact (forall_hasLiftingProperty_restrictionMap_iff j i p).2
    (fun τ ↦ hi.hasLiftingProperty (coslice.restrictionMap j p τ)) σ

end slice

namespace coslice

/-- The relative coslice map of an inner fibration along a right anodyne extension is a trivial
fibration. -/
lemma rlp_restrictionMap (i : L ⟶ K) (hi : rightAnodyneExtensions i) (p : X ⟶ S)
    [InnerFibration p] (τ : K ⟶ X) :
    (monomorphisms SSet.{u}).rlp (restrictionMap i p τ) := by
  intro A B j hj
  have : Mono j := hj
  exact (slice.forall_hasLiftingProperty_restrictionMap_iff i j p).1
    (fun σ ↦ hi.hasLiftingProperty (slice.restrictionMap j p σ)) τ

end coslice

end SSet
