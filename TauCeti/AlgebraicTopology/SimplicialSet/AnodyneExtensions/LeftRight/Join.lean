/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Slice

/-!
# One-sided anodyne pushout-joins

The pushout-join of a monomorphism and a Kan-anodyne extension is right anodyne;
with the Kan-anodyne extension in the first variable it is left anodyne. The statements
`SSet.join.rightAnodyneExtensions_of_isPushout` and
`SSet.join.leftAnodyneExtensions_of_isPushout` apply to any chosen pushout, and
`SSet.join.rightAnodyneExtensions_unionJoin_ι` and its left counterpart apply to subcomplexes.

The generating pushout-joins are horns: a boundary joined with a horn has missing face
strictly after the first vertex, and a horn joined with a boundary has missing face strictly
before the last vertex. The existing slice lifting correspondence extends these calculations
from boundaries to all monomorphisms and from horns to Kan-anodyne extensions. Equivalently,
the relative coslice of a right fibration along a monomorphism is a Kan fibration, as is the
relative slice of a left fibration.

This is the Kan-anodyne-input case of Joyal's pushout-join lemma, used to compare cocones
when the indexing simplicial set is assembled by pushouts. The lifting argument follows the
boundary reduction in Mathlib’s `SSet.fibration_pullbackObjObjπ`, by Jack McKoen and Joël Riou,
with slices and coslices replacing the internal hom.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 4.2.3.5 and its dual.
-/

public section

universe u

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Simplicial

namespace SSet

open modelCategoryQuillen

namespace join

/-- The pushout-join of a boundary with any positive-dimensional horn is right anodyne. -/
lemma rightAnodyneExtensions_unionJoin_boundary_horn (n : ℕ) {m : ℕ} [NeZero m]
    (j : Fin (m + 1)) :
    rightAnodyneExtensions (Subcomplex.unionJoin ∂Δ[n] Λ[m, j]).ι := by
  refine (Subcomplex.morphismProperty_ι_iff_of_preimage_eq _ (stdSimplexIso n m)
    (preimage_unionJoin_boundary_horn n (NeZero.ne m) j)).2 ?_
  exact rightAnodyneExtensions.horn_ι
    (Fin.lt_def.2 (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero]; omega))

/-- The pushout-join of any positive-dimensional horn with a boundary is left anodyne. -/
lemma leftAnodyneExtensions_unionJoin_horn_boundary (m : ℕ) {n : ℕ} [NeZero n]
    (i : Fin (n + 1)) :
    leftAnodyneExtensions (Subcomplex.unionJoin Λ[n, i] ∂Δ[m]).ι := by
  refine (Subcomplex.morphismProperty_ι_iff_of_preimage_eq _ (stdSimplexIso n m)
    (preimage_unionJoin_horn_boundary m (NeZero.ne n) i)).2 ?_
  exact leftAnodyneExtensions.horn_ι
    (Fin.lt_def.2 (by simp only [Fin.val_castLE, Fin.val_last]; omega))

end join

variable {A B K L X S P : SSet.{u}}

namespace slice

/-- The relative slice of a left fibration along a monomorphism is a Kan fibration. -/
instance fibration_restrictionMap_of_leftFibration (i : L ⟶ K) [Mono i] (p : X ⟶ S)
    [LeftFibration p] (σ : K ⟶ X) : Fibration (restrictionMap i p σ) := by
  rw [fibration_iff]
  intro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨m, ⟨k⟩⟩ := h
  apply (forall_hasLiftingProperty_restrictionMap_iff _ i p).2 ?_ σ
  intro τ
  exact coslice.hasLiftingProperty_restrictionMap_of_unionJoin _ p
    (fun n ↦ (join.leftAnodyneExtensions_unionJoin_horn_boundary n k).hasLiftingProperty p) τ i

end slice

namespace coslice

/-- The relative coslice of a right fibration along a monomorphism is a Kan fibration. -/
instance fibration_restrictionMap_of_rightFibration (j : A ⟶ B) [Mono j] (p : X ⟶ S)
    [RightFibration p] (τ : B ⟶ X) : Fibration (restrictionMap j p τ) := by
  rw [fibration_iff]
  intro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨m, ⟨k⟩⟩ := h
  apply (slice.forall_hasLiftingProperty_restrictionMap_iff j Λ[m + 1, k].ι p).1 ?_ τ
  intro σ
  exact slice.hasLiftingProperty_restrictionMap_of_unionJoin _ p
    (fun n ↦ (join.rightAnodyneExtensions_unionJoin_boundary_horn n k).hasLiftingProperty p) σ j

end coslice

namespace join

variable {j : A ⟶ B} {i : L ⟶ K} {f : join A K ⟶ P} {g : join B L ⟶ P}
  {u : P ⟶ join B K}

/-- The pushout-join of a monomorphism with a Kan-anodyne extension is right anodyne,
for any chosen pushout of `A ⋆ K ← A ⋆ L → B ⋆ L`. -/
lemma rightAnodyneExtensions_of_isPushout [Mono j] (hi : anodyneExtensions i)
    (h : IsPushout (map (𝟙 A) i) (map j (𝟙 L)) f g)
    (hf : f ≫ u = map j (𝟙 K)) (hg : g ≫ u = map (𝟙 B) i) :
    rightAnodyneExtensions u := by
  rw [rightAnodyneExtensions_eq_llp]
  intro X S p hp
  have : RightFibration p := ⟨hp⟩
  apply (coslice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout j i p h hf hg).1
  intro τ
  exact hi _ (mem_fibrations (coslice.restrictionMap j p τ))

/-- The pushout-join of a Kan-anodyne extension with a monomorphism is left anodyne,
for any chosen pushout of `A ⋆ K ← A ⋆ L → B ⋆ L`. -/
lemma leftAnodyneExtensions_of_isPushout (hj : anodyneExtensions j) [Mono i]
    (h : IsPushout (map (𝟙 A) i) (map j (𝟙 L)) f g)
    (hf : f ≫ u = map j (𝟙 K)) (hg : g ≫ u = map (𝟙 B) i) :
    leftAnodyneExtensions u := by
  rw [leftAnodyneExtensions_eq_llp]
  intro X S p hp
  have : LeftFibration p := ⟨hp⟩
  apply (slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout j i p h hf hg).1
  intro σ
  exact hj _ (mem_fibrations (slice.restrictionMap i p σ))

/-- The union-join inclusion of two subcomplexes is right anodyne if the second inclusion
is Kan-anodyne. -/
lemma rightAnodyneExtensions_unionJoin_ι (A₀ : A.Subcomplex) (B₀ : B.Subcomplex)
    (hB : anodyneExtensions B₀.ι) : rightAnodyneExtensions (A₀.unionJoin B₀).ι :=
  rightAnodyneExtensions_of_isPushout hB (Subcomplex.unionJoin.isPushout A₀ B₀)
    (Subcomplex.unionJoin.ι₁_ι A₀ B₀) (Subcomplex.unionJoin.ι₂_ι A₀ B₀)

/-- The union-join inclusion of two subcomplexes is left anodyne if the first inclusion
is Kan-anodyne. -/
lemma leftAnodyneExtensions_unionJoin_ι (A₀ : A.Subcomplex) (B₀ : B.Subcomplex)
    (hA : anodyneExtensions A₀.ι) : leftAnodyneExtensions (A₀.unionJoin B₀).ι :=
  leftAnodyneExtensions_of_isPushout hA (Subcomplex.unionJoin.isPushout A₀ B₀)
    (Subcomplex.unionJoin.ι₁_ι A₀ B₀) (Subcomplex.unionJoin.ι₂_ι A₀ B₀)

end join

end SSet
