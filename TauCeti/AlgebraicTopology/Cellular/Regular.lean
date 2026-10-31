/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.End
public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere

/-!
# Incidence numbers at embedded points of attaching maps

The cellular incidence number `[j : i]` of an `n`-cell `i` in the boundary of an `(n + 1)`-cell
`j` is the local degree of the attaching map `f` of `j` at a point `x` of the open cell `i`
(`TauCeti.singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul`). This file computes that
local degree in the simplest situation, where `f` is an embedding near the points over `x`.

* If `f` restricts to an embedding on a set `U` of the boundary sphere whose image contains the
  open cell `i`, then for the point `y ∈ U` over `x` the map `f` induces isomorphisms
  `Hₖ(U, U ∖ {y}) ⟶ Hₖ(Xⁿ, Xⁿ ∖ {x})`, by excision of the complement of `x` and of the open cell
  (`TauCeti.isIso_singularHomologyMap_cellAttachingMap_domRestrict`).
* If moreover `U` is open and `y` is the only point over `x`, then the local degree is a
  generator: for `n > 0` the incidence number is a unit of the coefficient ring
  (`TauCeti.isUnit_cellularIncidence_of_isEmbedding`).
* In particular, if the attaching map of `j` is injective, as in a regular CW complex, then every
  `n`-cell whose open cell lies in the frontier of `j` has unit incidence number
  (`TauCeti.isUnit_cellularIncidence_of_injective`); over `ℤ` it is `±1`.

The sign of the unit depends on the orientations of the characteristic maps and of the sphere
generator, and is not determined here.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2: the cellular boundary formula, and Proposition 2.30 for computing degrees by local
  degrees.
* A. T. Lundell, S. Weingram, *The Topology of CW Complexes*, Van Nostrand Reinhold (1969),
  Chapter V (regular CW complexes, whose incidence numbers are `0` or `±1`).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

section Coefficients

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **Excision near an embedded point of an attaching map.** Let `U` be a set of points of the
boundary sphere of an `(n + 1)`-cell `j` on which its attaching map restricts to an embedding
whose image contains the open `n`-cell `i`, and let `y` lie over a point of that open cell. Then
the attaching map induces isomorphisms from `Hₖ(U, U ∖ {y})` to the local homology of the
`n`-skeleton at the image of `y`. -/
theorem isIso_singularHomologyMap_cellAttachingMap_domRestrict {n : ℕ} {i : cell C n}
    {j : cell C (n + 1)} {U : Set (TopCat.diskBoundary.{w} (n + 1))}
    {y : TopCat.diskBoundary.{w} (n + 1)}
    (hx : ((cellAttachingMap j y : skeletonObj C (n + 1)) : X) ∈ openCell n i)
    (hemb : IsEmbedding (U.domRestrict (cellAttachingMap j)))
    (hsurj : ∀ z : skeletonObj C (n + 1), (z : X) ∈ openCell n i →
      ∃ u ∈ U, cellAttachingMap j u = z)
    (hfU : MapsTo (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(U, TopCat.diskBoundary.{w} (n + 1))) ≫ cellAttachingMap j)
      (Subtype.val ⁻¹' {y}ᶜ : Set U) {cellAttachingMap j y}ᶜ) (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfU) R k) := by
  -- Cover the `n`-skeleton by the open cell `i`, which lies in the image of `U`, and by the
  -- complement of `x`, which is the subspace of the target pair.
  refine TopPair.isIso_singularHomologyMap_of_open_cover R (TopPair.ofSubsetMap _ hfU) ?_ ?_
    (fun b : Bool ↦ bif b
      then (Subtype.val ⁻¹' openCell n i : Set (skeletonObj C (n + 1)))
      else {cellAttachingMap j y}ᶜ)
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · rw [TopPair.ofSubsetMap_fst]
    exact hemb
  · rintro u ⟨z, hz⟩
    refine ⟨⟨u, fun hu ↦ z.2 ?_⟩, rfl⟩
    refine hz.trans ?_
    rw [TopPair.ofSubsetMap_fst_apply]
    exact congrArg (cellAttachingMap j) hu
  · cases b
    · -- The skeleton is `T₁`, but instance search does not see it through the target pair.
      have : T1Space (skeletonObj C (n + 1)) :=
        inferInstanceAs (T1Space (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
      exact @isOpen_compl_singleton _ _ this _
    · exact isOpen_preimage_val_openCell n subset_rfl i
  · refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    by_cases hz : z = cellAttachingMap j y
    · exact ⟨true, hz ▸ hx⟩
    · exact ⟨false, hz⟩
  · cases b
    · exact Or.inl TopPair.range_ofSubset_map.symm.subset
    · refine Or.inr fun z hz ↦ ?_
      obtain ⟨u, hu, rfl⟩ := hsurj z hz
      exact ⟨⟨u, hu⟩, TopPair.ofSubsetMap_fst_apply _ _ _⟩

end Coefficients

section Ring

variable (R : Type w) [Ring R]

/-- **Incidence numbers at an embedded single preimage are units.** Let `y` be a point of the
boundary sphere of an `(n + 2)`-cell `j` whose image `x` under the attaching map lies in the open
`(n + 1)`-cell `i`, such that `y` is the only point over `x` and the attaching map restricts to an
embedding on an open set `U` whose image contains the open cell `i`. Then the incidence number of
`i` in the cellular boundary of `j` is a unit. -/
theorem isUnit_cellularIncidence_of_isEmbedding {n : ℕ} {i : cell C (n + 1)}
    {j : cell C (n + 2)} {U : Set (TopCat.diskBoundary.{w} (n + 2))} (hU : IsOpen U)
    {y : TopCat.diskBoundary.{w} (n + 2)}
    (hx : ((cellAttachingMap j y : skeletonObj C (n + 2)) : X) ∈ openCell (n + 1) i)
    (hfib : ∀ z, cellAttachingMap j z = cellAttachingMap j y → z = y)
    (hemb : IsEmbedding (U.domRestrict (cellAttachingMap j)))
    (hsurj : ∀ z : skeletonObj C (n + 2), (z : X) ∈ openCell (n + 1) i →
      ∃ u ∈ U, cellAttachingMap j u = z) :
    IsUnit (cellularIncidence C R (n + 1) i j) := by
  -- Let `s` be the sphere generator in `Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {y})`. The attaching map sends it to
  -- `[j : i]` times the local class of `i` at `x`, and both `s` and the map it is pushed along are
  -- isomorphisms: the latter by excision of `Sⁿ⁺¹ ∖ U` and the local embedding.
  have hyU : y ∈ U := by
    obtain ⟨u, hu, hfu⟩ := hsurj _ hx
    exact hfib u hfu ▸ hu
  have hfP : MapsTo (cellAttachingMap j) {y}ᶜ {cellAttachingMap j y}ᶜ :=
    fun z hz h ↦ hz (hfib z h)
  have hfU : MapsTo (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
      C(U, TopCat.diskBoundary.{w} (n + 2))) ≫ cellAttachingMap j)
      (Subtype.val ⁻¹' {y}ᶜ : Set U) {cellAttachingMap j y}ᶜ := fun _ hu ↦ hfP hu
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset
    (ModuleCat.of R R) hU isClosed_singleton (singleton_subset_iff.2 hyU) (n + 1)
  have hloc := isIso_singularHomologyMap_cellAttachingMap_domRestrict C (ModuleCat.of R R) hx hemb
    hsurj hfU (n + 1)
  have hfac : TopPair.excisionMap U {y}ᶜ ≫ TopPair.ofSubsetMap _ hfP =
      TopPair.ofSubsetMap _ hfU := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst]
    congr 1
    ext u
    exact TopPair.excisionMap_fst_apply U {y}ᶜ u
  have : IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfP) (ModuleCat.of R R)
      (n + 1)) := by
    rw [← hfac, TopPair.singularHomologyMap_comp] at hloc
    exact IsIso.of_isIso_comp_left (TopPair.singularHomologyMap (TopPair.excisionMap U {y}ᶜ)
      (ModuleCat.of R R) (n + 1)) _
  have := isIso_diskBoundaryFundamentalClass_compl_singleton (ModuleCat.of R R) n y
  have hs : (diskBoundaryFundamentalClass (ModuleCat.of R R) {y}ᶜ ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfP) (ModuleCat.of R R) (n + 1)) 1 =
      cellularIncidence C R (n + 1) i j •
        cellLocalClass C (ModuleCat.of R R) (cellAttachingMap j y) hx 1 := by
    rw [diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap]
    exact singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul C R _ hx j
  exact ModuleCat.isUnit_of_apply_one_eq_smul
    (cellLocalClass C (ModuleCat.of R R) (cellAttachingMap j y) hx)
    (diskBoundaryFundamentalClass (ModuleCat.of R R) {y}ᶜ ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hfP) (ModuleCat.of R R) (n + 1)) hs

/-- **Injective attaching maps have unit incidence numbers.** If the attaching map of an
`(n + 2)`-cell `j` is injective, as in a regular CW complex, then every `(n + 1)`-cell whose open
cell lies in the frontier of `j` has a unit incidence number in the cellular boundary of `j`. -/
theorem isUnit_cellularIncidence_of_injective {n : ℕ} {i : cell C (n + 1)} {j : cell C (n + 2)}
    (hinj : Function.Injective (cellAttachingMap j))
    (hi : openCell (n + 1) i ⊆ cellFrontier (n + 2) j) :
    IsUnit (cellularIncidence C R (n + 1) i j) := by
  have hemb : IsEmbedding (cellAttachingMap j) :=
    ((cellAttachingMap j).hom.continuous.isClosedEmbedding hinj).isEmbedding
  have hsurj (z : skeletonObj C (n + 2)) (hz : (z : X) ∈ openCell (n + 1) i) :
      ∃ u ∈ (univ : Set (TopCat.diskBoundary.{w} (n + 2))), cellAttachingMap j u = z := by
    rw [← range_cellAttachingMap] at hi
    obtain ⟨u, hu⟩ := hi hz
    exact ⟨u, mem_univ _, Subtype.ext hu⟩
  obtain ⟨x₀, hx₀⟩ := openCell_nonempty (n + 1) i
  obtain ⟨y, -, hy⟩ := hsurj ⟨x₀, openCell_subset_skeletonLT (n + 1) i hx₀⟩ hx₀
  have hx : ((cellAttachingMap j y : skeletonObj C (n + 2)) : X) ∈ openCell (n + 1) i :=
    hy ▸ hx₀
  exact isUnit_cellularIncidence_of_isEmbedding C R isOpen_univ hx (fun _ h ↦ hinj h)
    (hemb.comp IsEmbedding.subtypeVal) hsurj

end Ring

end TauCeti
