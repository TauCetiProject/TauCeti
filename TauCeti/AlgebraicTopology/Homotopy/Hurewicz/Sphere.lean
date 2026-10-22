/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.AlgebraicTopology.Sphere.Puncture

/-!
# The Hurewicz class of the tautological loop of a sphere

The map `TauCeti.cubeToSphere : Iⁿ⁺¹ → Sⁿ⁺¹` collapses the boundary of the cube to the north pole
`N`, so it is a generalized loop `TauCeti.sphereGenLoop (n + 1)` of the sphere at `N`. This file
proves that its Hurewicz class generates the top homology of the sphere: the morphism
`GenLoop.hurewicz R (sphereGenLoop (n + 1)) : R ⟶ Hₙ₊₁(Sⁿ⁺¹; R)` is an isomorphism, for
coefficients `R` in any abelian category with coproducts
(`TauCeti.isIso_hurewicz_sphereGenLoop`). In other words, the quotient map
`(Iⁿ⁺¹, ∂Iⁿ⁺¹) → (Sⁿ⁺¹, N)` sends the fundamental class of the cube to a fundamental class of the
sphere.

Every generalized loop factors through the tautological one
(`GenLoop.map_toSphere_sphereGenLoop`), so this is the universal example of the Hurewicz map: every
Hurewicz class is the image of that of the tautological loop
(`GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp`), which pins down the Hurewicz map on all spaces
up to its value on `π_{n+1}(Sⁿ⁺¹)`.

The proof reads the Hurewicz class in the local homology `Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})` at the south pole
`s`, the image of the centre `0` of the disk `Dⁿ⁺¹` under `TauCeti.closedBallToSphere`, through
which `TauCeti.cubeToSphere` factors.

* The punctured sphere `Sⁿ⁺¹ ∖ {s}` is contractible, so `Hₙ₊₁(Sⁿ⁺¹) ⟶ Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})` is an
  isomorphism.
* The boundary sphere `Sⁿ` of the disk is a deformation retract of `Dⁿ⁺¹ ∖ {0}`, so
  `(Dⁿ⁺¹, Sⁿ) ⟶ (Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0})` induces isomorphisms on relative homology
  (`TauCeti.isIso_singularHomologyMap_diskBoundaryPairToComplDiskCenter`).
* The collapse map is a homeomorphism from the open ball onto `Sⁿ⁺¹ ∖ {N}`, and only the centre
  goes to `s`. So it is a chart at the centre of the disk, and the local homology comparison
  `TauCeti.singularHomologyComplSingletonIsoOfChart` shows that
  `(Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0}) ⟶ (Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})` induces isomorphisms on relative homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.22 (the quotient map of a good pair, here
  `(Dⁿ, ∂Dⁿ) → (Dⁿ / ∂Dⁿ, pt)`), and Section 4.2, the Hurewicz map.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology AlgebraicTopology
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable (n : ℕ)

/-- The collapse `x ↦ (2 √(1 - ‖x‖²) x, 2 ‖x‖² - 1)` of the disk `Dⁿ⁺¹` onto the sphere `Sⁿ⁺¹`,
through which `TauCeti.cubeToSphere` factors. -/
private def diskToSphere :
    TopCat.disk.{0} (n + 1) ⟶ TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  TopCat.ofHom ((closedBallToSphere (n + 1)).comp
    (Homeomorph.ulift.{0} (X := closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      C(ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1), _)))

private lemma diskToSphere_apply (z : TopCat.disk.{0} (n + 1)) :
    diskToSphere n z = closedBallToSphere (n + 1)
      (z : ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :=
  (rfl)

/-- Only the boundary sphere of the disk goes to the north pole. -/
private lemma diskToSphere_eq_sphereNorthPole_iff {z : TopCat.disk.{0} (n + 1)} :
    diskToSphere n z = sphereNorthPole (n + 1) ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{0} (n + 1)) := by
  rw [diskToSphere_apply, closedBallToSphere_eq_sphereNorthPole_iff,
    mem_range_diskBoundaryInclusion_iff]

/-! ### The collapse map on the interior of the disk -/

/-- The interior of the disk, the preimage of the complement of the north pole. -/
private abbrev diskInterior : Set (TopCat.disk.{0} (n + 1)) :=
  diskToSphere n ⁻¹' {sphereNorthPole (n + 1)}ᶜ

/-- The collapse map is a bijection from the interior of the disk onto the complement of the
north pole. -/
private lemma bijOn_diskToSphere :
    BijOn (diskToSphere n) (diskInterior n) {sphereNorthPole (n + 1)}ᶜ := by
  refine ⟨fun _ hz ↦ hz, fun z hz w hw h ↦ ?_, fun y hy ↦ ?_⟩
  · rw [diskToSphere_apply, diskToSphere_apply, closedBallToSphere_eq_closedBallToSphere_iff] at h
    rcases h with h | ⟨h, -⟩
    · exact ULift.ext h
    · exact (hz ((diskToSphere_eq_sphereNorthPole_iff n).2
        ((mem_range_diskBoundaryInclusion_iff _).2 h))).elim
  · obtain ⟨z, hz⟩ := closedBallToSphere_surjective (n := n + 1) y
    have hz' : diskToSphere n
        (ULift.up z : ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) = y :=
      (diskToSphere_apply n _).trans hz
    exact ⟨_, Set.mem_compl_singleton_iff.2 (hz' ▸ hy), hz'⟩

/-- On the interior of the disk the collapse map is an open embedding. -/
private lemma isOpenEmbedding_diskToSphere_domRestrict :
    IsOpenEmbedding ((diskInterior n).domRestrict (diskToSphere n)) := by
  have : CompactSpace (TopCat.disk.{0} (n + 1)) :=
    (Homeomorph.ulift.{0}
      (X := closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).symm.compactSpace
  refine ⟨IsEmbedding.subtypeVal.comp (g := Subtype.val) (f := ({sphereNorthPole (n + 1)}ᶜ :
    Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)).restrictPreimage (diskToSphere n))
      (IsClosedEmbedding.of_continuous_injective_isClosedMap
        ((diskToSphere n).hom.continuous.restrictPreimage) ?_
        (IsClosedMap.restrictPreimage (diskToSphere n).hom.continuous.isClosedMap _)).isEmbedding,
    ?_⟩
  · exact fun z w h ↦ Subtype.ext ((bijOn_diskToSphere n).injOn z.2 w.2 (congrArg Subtype.val h))
  · rw [range_domRestrict, (bijOn_diskToSphere n).image_eq]
    exact isOpen_compl_singleton

/-- The collapse map as an open partial homeomorphism from the interior of the disk onto the
complement of the north pole. -/
private def diskToSphereChart :
    OpenPartialHomeomorph (TopCat.disk.{0} (n + 1))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((bijOn_diskToSphere n).toPartialEquiv _ _ _) (diskToSphere n).hom.continuous.continuousOn
    (isOpenEmbedding_diskToSphere_domRestrict n).isOpenMap
    (isOpen_compl_singleton.preimage (diskToSphere n).hom.continuous)

private lemma diskToSphereChart_apply (z : TopCat.disk.{0} (n + 1)) :
    diskToSphereChart n z = diskToSphere n z :=
  (rfl)

/-- The south pole of `Sⁿ⁺¹`, the image of the centre of the disk. -/
private abbrev southPole : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  diskToSphereChart n (diskCenter (n + 1))

/-- Only the centre of the disk goes to the south pole. -/
private lemma diskToSphere_eq_southPole_iff {z : TopCat.disk.{0} (n + 1)} :
    diskToSphere n z = southPole n ↔ z = diskCenter (n + 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [southPole, diskToSphereChart_apply, diskToSphere_apply, diskToSphere_apply,
    closedBallToSphere_eq_closedBallToSphere_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact ULift.ext h
  · simp at h

private lemma southPole_ne_sphereNorthPole : southPole n ≠ sphereNorthPole (n + 1) := by
  rw [Ne, southPole, diskToSphereChart_apply, diskToSphere_eq_sphereNorthPole_iff]
  exact diskCenter_notMem_range_diskBoundaryInclusion (n + 1)

private lemma diskCenter_mem_diskToSphereChart_source :
    diskCenter (n + 1) ∈ (diskToSphereChart n).source :=
  southPole_ne_sphereNorthPole n

private lemma mapsTo_diskToSphere_compl :
    MapsTo (diskToSphere n) ({diskCenter (n + 1)}ᶜ : Set (TopCat.disk.{0} (n + 1)))
      ({southPole n}ᶜ : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) :=
  fun _ hz h ↦ hz ((diskToSphere_eq_southPole_iff n).1 h)

/-- The collapse map as a map of pairs `(Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0}) ⟶ (Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})`. -/
private def diskToSpherePairMap :
    TopPair.ofSubset ({diskCenter (n + 1)}ᶜ : Set (TopCat.disk.{0} (n + 1))) ⟶
      TopPair.ofSubset
        ({southPole n}ᶜ : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) :=
  TopPair.ofSubsetMap (diskToSphere n) (mapsTo_diskToSphere_compl n)

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **Local homology at the centre of the disk.** The collapse map induces isomorphisms
`Hₖ(Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0}) ≅ Hₖ(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})`, since it is a homeomorphism near the centre. -/
private lemma isIso_singularHomologyMap_diskToSpherePairMap (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (diskToSpherePairMap n) R k) := by
  have hx := diskCenter_mem_diskToSphereChart_source n
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.of (TopCat.disk.{0} (n + 1))) (diskToSphereChart n).open_source
    isClosed_singleton (singleton_subset_iff.2 hx) k
  have hfac := singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom
    R (diskToSphereChart n) hx k
  rw [← TopPair.singularHomologyMap_comp] at hfac
  -- Excision onto the source followed by the collapse map is the homeomorphism of the chart
  -- followed by excision onto the target.
  have hpair : TopPair.excisionMap (X := TopCat.of (TopCat.disk.{0} (n + 1)))
      (diskToSphereChart n).source {diskCenter (n + 1)}ᶜ ≫ diskToSpherePairMap n =
      (TopPair.ofSubsetIso (X := TopCat.of (diskToSphereChart n).source)
        (Y := TopCat.of (diskToSphereChart n).target) (diskToSphereChart n).toHomeomorphSourceTarget
        (B := Subtype.val ⁻¹' {diskCenter (n + 1)}ᶜ)
        (B' := Subtype.val ⁻¹' {diskToSphereChart n (diskCenter (n + 1))}ᶜ)
        fun z ↦ ((diskToSphereChart n).injOn.eq_iff z.2 hx).not.symm).hom ≫
      TopPair.excisionMap (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
        (diskToSphereChart n).target {diskToSphereChart n (diskCenter (n + 1))}ᶜ := by
    apply TopPair.hom_ext_of_fst
    ext z
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    -- The ambient spaces of these pairs are subspaces presented through `TopPair.ofSubset`, so
    -- the evaluation lemmas only match after unfolding.
    erw [TopPair.excisionMap_fst_apply, TopPair.excisionMap_fst_apply, TopPair.ofSubsetIso_hom,
      TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    rfl
  rw [← hpair, TopPair.singularHomologyMap_comp, cancel_epi] at hfac
  rw [← hfac]
  infer_instance

/-! ### The Hurewicz class of the tautological loop -/

private lemma mapsTo_id_sphereNorthPole :
    MapsTo (𝟙 (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))
      ({sphereNorthPole (n + 1)} :
        Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))
      ({southPole n}ᶜ : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) := by
  rintro _ rfl h
  exact southPole_ne_sphereNorthPole n h.symm

/-- The tautological loop, read on the disk, is the collapse map: the composite
`(Dⁿ⁺¹, Sⁿ) ⟶ (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (Sⁿ⁺¹, {N}) ⟶ (Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})` is the composite
`(Dⁿ⁺¹, Sⁿ) ⟶ (Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0}) ⟶ (Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})`. -/
private lemma diskBoundaryPairToCube_comp_toCubeBoundaryPairHom :
    diskBoundaryPairToCube.{0} (n + 1) ≫
        GenLoop.toCubeBoundaryPairHom (sphereGenLoop (n + 1)) ≫
          TopPair.ofSubsetMap (𝟙 _) (mapsTo_id_sphereNorthPole n) =
      diskBoundaryPairToComplDiskCenter (n + 1) ≫ diskToSpherePairMap n := by
  apply TopPair.hom_ext_of_fst
  ext z
  rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply,
    GenLoop.toCubeBoundaryPairHom_fst_apply, diskBoundaryPairToCube_fst_apply_down]
  -- The ambient spaces of these pairs are presented through `TopPair.ofSubset` and
  -- `TopCat.disk`, so the evaluation lemmas only match after unfolding.
  erw [TopPair.ofSubsetMap_fst_apply]
  rw [sphereGenLoop_apply, cubeToSphere_apply]
  erw [Homeomorph.symm_apply_apply]
  rw [diskBoundaryPairToComplDiskCenter_fst]
  -- Both sides are now the collapse map at `z`, since `TauCeti.diskToSphere_apply` holds by
  -- definition.
  rfl

/-- **The Hurewicz class of the tautological loop generates the top homology of the sphere.**
The class of `TauCeti.cubeToSphere : (Iⁿ⁺¹, ∂Iⁿ⁺¹) → (Sⁿ⁺¹, N)` under the Hurewicz map is an
isomorphism `R ≅ Hₙ₊₁(Sⁿ⁺¹; R)`: the collapse of the boundary of the cube sends the fundamental
class of the cube to a fundamental class of the sphere. -/
instance isIso_hurewicz_sphereGenLoop :
    IsIso (GenLoop.hurewicz R (sphereGenLoop (n + 1))) := by
  have hN := mapsTo_id_sphereNorthPole n
  -- Read the class in the local homology at the south pole.
  have hπ : (singularHomologyIsoOfSubsetSingleton R n (sphereNorthPole (n + 1))).hom ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hN) R (n + 1) =
        (TopPair.ofSubset ({southPole n}ᶜ :
          Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).singularHomologyπ
            R (n + 1) := by
    have h := TopPair.singularHomologyπ_naturality (R := R) (TopPair.ofSubsetMap (𝟙 _) hN) (n + 1)
    -- The ambient space of `TopPair.ofSubset` is `TopCat.of` of the sphere only up to unfolding,
    -- so the identity is matched by `erw`.
    erw [TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id, SSet.homologyMap_id,
      Category.id_comp] at h
    rw [singularHomologyIsoOfSubsetSingleton_hom]
    exact h.symm
  have : ContractibleSpace (TopPair.ofSubset ({southPole n}ᶜ :
      Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).snd :=
    contractibleSpace_sphere_compl_singleton _
  -- The source of the quotient map is the homology of the singular simplicial set; it is stated
  -- here as the singular homology of the sphere, the form it takes after the Hurewicz class, so
  -- that instance search finds it there.
  have : IsIso (X := ((singularHomologyFunctor C (n + 1)).obj R).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))
      ((TopPair.ofSubset ({southPole n}ᶜ :
        Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).singularHomologyπ
          R (n + 1)) :=
    TopPair.isIso_singularHomologyπ_of_contractibleSpace _ R n
  have := isIso_singularHomologyMap_diskBoundaryPairToComplDiskCenter R (n + 1) (n + 1)
  have := isIso_singularHomologyMap_diskToSpherePairMap n R (n + 1)
  have hfac : GenLoop.hurewicz R (sphereGenLoop (n + 1)) ≫
      (TopPair.ofSubset ({southPole n}ᶜ :
        Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).singularHomologyπ
          R (n + 1) =
      (singularHomologyDiskBoundaryPairIso R (n + 1)).inv ≫
        TopPair.singularHomologyMap (diskBoundaryPairToComplDiskCenter (n + 1)) R (n + 1) ≫
          TopPair.singularHomologyMap (diskToSpherePairMap n) R (n + 1) := by
    rw [← hπ, GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_assoc,
      singularHomologyCubeBoundaryPairIso_inv, Category.assoc,
      ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
      diskBoundaryPairToCube_comp_toCubeBoundaryPairHom, TopPair.singularHomologyMap_comp]
  exact IsIso.of_isIso_fac_right hfac

end TauCeti

namespace GenLoop

open TauCeti

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C) {n : ℕ}
  {X : Type} [TopologicalSpace X] {x : X}

/-- **Every Hurewicz class is the image of that of the tautological loop**: the Hurewicz class of
a generalized loop `p` is the image of the Hurewicz class of `TauCeti.sphereGenLoop (n + 1)` under
`(GenLoop.toSphere p)_* : Hₙ₊₁(Sⁿ⁺¹; R) ⟶ Hₙ₊₁(X; R)`. -/
theorem hurewicz_eq_hurewicz_sphereGenLoop_comp (p : Ω^ (Fin (n + 1)) X x) :
    hurewicz R p = hurewicz R (sphereGenLoop (n + 1)) ≫
      ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom (toSphere p)) := by
  rw [← hurewicz_map R (toSphere p) (toSphere_sphereNorthPole p), map_toSphere_sphereGenLoop]

end GenLoop
