/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

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
(`GenLoop.map_toSphere_sphereGenLoop`), so this is the universal example of the Hurewicz map: it
pins down the Hurewicz map on all spaces up to its value on `π_{n+1}(Sⁿ⁺¹)`.

The proof reads the Hurewicz class in the local homology `Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})` at the south pole
`s`, the image of the centre `0` of the disk `Dⁿ⁺¹` under `TauCeti.closedBallToSphere`, through
which `TauCeti.cubeToSphere` factors.

* The punctured sphere `Sⁿ⁺¹ ∖ {s}` is contractible, so `Hₙ₊₁(Sⁿ⁺¹) ⟶ Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})` is an
  isomorphism.
* The boundary sphere `Sⁿ` of the disk is a deformation retract of `Dⁿ⁺¹ ∖ {0}`
  (`StarConvex.sphereHomotopyEquiv`), so by the five lemma
  `(Dⁿ⁺¹, Sⁿ) ⟶ (Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0})` induces isomorphisms on relative homology.
* The collapse map is a homeomorphism from the open ball onto `Sⁿ⁺¹ ∖ {N}`, and only the centre
  goes to `s`. Excising the boundary sphere of the disk and the north pole of the sphere
  (`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`,
  `TopPair.isIso_singularHomologyMap_of_open_cover`) shows that
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

/-- The centre of the disk `Dⁿ⁺¹`. -/
private def diskCenter : TopCat.disk.{0} (n + 1) :=
  (ULift.up ⟨0, mem_closedBall_self zero_le_one⟩ :
    ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

/-- The south pole of `Sⁿ⁺¹`, the image of the centre of the disk. -/
private abbrev southPole : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  diskToSphere n (diskCenter n)

/-- Only the centre of the disk goes to the south pole. -/
private lemma diskToSphere_eq_southPole_iff {z : TopCat.disk.{0} (n + 1)} :
    diskToSphere n z = southPole n ↔ z = diskCenter n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [southPole, diskToSphere_apply, diskToSphere_apply,
    closedBallToSphere_eq_closedBallToSphere_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact ULift.ext h
  · simp [diskCenter] at h

/-- Only the boundary sphere of the disk goes to the north pole. -/
private lemma diskToSphere_eq_sphereNorthPole_iff {z : TopCat.disk.{0} (n + 1)} :
    diskToSphere n z = sphereNorthPole (n + 1) ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{0} (n + 1)) := by
  rw [diskToSphere_apply, closedBallToSphere_eq_sphereNorthPole_iff,
    mem_range_diskBoundaryInclusion_iff]

private lemma southPole_ne_sphereNorthPole : southPole n ≠ sphereNorthPole (n + 1) := by
  rw [Ne, diskToSphere_eq_sphereNorthPole_iff, mem_range_diskBoundaryInclusion_iff]
  simp [diskCenter]

/-! ### The boundary sphere is a deformation retract of the punctured disk -/

/-- The inclusion of pairs `(Dⁿ⁺¹, Sⁿ) ⟶ (Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0})`. -/
private def diskBoundaryPairToComplCenter :
    diskBoundaryPair.{0} (n + 1) ⟶
      TopPair.ofSubset ({diskCenter n}ᶜ : Set (TopCat.disk.{0} (n + 1))) :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun s ↦ ⟨TopCat.diskBoundaryInclusion (n + 1) s, fun h ↦ by
    have := (mem_range_diskBoundaryInclusion_iff _).1 ⟨s, rfl⟩
    rw [h] at this
    simp [diskCenter] at this⟩,
    (TopCat.diskBoundaryInclusion (n + 1)).hom.continuous.subtype_mk _⟩) rfl

/-- The punctured closed ball of `EuclideanSpace ℝ (Fin (n + 1))` is the punctured disk
`Dⁿ⁺¹ ∖ {0}`. -/
private def complCenterHomeomorph :
    ↥(closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 \ {0}) ≃ₜ
      ↥({diskCenter n}ᶜ : Set (TopCat.disk.{0} (n + 1))) where
  toFun z := ⟨(ULift.up ⟨z, z.2.1⟩ : ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)),
    fun h ↦ z.2.2 (congrArg (fun w : ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      ↦ (w.down : EuclideanSpace ℝ (Fin (n + 1)))) h)⟩
  invFun w := ⟨((w : TopCat.disk.{0} (n + 1)) :
      ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down,
    ((w : TopCat.disk.{0} (n + 1)) :
      ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down.2,
    fun h ↦ w.2 (ULift.ext (Subtype.ext h))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **The punctured disk retracts onto its boundary**: `(Dⁿ⁺¹, Sⁿ) ⟶ (Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0})` induces
isomorphisms on relative singular homology. -/
private lemma isIso_singularHomologyMap_diskBoundaryPairToComplCenter (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (diskBoundaryPairToComplCenter n) R k) := by
  have hfst (m : ℕ) : IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopPair.Hom.fst (diskBoundaryPairToComplCenter n))) R m) := by
    have : IsIso (TopPair.Hom.fst (diskBoundaryPairToComplCenter n)) := IsIso.id _
    infer_instance
  -- The subspace map is the inclusion of the boundary sphere into the punctured disk, a homotopy
  -- equivalence by radial projection.
  let e := (Homeomorph.ulift.{0} (X := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      TopCat.diskBoundary.{0} (n + 1) ≃ₜ _).toHomotopyEquiv.trans
    ((((convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).starConvex
      (mem_closedBall_self zero_le_one)).sphereHomotopyEquiv one_pos
        sphere_subset_closedBall).trans (complCenterHomeomorph n).toHomotopyEquiv)
  have he : TopCat.ofHom e.toFun = TopPair.Hom.snd (diskBoundaryPairToComplCenter n) := by
    ext s
    apply ULift.ext
    apply Subtype.ext
    exact (StarConvex.coe_sphereHomotopyEquiv_apply _ _ _ _).trans
      (TopCat.coe_diskBoundaryInclusion_apply_down (n + 1) s).symm
  have hsnd (m : ℕ) : IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopPair.Hom.snd (diskBoundaryPairToComplCenter n))) R m) := by
    have := (e.singularHomologyIso R m).isIso_hom
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, he] at this
    exact this
  exact TopPair.isIso_singularHomologyMap_of_isIso R _ k (hfst k) (hsnd k) (fun m _ ↦ hfst m)
    fun m _ ↦ hsnd m

/-! ### The collapse map near the centre of the disk -/

private lemma mapsTo_diskToSphere_compl :
    MapsTo (diskToSphere n) ({diskCenter n}ᶜ : Set (TopCat.disk.{0} (n + 1)))
      ({southPole n}ᶜ : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) :=
  fun _ hz h ↦ hz ((diskToSphere_eq_southPole_iff n).1 h)

/-- The collapse map as a map of pairs `(Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0}) ⟶ (Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})`. -/
private def diskToSpherePairMap :
    TopPair.ofSubset ({diskCenter n}ᶜ : Set (TopCat.disk.{0} (n + 1))) ⟶
      TopPair.ofSubset
        ({southPole n}ᶜ : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) :=
  TopPair.ofSubsetMap (diskToSphere n) (mapsTo_diskToSphere_compl n)

/-- The interior of the disk, the preimage of the complement of the north pole. -/
private abbrev diskInterior : Set (TopCat.disk.{0} (n + 1)) :=
  diskToSphere n ⁻¹' {sphereNorthPole (n + 1)}ᶜ

/-- On the interior of the disk the collapse map is an embedding. -/
private lemma isEmbedding_diskToSphere_restrict :
    IsEmbedding (fun z : diskInterior n ↦ diskToSphere n z.1) := by
  refine IsEmbedding.subtypeVal.comp (g := Subtype.val) (f := ({sphereNorthPole (n + 1)}ᶜ :
    Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)).restrictPreimage (diskToSphere n)) ?_
  have : CompactSpace (TopCat.disk.{0} (n + 1)) :=
    (Homeomorph.ulift.{0}
      (X := closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).symm.compactSpace
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap
    ((diskToSphere n).hom.continuous.restrictPreimage) ?_
    (IsClosedMap.restrictPreimage (diskToSphere n).hom.continuous.isClosedMap _)).isEmbedding
  intro z w h
  have h' : diskToSphere n z = diskToSphere n w := congrArg Subtype.val h
  rw [diskToSphere_apply, diskToSphere_apply, closedBallToSphere_eq_closedBallToSphere_iff] at h'
  rcases h' with h' | ⟨h', -⟩
  · exact Subtype.ext (ULift.ext h')
  · exact (z.2 ((diskToSphere_eq_sphereNorthPole_iff n).2
      ((mem_range_diskBoundaryInclusion_iff _).2 h'))).elim

/-- **Local homology at the centre of the disk.** The collapse map induces isomorphisms
`Hₖ(Dⁿ⁺¹, Dⁿ⁺¹ ∖ {0}) ≅ Hₖ(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {s})`. -/
private lemma isIso_singularHomologyMap_diskToSpherePairMap (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (diskToSpherePairMap n) R k) := by
  have hcU : diskCenter n ∈ diskInterior n := southPole_ne_sphereNorthPole n
  have hexc := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.disk.{0} (n + 1)) (isOpen_compl_singleton.preimage (diskToSphere n).hom.continuous)
    isClosed_singleton (singleton_subset_iff.2 hcU) k
  have hfst' (z : diskInterior n) : TopPair.Hom.fst
      (TopPair.excisionMap (diskInterior n) {diskCenter n}ᶜ ≫ diskToSpherePairMap n) z =
        diskToSphere n z.1 := by
    exact (congrArg (TopPair.Hom.fst (diskToSpherePairMap n))
      (TopPair.excisionMap_fst_apply (diskInterior n) {diskCenter n}ᶜ z)).trans
        (TopPair.ofSubsetMap_fst_apply (diskToSphere n) _ z.1)
  have hfst : ⇑(ConcreteCategory.hom (TopPair.Hom.fst
      (TopPair.excisionMap (diskInterior n) {diskCenter n}ᶜ ≫ diskToSpherePairMap n))) =
        fun z : diskInterior n ↦ diskToSphere n z.1 :=
    funext hfst'
  -- Excise the boundary of the disk and the north pole of the sphere.
  have hcomp : IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (diskInterior n) {diskCenter n}ᶜ ≫ diskToSpherePairMap n) R k) := by
    refine TopPair.isIso_singularHomologyMap_of_open_cover R _ ?_ ?_
      (fun b : Bool ↦ bif b
        then ({southPole n}ᶜ : Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))
        else ({sphereNorthPole (n + 1)}ᶜ :
          Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))))
      (fun b ↦ by
        cases b
        · exact isOpen_compl_singleton (X := sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
        · exact isOpen_compl_singleton (X := sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
      ?_ (fun b ↦ ?_) k
    · rw [hfst]
      exact isEmbedding_diskToSphere_restrict n
    · intro z hz
      rw [TopPair.range_ofSubset_map] at hz ⊢
      exact fun h ↦ hz ((hfst' z).trans (congrArg (diskToSphere n) (Set.mem_singleton_iff.1 h)))
    · refine eq_univ_of_forall fun y ↦ mem_iUnion.2 ?_
      by_cases hy : y = southPole n
      · exact ⟨false, hy ▸ southPole_ne_sphereNorthPole n⟩
      · exact ⟨true, hy⟩
    · cases b
      · refine Or.inr fun y (hy : y ≠ sphereNorthPole (n + 1)) ↦ ?_
        obtain ⟨z, hz⟩ := closedBallToSphere_surjective (n := n + 1) y
        have hz' : diskToSphere n
            (ULift.up z : ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) = y := hz
        exact ⟨⟨_, show _ ∈ ({sphereNorthPole (n + 1)}ᶜ : Set _) from hz' ▸ hy⟩,
          (hfst' _).trans hz'⟩
      · exact Or.inl TopPair.range_ofSubset_map.symm.subset
  rw [TopPair.singularHomologyMap_comp] at hcomp
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hexc hcomp

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
      diskBoundaryPairToComplCenter n ≫ diskToSpherePairMap n := by
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
  -- Both sides are now the collapse map at `z`: `diskBoundaryPairToComplCenter` is the identity
  -- on the disk, and `TauCeti.diskToSphere_apply` holds by definition.
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
  have hπs : IsIso ((TopPair.ofSubset ({southPole n}ᶜ :
      Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).singularHomologyπ
        R (n + 1)) :=
    TopPair.isIso_singularHomologyπ_of_contractibleSpace _ R n
  have := isIso_singularHomologyMap_diskBoundaryPairToComplCenter n R (n + 1)
  have := isIso_singularHomologyMap_diskToSpherePairMap n R (n + 1)
  have hfac : GenLoop.hurewicz R (sphereGenLoop (n + 1)) ≫
      (TopPair.ofSubset ({southPole n}ᶜ :
        Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).singularHomologyπ
          R (n + 1) =
      (singularHomologyDiskBoundaryPairIso R (n + 1)).inv ≫
        TopPair.singularHomologyMap (diskBoundaryPairToComplCenter n) R (n + 1) ≫
          TopPair.singularHomologyMap (diskToSpherePairMap n) R (n + 1) := by
    rw [← hπ, GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_assoc,
      singularHomologyCubeBoundaryPairIso_inv, Category.assoc,
      ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
      diskBoundaryPairToCube_comp_toCubeBoundaryPairHom, TopPair.singularHomologyMap_comp]
  have : IsIso (GenLoop.hurewicz R (sphereGenLoop (n + 1)) ≫
      (TopPair.ofSubset ({southPole n}ᶜ :
        Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))).singularHomologyπ
          R (n + 1)) := by
    rw [hfac]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπs this

end TauCeti
