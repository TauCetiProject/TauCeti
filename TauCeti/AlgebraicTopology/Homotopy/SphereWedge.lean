/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.AlgebraicTopology.Homotopy.CellAttachment
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute

/-!
# The homotopy group of a wedge of spheres in its dimension

The wedge `⋁ᵢ Sⁿ` of `n`-spheres indexed by a type `ι` (`TauCeti.sphereWedge ι n`) is the space
obtained from a point by attaching one `n`-cell along the constant map for each `i : ι`. The
characteristic map of the `i`-th cell, read on the cube through `TauCeti.diskHomeomorphCube`,
sends the boundary of the cube to the base point, so it is a generalized loop
`TauCeti.sphereWedgeLoop ι n i`: the `i`-th sphere of the wedge. This is the CW model of the
wedge, with one `0`-cell and one `n`-cell for each `i`, as needed to compute its homology
cellularly and to attach further cells to it; it is not compared here with the quotient model
`TauCeti.WedgeSum` of a wedge of pointed spaces.

The wedge of `(n + 1)`-spheres is `n`-connected
(`TauCeti.subsingleton_homotopyGroup_sphereWedge`), since attaching `(n + 1)`-cells is onto on
`π_k` for `k ≤ n`. For `n ≥ 2` the classes of the spheres form a basis of the abelian group
`πₙ(⋁ᵢ Sⁿ)`, which is therefore free abelian on `ι` (`TauCeti.sphereWedgeHomotopyGroupBasis`),
with no finiteness assumption on `ι`.

The proof goes through homology. The wedge is `(n - 1)`-connected, so the Hurewicz map is an
isomorphism `πₙ(⋁ᵢ Sⁿ) ≅ Hₙ(⋁ᵢ Sⁿ; ℤ)` (`HomotopyGroup.hurewiczAddEquiv`), and `Hₙ(⋁ᵢ Sⁿ; ℤ)`
is the relative homology of the wedge modulo its base point
(`TauCeti.singularHomologyIsoOfSubsetSingleton`). Read as a relative CW complex over the point,
the wedge has all its cells in dimension `n`, so this relative homology is the cellular chain
group in degree `n`, which has the cellular basis `TauCeti.cellularChainBasis` indexed by the
cells. The Hurewicz class of a sphere is the image of the generator of the disk pair under the
characteristic map of its cell, read on the cube; the cellular basis vector of that cell is the
image of the same generator under the same map, read on the disk. The cube and the disk are
identified by `TauCeti.diskHomeomorphCube`, which the generator of the cube pair is defined to
respect (`TauCeti.singularHomologyCubeBoundaryPairIso_inv`), so the two classes agree on the nose,
without a sign.

This is the first stage of the construction of an Eilenberg–MacLane space `K(A, n)` from a
presentation of an abelian group `A`: start with a wedge of `n`-spheres, one for each generator,
and attach `(n + 1)`-cells along the relations
(`TauCeti.cellAttachmentHomotopyGroupMulEquiv`).

Maps out of the wedge are families of generalized loops. For generalized loops `γ i` at `z` in a
space `Z`, `TauCeti.sphereWedgeLift γ : ⋁ᵢ Sⁿ ⟶ Z` sends the base point to `z` and the `i`-th
sphere onto `γ i`, on the nose (`TauCeti.genLoopMap_sphereWedgeLift_sphereWedgeLoop`), and every
based map out of the wedge is of this form, for the images of its spheres
(`TauCeti.sphereWedgeLift_genLoopMap_sphereWedgeLoop`). Combined with the basis of
`πₙ₊₂(⋁ᵢ Sⁿ⁺²)`, this realizes homomorphisms by maps: every homomorphism
`πₙ₊₂(⋁ᵢ Sⁿ⁺²) → πₙ₊₂(Z, z)` is induced by a based map (`TauCeti.exists_sphereWedge_mapHom_eq`),
and, when `Z` is `(n + 1)`-connected, so is every homomorphism `Hₙ₊₂(⋁ᵢ Sⁿ⁺²; ℤ) → Hₙ₊₂(Z; ℤ)`
on integral homology (`TauCeti.exists_sphereWedge_singularHomologyMap_eq`), through the Hurewicz
isomorphisms of both spaces. This is the first step in mapping the presentation model of
`K(A, n)` to another space: the generator spheres are sent to representatives of the prescribed
classes, before the map is extended over the relation cells and the higher cells.

## Main definitions

* `TauCeti.sphereWedge ι n`: the wedge of `n`-spheres indexed by `ι`, a cell attachment to a
  point.
* `TauCeti.sphereWedgeBase ι n`: its base point.
* `TauCeti.sphereWedgeLoop ι n i`: the `i`-th sphere, as a generalized loop at the base point.
* `TauCeti.sphereWedgeHomotopyGroupBasis ι n`: the basis of `πₙ₊₂(⋁ᵢ Sⁿ⁺²)` given by the classes
  of the spheres (`TauCeti.sphereWedgeHomotopyGroupBasis_apply`).
* `TauCeti.sphereWedgeLift γ`: the map out of the wedge sending the `i`-th sphere onto the
  generalized loop `γ i`.

## Main results

* `TauCeti.subsingleton_homotopyGroup_sphereWedge`: the wedge of `(n + 1)`-spheres is
  `n`-connected.
* `TauCeti.sphereWedgeLift_genLoopMap_sphereWedgeLoop`: a based map out of the wedge is the lift of
  the images of its spheres.
* `TauCeti.sphereWedge_homotopyGroup_hom_ext`: homomorphisms out of `πₙ₊₂(⋁ᵢ Sⁿ⁺²)` into a
  commutative group are determined on the spheres.
* `TauCeti.exists_sphereWedge_mapHom_eq`: every homomorphism `πₙ₊₂(⋁ᵢ Sⁿ⁺²) → πₙ₊₂(Z, z)` is
  induced by a based map.
* `TauCeti.exists_sphereWedge_singularHomologyMap_eq`: every homomorphism
  `Hₙ₊₂(⋁ᵢ Sⁿ⁺²; ℤ) → Hₙ₊₂(Z; ℤ)` into an `(n + 1)`-connected space is induced by a based map.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2: the homotopy group `πₙ` of a wedge of `n`-spheres, Theorem 4.32 (the Hurewicz
  theorem), and the construction of Eilenberg–MacLane spaces from a presentation; Lemma 4.31,
  whose proof begins by sending the generator spheres to representatives of the prescribed classes.
-/

public section

noncomputable section

open CategoryTheory Topology Set Topology.RelCWComplex AlgebraicTopology
open scoped Topology.Homotopy unitInterval

namespace TauCeti

variable (ι : Type) (n : ℕ)

/-- The attaching maps of the wedge of spheres: every `n`-cell is attached to the point along the
constant map. -/
abbrev sphereWedgeAttachingMap : ι → (TopCat.diskBoundary.{0} n ⟶ TopCat.of PUnit) :=
  fun _ ↦ TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

/-- The wedge `⋁ᵢ Sⁿ` of `n`-spheres indexed by `ι`: the space obtained from a point by attaching
one `n`-cell along the constant map for each `i : ι`. -/
abbrev sphereWedge : TopCat.{0} :=
  cellAttachment (sphereWedgeAttachingMap ι n)

/-- The base point of the wedge of spheres, the image of the point to which the cells are
attached. -/
def sphereWedgeBase : sphereWedge ι n :=
  cellAttachmentIncl (sphereWedgeAttachingMap ι n) PUnit.unit

/-- The base point of the wedge of spheres is the image of the point under the inclusion of the
cell attachment. -/
lemma sphereWedgeBase_def :
    sphereWedgeBase ι n = cellAttachmentIncl (sphereWedgeAttachingMap ι n) PUnit.unit :=
  (rfl)

/-- **The `i`-th sphere of a wedge of spheres**, as a generalized loop at the base point: the
characteristic map of the `i`-th cell, read on the cube through `TauCeti.diskHomeomorphCube`
(`TauCeti.sphereWedgeLoop_apply`), a case of `TauCeti.cellAttachmentCellLoop`. The boundary of the
cube goes to the boundary sphere of the disk, which is attached at the base point. -/
def sphereWedgeLoop (i : ι) : Ω^ (Fin n) (sphereWedge ι n) (sphereWedgeBase ι n) :=
  cellAttachmentCellLoop (sphereWedgeAttachingMap ι n) i rfl

variable {ι n} in
/-- The `i`-th sphere of the wedge is the characteristic map of the `i`-th cell, read on the cube
through `TauCeti.diskHomeomorphCube`. -/
@[simp]
lemma sphereWedgeLoop_apply (i : ι) (t : I^(Fin n)) :
    sphereWedgeLoop ι n i t =
      cellAttachmentCell (sphereWedgeAttachingMap ι n) i ((diskHomeomorphCube n).symm t) :=
  cellAttachmentCellLoop_apply _ i rfl t

/-- **A wedge of `(n + 1)`-spheres is `n`-connected**: its homotopy groups `π_k` vanish for
`k ≤ n`, because attaching `(n + 1)`-cells to a point is onto on `π_k` for `k ≤ n`. -/
theorem subsingleton_homotopyGroup_sphereWedge {k : ℕ} (hk : k ≤ n) :
    Subsingleton (HomotopyGroup (Fin k) (sphereWedge ι (n + 1)) (sphereWedgeBase ι (n + 1))) :=
  (surjective_homotopyGroupMap_cellAttachmentIncl (sphereWedgeAttachingMap ι (n + 1))
    (N := Fin k) (by simpa using hk) PUnit.unit).subsingleton

section Basis

/-! ### The basis of `πₙ₊₂` given by the spheres -/

/-- The homotopy groups of the wedge of `(n + 2)`-spheres below degree `n + 2` vanish, in the form
consumed by the Hurewicz theorem. -/
private lemma subsingleton_homotopyGroup_sphereWedge_of_lt :
    ∀ k < n + 2, Subsingleton
      (HomotopyGroup (Fin k) (sphereWedge ι (n + 2)) (sphereWedgeBase ι (n + 2))) :=
  fun _ hk ↦ subsingleton_homotopyGroup_sphereWedge ι (n + 1) (by omega)

/-- The wedge of `(n + 2)`-spheres, obtained by attaching `(n + 2)`-disks to the point. -/
private abbrev sphereWedgeAttachCells :
    HomotopicalAlgebra.AttachCells.{0} (TopCat.RelativeCWComplex.basicCell (n + 2))
      (cellAttachmentIncl (sphereWedgeAttachingMap ι (n + 2))) :=
  cellAttachmentAttachCells (sphereWedgeAttachingMap ι (n + 2))

/-- The wedge of `(n + 2)`-spheres as a classical relative CW complex over the point. -/
private abbrev sphereWedgeRelCWComplex :=
  (sphereWedgeAttachCells ι n).toRelativeCWComplex.toRelCWComplex

attribute [local instance] sphereWedgeRelCWComplex

/-- The `(n + 2)`-cells of the wedge of `(n + 2)`-spheres, read as a classical relative CW complex,
are indexed by `ι`. -/
private abbrev sphereWedgeCellEquiv : cell (univ : Set (sphereWedge ι (n + 2))) (n + 2) ≃ ι :=
  (sphereWedgeAttachCells ι n).cellToRelCWComplexEquiv

/-- The skeleton of dimension `n + 2` of the wedge of `(n + 2)`-spheres, read as a relative CW
complex over the point, is the whole wedge. -/
private lemma skeletonLT_sphereWedge_eq_univ :
    (skeletonLT (univ : Set (sphereWedge ι (n + 2))) (n + 2 + 1 : ℕ) :
      Set (sphereWedge ι (n + 2))) = univ :=
  (sphereWedgeAttachCells ι n).skeletonLT_toRelCWComplex_eq_univ (by omega)

/-- The skeleton of dimension `n + 1` of the wedge of `(n + 2)`-spheres, read as a relative CW
complex over the point, is the base point. -/
private lemma skeletonLT_sphereWedge_eq_singleton :
    (skeletonLT (univ : Set (sphereWedge ι (n + 2))) (n + 2 : ℕ) :
      Set (sphereWedge ι (n + 2))) =
      {sphereWedgeBase ι (n + 2)} := by
  rw [(sphereWedgeAttachCells ι n).skeletonLT_toRelCWComplex le_rfl, range_unique]
  rfl

/-- The identity of the wedge as a map of pairs from the wedge modulo its base point to the
skeletal pair in dimension `n + 2`. -/
private def sphereWedgePairToSkeletonPair :
    TopPair.ofSubset ({sphereWedgeBase ι (n + 2)} : Set (TopCat.of (sphereWedge ι (n + 2)))) ⟶
      skeletonPair (univ : Set (sphereWedge ι (n + 2))) (n + 2) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun y ↦ ⟨y, (skeletonLT_sphereWedge_eq_univ ι n).symm ▸ mem_univ y⟩,
      continuous_id.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun y ↦ ⟨y.1, (skeletonLT_sphereWedge_eq_singleton ι n).symm ▸ y.2⟩,
      continuous_subtype_val.subtype_mk _⟩)
    (by ext; rfl)

private lemma sphereWedgePairToSkeletonPair_fst_apply (y : sphereWedge ι (n + 2)) :
    (TopPair.Hom.fst (sphereWedgePairToSkeletonPair ι n) y).1 = y :=
  (rfl)

private lemma isIso_sphereWedgePairToSkeletonPair :
    IsIso (sphereWedgePairToSkeletonPair ι n) := by
  have : IsIso (TopPair.Hom.fst (sphereWedgePairToSkeletonPair ι n)) :=
    ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, by ext; rfl, by ext; rfl⟩
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun y ↦ ?_
  have hy : y.1 ∈ ({sphereWedgeBase ι (n + 2)} : Set _) :=
    skeletonLT_sphereWedge_eq_singleton ι n ▸ y.2
  exact ⟨⟨sphereWedgeBase ι (n + 2), rfl⟩, Subtype.ext (mem_singleton_iff.1 hy).symm⟩

private instance isIso_singularHomologyMap_sphereWedgePairToSkeletonPair (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (sphereWedgePairToSkeletonPair ι n)
      (ModuleCat.of ℤ ℤ) k) := by
  have := isIso_sphereWedgePairToSkeletonPair ι n
  exact (TopPair.toSSetPair ⋙ SSetPair.homologyFunctor (ModuleCat.of ℤ ℤ) k).map_isIso _

/-- The Hurewicz isomorphism `πₙ₊₂(⋁ᵢ Sⁿ⁺²) ≅ Hₙ₊₂(⋁ᵢ Sⁿ⁺²; ℤ)`, followed by the identification
of `Hₙ₊₂(⋁ᵢ Sⁿ⁺²; ℤ)` with the cellular chain group of the wedge in degree `n + 2`. -/
private def sphereWedgeCellularEquiv :
    Additive (HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) (sphereWedgeBase ι (n + 2)))
      ≃ₗ[ℤ]
      (cellularChainGroup (univ : Set (sphereWedge ι (n + 2))) (ModuleCat.of ℤ ℤ) (n + 2) :
        ModuleCat ℤ) :=
  (HomotopyGroup.hurewiczAddEquiv
      (subsingleton_homotopyGroup_sphereWedge_of_lt ι n)).toIntLinearEquiv.trans
    (singularHomologyIsoOfSubsetSingleton (ModuleCat.of ℤ ℤ) (n + 1) (sphereWedgeBase ι (n + 2)) ≪≫
      asIso (TopPair.singularHomologyMap (sphereWedgePairToSkeletonPair ι n)
        (ModuleCat.of ℤ ℤ) (n + 2))).toLinearEquiv

/-- The Hurewicz class of the `i`-th sphere is the cellular basis vector of the `i`-th cell. -/
private lemma sphereWedgeCellularEquiv_sphereWedgeLoop (i : ι) :
    sphereWedgeCellularEquiv ι n (Additive.ofMul
      (⟦sphereWedgeLoop ι (n + 2) i⟧ : HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) _)) =
      cellularChainBasis (univ : Set (sphereWedge ι (n + 2))) ℤ (n + 2)
        ((sphereWedgeCellEquiv ι n).symm i) := by
  set R := ModuleCat.of ℤ ℤ
  set j := (sphereWedgeCellEquiv ι n).symm i
  -- Both classes are images of the generator of the disk pair under maps of pairs out of the disk
  -- pair, and these maps agree: both are the characteristic map of the `i`-th cell.
  have hpair : diskBoundaryPairToCube (n + 2) ≫
      GenLoop.toCubeBoundaryPairHom (sphereWedgeLoop ι (n + 2) i) ≫
        sphereWedgePairToSkeletonPair ι n =
      characteristicCellPairMap _ j := by
    refine TopPair.hom_ext_of_fst _ ?_
    ext z
    refine Subtype.ext ?_
    simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
    refine (sphereWedgePairToSkeletonPair_fst_apply ι n _).trans ?_
    refine (GenLoop.toCubeBoundaryPairHom_fst_apply _ _).trans ?_
    rw [diskBoundaryPairToCube_fst_apply_down, sphereWedgeLoop_apply]
    refine (congrArg _ ((diskHomeomorphCube (n + 2)).symm_apply_apply z)).trans ?_
    refine Eq.trans ?_ ((coe_characteristicCellPairMap_fst_apply _ j z).trans
      (congrArg (map (n + 2) j) (coe_diskHomeomorphClosedBall_apply z)).symm).symm
    refine Eq.trans ?_ ((sphereWedgeAttachCells ι n).map_cellToRelCWComplexEquiv_symm i
      (diskHomeomorphClosedBall (n + 2) z)).symm
    rw [cellAttachmentAttachCells_cell]
    exact (congrArg _ ((diskHomeomorphClosedBall (n + 2)).symm_apply_apply z)).symm
  have hR := ConcreteCategory.congr_hom
    (ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap
      (univ : Set (sphereWedge ι (n + 2))) R (n + 2) j) (1 : ℤ)
  rw [cellularChainBasis_apply, ← ConcreteCategory.comp_apply, hR, ← hpair]
  rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp, ← Category.assoc,
    ← singularHomologyCubeBoundaryPairIso_inv, ← Category.assoc,
    ← GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom]
  simp only [sphereWedgeCellularEquiv, LinearEquiv.trans_apply, AddEquiv.coe_toIntLinearEquiv,
    HomotopyGroup.hurewiczAddEquiv_apply, HomotopyGroup.hurewiczHom_apply, Iso.toLinearEquiv_apply,
    Iso.trans_hom, ConcreteCategory.comp_apply, asIso_hom]
  -- The class is stated in `Additive (HomotopyGroup _ _ _)`, which `rw` does not see through.
  erw [toMul_ofMul, HomotopyGroup.hurewicz_mk]
  -- The two sides differ only in how the morphisms of `ModuleCat ℤ` are coerced to functions.
  rfl

/-- **The homotopy group of a wedge of spheres is free on the spheres.** For `n ≥ 0`, the classes
of the spheres `TauCeti.sphereWedgeLoop ι (n + 2) i` form a basis of the abelian group
`πₙ₊₂(⋁ᵢ Sⁿ⁺²)` (`TauCeti.sphereWedgeHomotopyGroupBasis_apply`), for an arbitrary index type
`ι`. -/
def sphereWedgeHomotopyGroupBasis :
    Module.Basis ι ℤ (Additive
      (HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) (sphereWedgeBase ι (n + 2)))) :=
  ((cellularChainBasis (univ : Set (sphereWedge ι (n + 2))) ℤ (n + 2)).reindex
    (sphereWedgeCellEquiv ι n)).map (sphereWedgeCellularEquiv ι n).symm

/-- The basis vector of `TauCeti.sphereWedgeHomotopyGroupBasis` at `i` is the class of the `i`-th
sphere. -/
@[simp]
theorem sphereWedgeHomotopyGroupBasis_apply (i : ι) :
    sphereWedgeHomotopyGroupBasis ι n i = Additive.ofMul
      (⟦sphereWedgeLoop ι (n + 2) i⟧ : HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) _) := by
  rw [sphereWedgeHomotopyGroupBasis, Module.Basis.map_apply, Module.Basis.reindex_apply]
  exact (sphereWedgeCellularEquiv ι n).symm_apply_eq.2
    (sphereWedgeCellularEquiv_sphereWedgeLoop ι n i).symm

end Basis

section Lift

/-! ### Maps out of a wedge of spheres -/

variable {ι n} {Z : TopCat.{0}} {z : Z}

/-- **The map out of a wedge of spheres with prescribed spheres.** For generalized loops
`γ i : Ω^ (Fin n) Z z`, the map `⋁ᵢ Sⁿ ⟶ Z` sending the base point to `z` and the `i`-th sphere
onto `γ i` (`TauCeti.genLoopMap_sphereWedgeLift_sphereWedgeLoop`): on the `i`-th cell it is
`γ i`, read on the disk through `TauCeti.diskHomeomorphCube`. -/
def sphereWedgeLift (γ : ι → Ω^ (Fin n) Z z) : sphereWedge ι n ⟶ Z :=
  cellAttachmentLift (sphereWedgeAttachingMap ι n) (TopCat.ofHom (ContinuousMap.const _ z))
    (fun i ↦ GenLoop.diskMap (γ i)) fun i ↦ by
      rw [GenLoop.diskBoundaryInclusion_comp_diskMap]
      -- The attaching maps of the wedge are constant, so both sides are the constant map at `z`
      -- by definition.
      rfl

/-- The map out of the wedge with prescribed spheres sends the base point to the base point of
the target. -/
@[simp]
theorem sphereWedgeLift_sphereWedgeBase (γ : ι → Ω^ (Fin n) Z z) :
    sphereWedgeLift γ (sphereWedgeBase ι n) = z := by
  rw [sphereWedgeBase_def, sphereWedgeLift, ← ConcreteCategory.comp_apply,
    cellAttachmentIncl_lift]
  simp

/-- On the `i`-th cell, the map out of the wedge with prescribed spheres is `γ i`, read on the
disk. -/
@[reassoc (attr := simp)]
theorem cellAttachmentCell_sphereWedgeLift (γ : ι → Ω^ (Fin n) Z z) (i : ι) :
    cellAttachmentCell (sphereWedgeAttachingMap ι n) i ≫ sphereWedgeLift γ =
      GenLoop.diskMap (γ i) :=
  cellAttachmentCell_lift _ _ _ _ i

/-- The map out of the wedge with prescribed spheres sends the `i`-th sphere onto `γ i`, on the
nose. -/
@[simp]
theorem genLoopMap_sphereWedgeLift_sphereWedgeLoop (γ : ι → Ω^ (Fin n) Z z) (i : ι) :
    GenLoop.map (sphereWedgeLift γ).hom (sphereWedgeLift_sphereWedgeBase γ)
      (sphereWedgeLoop ι n i) = γ i := by
  ext t
  rw [GenLoop.map_apply, sphereWedgeLoop_apply, ← ConcreteCategory.comp_apply,
    cellAttachmentCell_sphereWedgeLift, GenLoop.diskMap_apply, Homeomorph.apply_symm_apply]

/-- **Maps out of a wedge of spheres are determined by their spheres.** A map `f : ⋁ᵢ Sⁿ ⟶ Z`
sending the base point to `z` is the map out of the wedge whose prescribed spheres are the images
`f ∘ Sⁿᵢ` of the spheres of the wedge. -/
@[simp]
theorem sphereWedgeLift_genLoopMap_sphereWedgeLoop (f : sphereWedge ι n ⟶ Z)
    (hf : f (sphereWedgeBase ι n) = z) :
    sphereWedgeLift (fun i ↦ GenLoop.map f.hom hf (sphereWedgeLoop ι n i)) = f := by
  refine (cellAttachmentAttachCells (sphereWedgeAttachingMap ι n)).hom_ext ?_ fun (i : ι) ↦ ?_
  · -- The old space is a point, sent to the base point by both maps.
    ext ⟨⟩
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← sphereWedgeBase_def,
      sphereWedgeLift_sphereWedgeBase, hf]
  · rw [cellAttachmentAttachCells_cell, cellAttachmentCell_sphereWedgeLift]
    ext s
    rw [GenLoop.diskMap_apply, GenLoop.map_apply, sphereWedgeLoop_apply,
      Homeomorph.symm_apply_apply, ConcreteCategory.comp_apply]

/-- The map out of the wedge with prescribed spheres sends the class of the `i`-th sphere to the
class of `γ i`. -/
theorem homotopyGroupMap_sphereWedgeLift_mk_sphereWedgeLoop (γ : ι → Ω^ (Fin n) Z z) (i : ι) :
    HomotopyGroup.map (sphereWedgeLift γ).hom (sphereWedgeLift_sphereWedgeBase γ)
      (⟦sphereWedgeLoop ι n i⟧ : HomotopyGroup (Fin n) (sphereWedge ι n) _) = ⟦γ i⟧ := by
  rw [HomotopyGroup.map_mk, genLoopMap_sphereWedgeLift_sphereWedgeLoop]

end Lift

section Realization

/-! ### Realizing homomorphisms on `πₙ₊₂` -/

variable {ι n}

/-- **Homomorphisms out of `πₙ₊₂` of a wedge of spheres are determined by the spheres.** Two
homomorphisms from `πₙ₊₂(⋁ᵢ Sⁿ⁺²)` to a monoid that agree on the class of every sphere are equal,
since these classes generate `πₙ₊₂(⋁ᵢ Sⁿ⁺²)`. -/
theorem sphereWedge_homotopyGroup_hom_ext {G : Type*} [Monoid G]
    {φ ψ : HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) (sphereWedgeBase ι (n + 2)) →* G}
    (h : ∀ i, φ (⟦sphereWedgeLoop ι (n + 2) i⟧ : HomotopyGroup (Fin (n + 2)) _ _) =
      ψ ⟦sphereWedgeLoop ι (n + 2) i⟧) : φ = ψ := by
  refine MonoidHom.eq_of_eqOn_dense
    (G := HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) (sphereWedgeBase ι (n + 2)))
    ((Subgroup.eq_top_iff' _).2 fun a ↦ ?_) (Set.forall_mem_range.2 h)
  -- The classes of the spheres form a basis, so the subgroup they generate contains everything.
  refine Submodule.span_induction (p := fun b _ ↦ b.toMul ∈ Subgroup.closure _) ?_ (one_mem _)
    (fun _ _ _ _ ↦ mul_mem) (fun k b _ hb ↦ by rw [toMul_zsmul]; exact zpow_mem hb k)
    ((sphereWedgeHomotopyGroupBasis ι n).mem_span (Additive.ofMul a))
  rintro _ ⟨i, rfl⟩
  rw [sphereWedgeHomotopyGroupBasis_apply]
  exact Subgroup.subset_closure (Set.mem_range_self i)

variable {Z : TopCat.{0}} {z : Z}

/-- **Every homomorphism out of `πₙ₊₂` of a wedge of spheres is induced by a map**: for a
homomorphism `φ : πₙ₊₂(⋁ᵢ Sⁿ⁺²) → πₙ₊₂(Z, z)` there is a map `f : ⋁ᵢ Sⁿ⁺² ⟶ Z` sending the base
point to `z` and inducing `φ`. It is `TauCeti.sphereWedgeLift` of representatives of the images
of the spheres. -/
theorem exists_sphereWedge_mapHom_eq
    (φ : HomotopyGroup (Fin (n + 2)) (sphereWedge ι (n + 2)) (sphereWedgeBase ι (n + 2)) →*
      HomotopyGroup (Fin (n + 2)) Z z) :
    ∃ (f : sphereWedge ι (n + 2) ⟶ Z) (hf : f (sphereWedgeBase ι (n + 2)) = z),
      HomotopyGroup.mapHom f.hom hf = φ := by
  choose γ hγ using fun i ↦
    Quotient.exists_rep (φ (⟦sphereWedgeLoop ι (n + 2) i⟧ : HomotopyGroup (Fin (n + 2)) _ _))
  refine ⟨sphereWedgeLift γ, sphereWedgeLift_sphereWedgeBase γ,
    sphereWedge_homotopyGroup_hom_ext fun i ↦ ?_⟩
  exact (homotopyGroupMap_sphereWedgeLift_mk_sphereWedgeLoop γ i).trans (hγ i)

/-- **Every homomorphism on `Hₙ₊₂` out of a wedge of spheres into an `(n + 1)`-connected space is
induced by a map.** If `πₖ(Z, z)` is trivial for every `k < n + 2`, then every homomorphism
`χ : Hₙ₊₂(⋁ᵢ Sⁿ⁺²; ℤ) → Hₙ₊₂(Z; ℤ)` is the map induced on integral singular homology by a map
`f : ⋁ᵢ Sⁿ⁺² ⟶ Z` sending the base point to `z`. Both Hurewicz maps are isomorphisms and natural,
so this is `TauCeti.exists_sphereWedge_mapHom_eq` read through them. -/
theorem exists_sphereWedge_singularHomologyMap_eq
    (hZ : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Z z))
    (χ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
        (sphereWedge ι (n + 2)) →ₗ[ℤ]
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj Z) :
    ∃ f : sphereWedge ι (n + 2) ⟶ Z, f (sphereWedgeBase ι (n + 2)) = z ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).map f).hom =
        χ := by
  let hW := HomotopyGroup.hurewiczAddEquiv (subsingleton_homotopyGroup_sphereWedge_of_lt ι n)
  let hZ' := HomotopyGroup.hurewiczAddEquiv hZ
  obtain ⟨f, hf, hfφ⟩ := exists_sphereWedge_mapHom_eq (ι := ι) (n := n) (z := z)
    (AddMonoidHom.toMultiplicative
      ((hZ'.symm.toAddMonoidHom.comp χ.toAddMonoidHom).comp hW.toAddMonoidHom))
  refine ⟨f, hf, LinearMap.toAddMonoidHom_injective <|
    (AddMonoidHom.cancel_right (f := hW.toAddMonoidHom) hW.surjective).1 ?_⟩
  refine AddMonoidHom.ext fun a ↦ ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    AddEquiv.coe_toAddMonoidHom]
  have hφ : HomotopyGroup.map f.hom hf a.toMul = (hZ'.symm (χ (hW a))).toMul :=
    DFunLike.congr_fun hfφ a.toMul
  -- Naturality of the Hurewicz map turns the homology map of `f` into the map `φ` on `πₙ₊₂`.
  calc _ = (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom f.hom)).hom (HomotopyGroup.hurewiczIntHom (sphereWedge ι (n + 2))
            (sphereWedgeBase ι (n + 2)) (n + 1) (Additive.ofMul a.toMul)) := by
        rw [TopCat.ofHom_hom, ofMul_toMul, HomotopyGroup.hurewiczAddEquiv_apply_eq_hurewiczIntHom]
    _ = HomotopyGroup.hurewiczIntHom Z z (n + 1)
          (Additive.ofMul (HomotopyGroup.map f.hom hf a.toMul)) :=
        (HomotopyGroup.hurewiczIntHom_map f.hom hf a.toMul).symm
    _ = hZ' (hZ'.symm (χ (hW a))) := by
        rw [hφ, ofMul_toMul]
        exact (HomotopyGroup.hurewiczAddEquiv_apply_eq_hurewiczIntHom hZ _).symm
    _ = χ (hW a) := hZ'.apply_symm_apply _

end Realization

end TauCeti
