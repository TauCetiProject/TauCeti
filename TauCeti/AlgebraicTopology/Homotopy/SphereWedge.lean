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

## Main definitions

* `TauCeti.sphereWedge ι n`: the wedge of `n`-spheres indexed by `ι`, a cell attachment to a
  point.
* `TauCeti.sphereWedgeBase ι n`: its base point.
* `TauCeti.sphereWedgeLoop ι n i`: the `i`-th sphere, as a generalized loop at the base point.
* `TauCeti.sphereWedgeHomotopyGroupBasis ι n`: the basis of `πₙ₊₂(⋁ᵢ Sⁿ⁺²)` given by the classes
  of the spheres (`TauCeti.sphereWedgeHomotopyGroupBasis_apply`).

## Main results

* `TauCeti.subsingleton_homotopyGroup_sphereWedge`: the wedge of `(n + 1)`-spheres is
  `n`-connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2: the homotopy group `πₙ` of a wedge of `n`-spheres, Theorem 4.32 (the Hurewicz
  theorem), and the construction of Eilenberg–MacLane spaces from a presentation.
-/

public section

noncomputable section

open CategoryTheory Topology Set Topology.RelCWComplex
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

end TauCeti
