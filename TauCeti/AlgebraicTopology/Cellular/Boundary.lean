/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Coproduct

/-!
# The cellular boundary on a cell generator

The boundary of an `(n + 1)`-cell is the image of the fundamental class of its boundary sphere
under the attaching map, followed by the quotient to `Hₙ(Xⁿ, Xⁿ⁻¹)`.  The theorem
`TauCeti.ι_cellularChainGroupIso_inv_comp_cellularDifferential` expresses this formula using the
coproduct identification of cellular chains.  Thus computing the differential reduces to
computing the maps induced by the attaching spheres, rather than choosing singular chains
representing each cell.

The attaching maps here are restrictions of the characteristic maps, read on Euclidean disks
through the same radial rescaling as the cellular generators.  The sphere class uses reduced
homology: for a one-cell its boundary is the difference of the two endpoints, not their sum.
Coefficients are objects in an abelian category with coproducts; only the coproduct indexed by
the source cells needs to be exact.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2, the cellular boundary
formula.  This file proves its factorization through the attaching map; no identification of
individual matrix entries with integer degrees is asserted here.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

/-- The characteristic map of one cell, as a map from the Euclidean disk pair to the pair of
consecutive skeleta.  The disk coordinates are rescaled to the sup-norm coordinates of the
classical CW structure. -/
def characteristicCellPairMap {n : ℕ} (j : cell C n) :
    diskBoundaryPair.{w} n ⟶ skeletonPair C n :=
  TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j ≫
    (sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n

/-- The ambient component of the single-cell pair map is the characteristic map in rescaled
Euclidean coordinates. -/
@[simp]
lemma coe_characteristicCellPairMap_fst_apply {n : ℕ} (j : cell C n)
    (x : TopCat.disk.{w} n) :
    (ConcreteCategory.hom (X := TopCat.disk.{w} n)
      (Y := TopCat.of (skeletonLT C ((n + 1 : ℕ) : ℕ∞)))
      (TopPair.Hom.fst (characteristicCellPairMap C j)) x).1 =
      map n j ((EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph x.down) := by
  -- Pair components use the skeletal subspace object, while the evaluation lemmas use its
  -- explicit `TopCat.of` presentation; `erw` identifies these before evaluating composites.
  unfold characteristicCellPairMap
  erw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, characteristicPairMap_fst_apply,
    sigmaDiskBoundaryPairIso_hom_fst_apply_fst,
    coe_sigmaDiskBoundaryPairIso_hom_fst_apply_snd]
  rfl

/-- The attaching map of a cell into the preceding skeleton, obtained by restricting its
Euclidean characteristic map to the boundary sphere. -/
def cellAttachingMap {n : ℕ} (j : cell C n) :
    TopCat.diskBoundary.{w} n ⟶ skeletonObj C n :=
  TopPair.Hom.snd (characteristicCellPairMap C j)

/-- The attaching map followed by skeletal inclusion is the characteristic map restricted to
the disk boundary. -/
@[reassoc]
lemma cellAttachingMap_comp_inclusion {n : ℕ} (j : cell C n) :
    cellAttachingMap C j ≫ (skeletonPair C n).map =
      TopCat.diskBoundaryInclusion n ≫ TopPair.Hom.fst (characteristicCellPairMap C j) :=
  TopPair.Hom.w (characteristicCellPairMap C j)

/-- The attaching map is the boundary restriction of the characteristic map in rescaled
Euclidean coordinates. -/
@[simp]
lemma coe_cellAttachingMap_apply {n : ℕ} (j : cell C n)
    (x : TopCat.diskBoundary.{w} n) :
    (ConcreteCategory.hom (Y := TopCat.of (skeletonLT C n)) (cellAttachingMap C j) x).1 =
      map n j ((EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph x.down) := by
  have h := ConcreteCategory.congr_hom (cellAttachingMap_comp_inclusion C j) x
  have hval := congrArg Subtype.val h
  exact hval.trans (coe_characteristicCellPairMap_fst_apply C j
    (TopCat.diskBoundaryInclusion n x))

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The cellular boundary on a cell generator**: take the reduced fundamental class of the
boundary sphere, include it in ordinary homology, apply the attaching map, and pass to the
relative homology of consecutive skeleta.  This includes one-cells, whose reduced boundary
class gives the signed difference of their endpoints. -/
@[reassoc]
lemma ι_cellularChainGroupIso_inv_comp_cellularDifferential (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C (n + 1))) A] (j : cell C (n + 1)) :
    Sigma.ι (fun _ : cell C (n + 1) ↦ R) j ≫
        (cellularChainGroupIso C R (n + 1)).inv ≫ cellularDifferential C R n =
      (reducedSingularHomologyTopCatSphereIso R n).inv ≫
        (reducedSingularHomologyι R n).app (TopCat.diskBoundary.{w} (n + 1)) ≫
          SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap C j)) R n ≫
            skeletonPairπ C R n := by
  rw [ι_cellularChainGroupIso_inv_assoc,
    cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ]
  -- The connecting morphism is natural for the single-cell characteristic pair map.
  have h := TopPair.singularHomologyδ_naturality R (characteristicCellPairMap C j) (n + 1) n
  -- The sphere is the disk boundary, and skeletal homology is singular homology presented
  -- through `TopCat.toSSet`; `erw` matches those object presentations beneath the functors.
  erw [← Category.assoc (TopPair.singularHomologyMap _ R (n + 1)), ← h,
    Category.assoc, singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyδ_assoc,
    Category.assoc]
  rfl

end TauCeti
