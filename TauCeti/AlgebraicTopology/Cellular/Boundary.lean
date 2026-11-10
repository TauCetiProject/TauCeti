/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Coproduct
public import TauCeti.Topology.CWComplex.Classical.Skeleton.CellMap

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

As a first consequence, if the boundary sphere of every `(n + 1)`-cell lies in the
`(n - 1)`-skeleton, its class comes from `Hₙ(Xⁿ⁻¹)` and so vanishes in `Hₙ(Xⁿ, Xⁿ⁻¹)`: the
cellular differential leaving degree `n + 1` is zero
(`TauCeti.cellularDifferential_eq_zero_of_cellFrontier_subset`). In particular, all cellular
differentials vanish when every cell is attached along the base
(`TauCeti.cellularChainComplex_d_eq_zero_of_cellFrontier_subset`).
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

/-- The ambient component of the single-cell pair map is the characteristic map
`TauCeti.cellDiskHom` of the cell. -/
lemma characteristicCellPairMap_fst {n : ℕ} (j : cell C n) :
    TopPair.Hom.fst (characteristicCellPairMap C j) = cellDiskHom j := by
  ext x
  exact Subtype.ext <| (coe_characteristicCellPairMap_fst_apply C j x).trans <|
    (congrArg (map n j) (coe_diskHomeomorphClosedBall_apply x).symm).trans
      (coe_cellDiskHom_apply j x).symm

/-- The subspace component of the single-cell pair map is the attaching map
`TauCeti.cellAttachingMap` of the cell. -/
lemma characteristicCellPairMap_snd {n : ℕ} (j : cell C n) :
    TopPair.Hom.snd (characteristicCellPairMap C j) = cellAttachingMap j := by
  ext x
  exact Subtype.ext <| (congrArg Subtype.val (ConcreteCategory.congr_hom
    (TopPair.Hom.w (characteristicCellPairMap C j)) x)).trans <|
    (congrArg Subtype.val (ConcreteCategory.congr_hom (characteristicCellPairMap_fst C j)
      (TopCat.diskBoundaryInclusion n x))).trans <|
    (coe_cellDiskHom_apply j _).trans (coe_cellAttachingMap_apply j x).symm

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The inverse of `TauCeti.cellularChainGroupIso` on the summand of the cell `j` is the inverse of
`Hₙ(Dⁿ, Sⁿ⁻¹) ≅ R` followed by the map induced by the characteristic map of `j`. -/
@[reassoc]
lemma ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C n)) A] (j : cell C n) :
    Sigma.ι (fun _ : cell C n ↦ R) j ≫ (cellularChainGroupIso C R n).inv =
      (singularHomologyDiskBoundaryPairIso R n).inv ≫
        TopPair.singularHomologyMap (characteristicCellPairMap C j) R n :=
  ι_cellularChainGroupIso_inv C R n j

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
          SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap j)) R n ≫
            skeletonPairπ C R n := by
  rw [ι_cellularChainGroupIso_inv_assoc,
    cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ, ← characteristicCellPairMap_snd]
  -- The connecting morphism is natural for the single-cell characteristic pair map.
  have h := TopPair.singularHomologyδ_naturality R (characteristicCellPairMap C j) (n + 1) n
  -- The sphere is the disk boundary, and skeletal homology is singular homology presented
  -- through `TopCat.toSSet`; `erw` matches those object presentations beneath the functors.
  erw [← Category.assoc (TopPair.singularHomologyMap _ R (n + 1)), ← h,
    Category.assoc, singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyδ_assoc,
    Category.assoc]
  rfl

/-- **The cellular differential vanishes on cells attached two skeleta down.** If the boundary
sphere of every `(n + 1)`-cell lies in the `(n - 1)`-skeleton `skeletonLT C n`, then the cellular
differential `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` vanishes. -/
theorem cellularDifferential_eq_zero_of_cellFrontier_subset (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C (n + 1))) A]
    (h : ∀ j : cell C (n + 1), cellFrontier (n + 1) j ⊆ skeletonLT C n) :
    cellularDifferential C R n = 0 := by
  rw [← cancel_epi (cellularChainGroupIso C R (n + 1)).inv, comp_zero]
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  -- The attaching map of `j` factors through the inclusion of the `(n - 1)`-skeleton into the
  -- `n`-skeleton, and the homology of that inclusion dies in the relative homology of the pair.
  let g : TopCat.diskBoundary.{w} (n + 1) ⟶ (skeletonPair C n).snd :=
    TopCat.ofHom ⟨fun z ↦ ⟨cellAttachingMap j z, h j <| by
        rw [← range_cellAttachingMap]
        exact Set.mem_range_self z⟩,
      (continuous_subtype_val.comp (cellAttachingMap j).hom.continuous).subtype_mk _⟩
  have hzero : SSet.homologyMap (TopCat.toSSet.map (g ≫ (skeletonPair C n).map)) R n ≫
      (skeletonPair C n).singularHomologyπ R n = 0 := by
    rw [Functor.map_comp, SSet.homologyMap_comp]
    exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      ((skeletonPair C n).homologyMap_comp_singularHomologyπ R n)).trans comp_zero
  rw [ι_cellularChainGroupIso_inv_comp_cellularDifferential, comp_zero]
  -- `g ≫ (skeletonPair C n).map` is the attaching map of `j` by definition, but the boundary
  -- formula presents its spaces through `skeletonObj` and `TopCat.sphere`, so the vanishing is
  -- transported along `congrArg` rather than by rewriting.
  exact (congrArg (fun t ↦ (reducedSingularHomologyTopCatSphereIso R n).inv ≫
    (reducedSingularHomologyι R n).app (TopCat.diskBoundary.{w} (n + 1)) ≫ t) hzero).trans
      ((congrArg (_ ≫ ·) comp_zero).trans comp_zero)

/-- **The cellular differentials of a complex attached along its base vanish.** If the boundary
sphere of every cell lies in the base `D`, then every differential of the cellular chain complex
is zero. -/
theorem cellularChainComplex_d_eq_zero_of_cellFrontier_subset
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
    (h : ∀ m (j : cell C m), cellFrontier m j ⊆ D) (i j : ℕ) :
    (cellularChainComplex C R).d i j = 0 := by
  by_cases hij : i = j + 1
  · subst hij
    rw [cellularChainComplex_d, cellularDifferential_eq_zero_of_cellFrontier_subset C R j
      fun c ↦ (h _ c).trans ((skeletonLT_zero_eq_base (C := C)).symm.subset.trans
        (skeletonLT_mono zero_le)), zero_comp, comp_zero]
  · exact (cellularChainComplex C R).shape i j fun h' ↦ hij h'.symm


end TauCeti
