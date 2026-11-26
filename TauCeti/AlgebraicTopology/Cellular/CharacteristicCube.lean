/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.AlgebraicTopology.Singular.ReducedRelative
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator

/-!
# Characteristic cubes and the cellular basis

Let `C` be a relative CW complex with skeleta `Xⁿ`. The characteristic map of an `n`-cell `j`,
read on the cube `Iⁿ` through the homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube
onto the closed unit ball of the sup norm, is a singular `n`-cube `χⱼ` of the `n`-skeleton
(`TauCeti.characteristicCube`) sending the boundary of the cube into the `(n - 1)`-skeleton
(`TauCeti.mapsTo_characteristicCube_boundary`). So `χⱼ` is a relative cycle of the normalized
cubical chains of the skeletal pair `(Xⁿ, Xⁿ⁻¹)`, and it has a class in relative cubical homology
(`TauCeti.exists_isCubicalRepresentative_characteristicCube`).

Read in relative singular homology, this class is the cellular basis vector of `j`
(`TauCeti.cellularChainBasis`) up to a sign depending only on `n`
(`TauCeti.singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis`):

`[χⱼ] = (-1) ^ (n choose 2) • eⱼ`.

The cellular basis vector `eⱼ` is the image under the characteristic map of the generator of
`Hₙ(Dⁿ, Sⁿ⁻¹)`, and `χⱼ` is the image of the identity cube, so the comparison reduces to the cube
pair `(Iⁿ, ∂Iⁿ)`, where the identity cube is `(-1) ^ (n choose 2)` times the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` transported from the disk
(`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle` in positive dimension;
in dimension `0` both are the class of the point).

So the characteristic cubes of the cells form a basis of the cellular chain groups, and a cellular
chain can be computed on normalized cubical chains, for instance from chains on a path space
pushed to the base.

## Main results

* `TauCeti.characteristicCube`: the characteristic cube of an `n`-cell, a singular `n`-cube of the
  `n`-skeleton.
* `TauCeti.mapsTo_characteristicCube_boundary`: the characteristic cube of a cell sends the
  boundary of the cube into the `(n - 1)`-skeleton.
* `TauCeti.exists_isCubicalRepresentative_characteristicCube`: it represents a class of the
  relative cubical homology of the skeletal pair.
* `TauCeti.singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis`: that class is
  `(-1) ^ (n choose 2)` times the cellular basis vector of the cell.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the cellular chain complex.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex
open scoped unitInterval

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (R : Type w) [Ring R]

/-- The **characteristic cube** of an `n`-cell `j`: its characteristic map, read on the cube `Iⁿ`
through `TauCeti.cubeHomeomorphClosedBall`, as a singular `n`-cube of the `n`-skeleton. -/
def characteristicCube (n : ℕ) (j : cell C n) : SingularCube (skeletonPair C n).fst n :=
  ⟨fun d ↦ ⟨map n j (cubeHomeomorphClosedBall (Fin n) d),
      map_mem_skeletonLT_succ j
        (mem_closedBall_zero_iff.1 (cubeHomeomorphClosedBall (Fin n) d).property)⟩,
    ((RelCWComplex.continuousOn n j).comp_continuous
      (continuous_subtypeVal.comp (cubeHomeomorphClosedBall (Fin n)).continuous)
      fun d ↦ (cubeHomeomorphClosedBall (Fin n) d).property).subtype_mk _⟩

variable {C} in
/-- Read in `X`, the characteristic cube is the characteristic map of the cell on the cube. -/
lemma coe_characteristicCube_apply (n : ℕ) (j : cell C n) (d : Fin n → I) :
    (characteristicCube C n j d).val = map n j (cubeHomeomorphClosedBall (Fin n) d) :=
  (rfl)

variable {C} in
/-- The characteristic cube of an `n`-cell sends the boundary of the cube into the
`(n - 1)`-skeleton, the subspace of the skeletal pair. -/
lemma mapsTo_characteristicCube_boundary (n : ℕ) (j : cell C n) :
    MapsTo (characteristicCube C n j) (Cube.boundary (Fin n)) (range (skeletonPair C n).map) :=
  fun d hd ↦ ⟨⟨_, map_mem_skeletonLT_of_norm_eq_one j
    ((norm_cubeHomeomorphClosedBall_eq_one_iff d).2 hd)⟩, rfl⟩

variable {C} in
/-- **The characteristic cube of a cell is a relative cycle**: it represents a class of the
relative cubical homology `Hₙ(Xⁿ, Xⁿ⁻¹)` of the skeletal pair. -/
theorem exists_isCubicalRepresentative_characteristicCube (n : ℕ) (j : cell C n) :
    ∃ μ, (skeletonPair C n).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube (skeletonPair C n).fst R (characteristicCube C n j)) μ :=
  TopPair.exists_isCubicalRepresentative_ofCube R _ (mapsTo_characteristicCube_boundary n j)

/-- **The identity cube is a signed generator**: read in relative singular homology, the class of
the identity cube of `(Iⁿ, ∂Iⁿ)` is `(-1) ^ (n choose 2)` times the generator
`TauCeti.singularHomologyCubeBoundaryPairIso`. -/
private lemma singularCubicalHomologyIso_inv_upCube {n : ℕ}
    {κ : ((cubeBoundaryPair.{w} n).cubicalChainComplex R).homology n}
    (hκ : (cubeBoundaryPair.{w} n).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube _ R (upCube.{w} n)) κ) :
    (TopPair.singularCubicalHomologyIso R (cubeBoundaryPair.{w} n) n).inv κ =
      (-1 : R) ^ n.choose 2 • (singularHomologyCubeBoundaryPairIso (ModuleCat.of R R) n).inv 1 := by
  cases n with
  | zero =>
    let P := cubeBoundaryPair.{w} 0
    let pt : P.fst := ULift.up fun i ↦ i.elim0
    -- `κ` is the relative class of the absolute class of the point.
    have hκ' : HomologicalComplex.homologyMap
        (cokernel.π ((normalizedCubicalChainComplex R).map P.map)) 0
          (((normalizedCubicalChainComplex R).obj P.fst).homologyπ 0
            (cubicalCycleOfPoint R pt)) = κ := by
      refine P.homologyMap_homologyπ_eq_of_isCubicalRepresentative R _ hκ ?_
      rw [iCycles_cubicalCycleOfPoint, LinearEquiv.apply_symm_apply]
      have hpt : SingularCube.point pt = upCube.{w} 0 :=
        ContinuousMap.ext fun _ ↦ ULift.ext (funext fun i ↦ i.elim0)
      rw [hpt, sub_self]
      exact zero_mem _
    -- The generator of `H₀(I⁰, ∂I⁰)` is the class of the point.
    have hg : (singularHomologyCubeBoundaryPairIso (ModuleCat.of R R) 0).inv =
        singularHomology₀Section (ModuleCat.of R R) pt ≫
          P.singularHomologyπ (ModuleCat.of R R) 0 := by
      rw [singularHomologyCubeBoundaryPairIso_inv, singularHomologyDiskBoundaryPairIso_zero_inv]
      exact TopPair.singularHomology₀Section_singularHomologyMap _ _ (diskBoundaryPairToCube.{w} 0)
        (diskCenter 0) pt (ULift.ext (funext fun i ↦ i.elim0))
    have hM := ConcreteCategory.congr_hom
      (TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv R P 0)
      ((singularCubicalHomologyIso R P.fst 0).hom
        ((singularHomology₀Section (ModuleCat.of R R) pt).hom 1))
    rw [Nat.choose_zero_succ, pow_zero, one_smul, hg, ← hκ',
      ← singularCubicalHomologyIso_hom_singularHomology₀Section]
    refine (ConcreteCategory.comp_apply _ _ _).symm.trans (hM.trans ?_)
    -- The singular homology of the point appears in its simplicial and in its chain complex
    -- presentation, which agree only up to unfolding.
    erw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]
    rfl
  | succ m =>
    have hκ' : κ = ((cubeBoundaryPair.{w} (m + 1)).cubicalChainComplex R).homologyπ (m + 1)
        (cubeBoundaryPairCycle R m) :=
      hκ.unique ((TopPair.isCubicalRepresentative_iff _ _).2 ⟨_, by
        have h := TopPair.cubicalChainOfCube_def R (P := cubeBoundaryPair.{w} (m + 1))
          (upCube.{w} (m + 1))
        rw [normalizedCubicalChainComplexXEquiv_symm_apply] at h
        rw [iCycles_cubeBoundaryPairCycle, h], rfl⟩)
    rw [hκ', singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle,
      Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (m + 1) m]

variable {C} in
/-- Read on the Euclidean disk pair, the map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (Xⁿ, Xⁿ⁻¹)` of the
characteristic cube of the cell `j` is the characteristic map of `j`. -/
private lemma diskBoundaryPairToCube_comp_cubeBoundaryPairHom (n : ℕ) (j : cell C n) :
    diskBoundaryPairToCube.{w} n ≫
        cubeBoundaryPairHom (characteristicCube C n j) (mapsTo_characteristicCube_boundary n j) =
      characteristicCellPairMap C j := by
  have hz (y : TopCat.disk.{w} n) :
      cubeHomeomorphClosedBall (Fin n) (diskHomeomorphCube n y) = diskHomeomorphClosedBall n y := by
    rw [diskHomeomorphCube_apply, Homeomorph.apply_symm_apply]
  refine TopPair.hom_ext_of_fst _ ?_
  rw [characteristicCellPairMap_fst]
  ext z
  refine Subtype.ext ?_
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, cubeBoundaryPairHom_fst_apply,
    coe_characteristicCube_apply, diskBoundaryPairToCube_fst_apply_down]
  -- The point `z` of the disk pair is a point of `TopCat.disk n` only up to unfolding.
  exact (congrArg (fun y ↦ map n j y.val) (hz z)).trans (coe_cellDiskHom_apply j z).symm

variable {C} in
/-- **The characteristic cube of a cell is a signed cellular basis vector.** The class of the
characteristic cube of the `n`-cell `j` in the relative cubical homology of the skeletal pair
`(Xⁿ, Xⁿ⁻¹)`, read in relative singular homology, is `(-1) ^ (n choose 2)` times the cellular basis
vector of `j`. -/
theorem singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis {n : ℕ}
    {j : cell C n} {μ : ((skeletonPair C n).cubicalChainComplex R).homology n}
    (hμ : (skeletonPair C n).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube (skeletonPair C n).fst R (characteristicCube C n j)) μ) :
    (TopPair.singularCubicalHomologyIso R (skeletonPair C n) n).inv μ =
      (-1 : R) ^ n.choose 2 • cellularChainBasis C R n j := by
  let f := cubeBoundaryPairHom (characteristicCube C n j) (mapsTo_characteristicCube_boundary n j)
  obtain ⟨κ, hκ⟩ :=
    TopPair.exists_isCubicalRepresentative_ofCube R (P := cubeBoundaryPair.{w} n) (upCube.{w} n)
    (mapsTo_upCube_boundary.{w} n)
  -- The map of pairs of the characteristic cube carries the class of the identity cube to the
  -- class of the characteristic cube.
  have hfμ : HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap R f) n κ = μ := by
    have hcid : (TopPair.Hom.fst f).hom.comp (upCube.{w} n) = characteristicCube C n j :=
      ContinuousMap.ext fun y ↦ cubeBoundaryPairHom_fst_apply _ _ _
    have h := hκ.map f
    -- The identity cube is a cube of the ambient space of the cube pair only up to unfolding.
    erw [NormalizedCubicalChain.map_ofCube] at h
    rw [hcid] at h
    exact h.unique hμ
  -- Both sides are the generator of the disk pair pushed along the characteristic map of `j`.
  rw [← hfμ, ← ModuleCat.comp_apply, TopPair.singularCubicalHomologyIso_inv_naturality,
    ModuleCat.comp_apply, singularCubicalHomologyIso_inv_upCube R hκ, map_smul,
    singularHomologyCubeBoundaryPairIso_inv, ← ModuleCat.comp_apply, Category.assoc,
    ← TopPair.singularHomologyMap_comp, diskBoundaryPairToCube_comp_cubeBoundaryPairHom,
    ← ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
    ModuleCat.comp_apply, cellularChainBasis_apply]

end TauCeti
