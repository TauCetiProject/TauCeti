/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Incidence
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
(`TauCeti.singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_of_isCubicalRepresentative_upCube`).

So the characteristic cubes of the cells form a basis of the cellular chain groups, and a cellular
chain can be computed on normalized cubical chains, for instance from chains on a path space
pushed to the base.

Read in relative singular homology, the cellular differential is the cubical connecting morphism
of `(Xⁿ⁺¹, Xⁿ)` followed by the map to the relative cubical homology of `(Xⁿ, Xⁿ⁻¹)`
(`TauCeti.cellularDifferential_singularCubicalHomologyIso_inv`).

## Main results

* `TauCeti.characteristicCube`: the characteristic cube of an `n`-cell, a singular `n`-cube of the
  `n`-skeleton.
* `TauCeti.mapsTo_characteristicCube_boundary`: the characteristic cube of a cell sends the
  boundary of the cube into the `(n - 1)`-skeleton.
* `TauCeti.exists_isCubicalRepresentative_characteristicCube`: it represents a class of the
  relative cubical homology of the skeletal pair.
* `TauCeti.singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis`: that class is
  `(-1) ^ (n choose 2)` times the cellular basis vector of the cell.
* `TauCeti.cellularDifferential_singularCubicalHomologyIso_inv`: the cellular differential is the
  cubical connecting morphism.

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
  -- By naturality, the class of the characteristic cube is the image along `f` of the class of
  -- the identity cube, a signed generator of the cube pair.
  have h₁ : (TopPair.singularCubicalHomologyIso R (skeletonPair C n) n).inv μ =
      (-1 : R) ^ n.choose 2 • TopPair.singularHomologyMap f (ModuleCat.of R R) n
        ((singularHomologyCubeBoundaryPairIso (ModuleCat.of R R) n).inv 1) := by
    rw [← hfμ, ← ModuleCat.comp_apply, TopPair.singularCubicalHomologyIso_inv_naturality,
      ModuleCat.comp_apply,
      singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_of_isCubicalRepresentative_upCube R hκ,
      map_smul]
  -- Pushed along `f`, the generator of the cube pair is the generator of the disk pair pushed
  -- along the characteristic map of `j`, which is the cellular basis vector of `j`.
  have h₂ : TopPair.singularHomologyMap f (ModuleCat.of R R) n
      ((singularHomologyCubeBoundaryPairIso (ModuleCat.of R R) n).inv 1) =
        cellularChainBasis C R n j := by
    rw [singularHomologyCubeBoundaryPairIso_inv, ← ModuleCat.comp_apply, Category.assoc,
      ← TopPair.singularHomologyMap_comp, diskBoundaryPairToCube_comp_cubeBoundaryPairHom,
      ← ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
      ModuleCat.comp_apply, cellularChainBasis_apply]
  rw [h₁, h₂]

variable {C} in
/-- **The cellular differential is the cubical connecting morphism.** Read in relative singular
homology through `TopPair.singularCubicalHomologyIso`, the cellular differential of the class of a
relative cubical cycle of `(Xⁿ⁺¹, Xⁿ)` is the image of its cubical connecting class in the relative
cubical homology of `(Xⁿ, Xⁿ⁻¹)`. -/
lemma cellularDifferential_singularCubicalHomologyIso_inv (n : ℕ)
    (μ : ((skeletonPair C (n + 1)).cubicalChainComplex R).homology (n + 1)) :
    cellularDifferential C (ModuleCat.of R R) n
        ((TopPair.singularCubicalHomologyIso R (skeletonPair C (n + 1)) (n + 1)).inv μ) =
      (TopPair.singularCubicalHomologyIso R (skeletonPair C n) n).inv
        (HomologicalComplex.homologyMap
          (cokernel.π ((normalizedCubicalChainComplex R).map (skeletonPair C n).map)) n
          ((skeletonPair C (n + 1)).cubicalHomologyδ R (n + 1) n rfl μ)) := by
  have h₁ := ConcreteCategory.congr_hom
    (TopPair.singularCubicalHomologyIso_inv_singularHomologyδ R (skeletonPair C (n + 1)) (n + 1) n)
    μ
  have h₂ := ConcreteCategory.congr_hom
    (TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv R (skeletonPair C n) n)
    ((skeletonPair C (n + 1)).cubicalHomologyδ R (n + 1) n rfl μ)
  rw [cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ]
  exact (congrArg (skeletonPairπ C (ModuleCat.of R R) n).hom h₁).trans h₂.symm

end TauCeti
