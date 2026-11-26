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
onto the closed unit ball of the sup norm, is a singular `n`-cube `χⱼ` of the `n`-skeleton sending
the boundary of the cube into the `(n - 1)`-skeleton
(`TauCeti.mapsTo_boundary_of_characteristicCube`). So `χⱼ` is a relative cycle of the normalized
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

* `TauCeti.mapsTo_boundary_of_characteristicCube`: the characteristic cube of a cell sends the
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

variable {C} in
/-- A cube of the `n`-skeleton which reads the characteristic map of an `n`-cell `j` on the cube,
through `TauCeti.cubeHomeomorphClosedBall`, sends the boundary of the cube into the
`(n - 1)`-skeleton, the subspace of the skeletal pair. -/
lemma mapsTo_boundary_of_characteristicCube {n : ℕ} {j : cell C n}
    {c : SingularCube (skeletonPair C n).fst n}
    (hc : ∀ d, (c d).val = map n j (cubeHomeomorphClosedBall (Fin n) d)) :
    MapsTo c (Cube.boundary (Fin n)) (range (skeletonPair C n).map) := by
  intro d hd
  have hmem : (c d).val ∈ (skeletonLT C (n : ℕ∞) : Set X) := by
    rw [hc]
    exact cellFrontier_subset_skeletonLT n j
      ⟨_, mem_sphere_zero_iff_norm.2 ((norm_cubeHomeomorphClosedBall_eq_one_iff d).2 hd), rfl⟩
  exact ⟨⟨(c d).val, hmem⟩, rfl⟩

variable {C} in
/-- **The characteristic cube of a cell is a relative cycle**: it represents a class of the
relative cubical homology `Hₙ(Xⁿ, Xⁿ⁻¹)` of the skeletal pair. -/
theorem exists_isCubicalRepresentative_characteristicCube {n : ℕ} {j : cell C n}
    {c : SingularCube (skeletonPair C n).fst n}
    (hc : ∀ d, (c d).val = map n j (cubeHomeomorphClosedBall (Fin n) d)) :
    ∃ μ, (skeletonPair C n).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube (skeletonPair C n).fst R c) μ :=
  TopPair.exists_isCubicalRepresentative_ofCube R c (mapsTo_boundary_of_characteristicCube hc)

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
      let ptd : TopCat.disk.{w} 0 := diskCenter 0
      have hinv : (singularHomologyDiskBoundaryPairIso (ModuleCat.of R R) 0).inv =
          singularHomology₀Section (ModuleCat.of R R) ptd ≫
            (diskBoundaryPair.{w} 0).singularHomologyπ (ModuleCat.of R R) 0 := by
        refine ((Iso.comp_hom_eq_id _).1 ?_).symm
        rw [singularHomologyDiskBoundaryPairIso_zero_hom]
        -- The relative and absolute homology of `D⁰` agree only up to unfolding.
        erw [Category.assoc, IsIso.hom_inv_id_assoc]
        exact singularHomology₀Section_singularHomology₀ε _ ptd
      rw [singularHomologyCubeBoundaryPairIso_inv, hinv]
      exact TopPair.singularHomology₀Section_singularHomologyMap _ _ (diskBoundaryPairToCube.{w} 0)
        ptd pt        (ULift.ext (funext fun i ↦ i.elim0))
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
/-- Read on the Euclidean disk pair, the map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (Xⁿ, Xⁿ⁻¹)` of a characteristic
cube of the cell `j` is the characteristic map of `j`. -/
private lemma diskBoundaryPairToCube_comp_cubeBoundaryPairHom {n : ℕ} {j : cell C n}
    {c : SingularCube (skeletonPair C n).fst n}
    (hc : ∀ d, (c d).val = map n j (cubeHomeomorphClosedBall (Fin n) d)) :
    diskBoundaryPairToCube.{w} n ≫
        cubeBoundaryPairHom c (mapsTo_boundary_of_characteristicCube hc) =
      TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j ≫
        (sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n := by
  -- The two maps agree on the ambient disk; on the boundary sphere they are its restrictions.
  have key (z : (diskBoundaryPair.{w} n).fst) :
      (TopPair.Hom.fst (diskBoundaryPairToCube.{w} n ≫
          cubeBoundaryPairHom c (mapsTo_boundary_of_characteristicCube hc)) z).val =
        (TopPair.Hom.fst (TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j ≫
          (sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n) z).val := by
    have hz (y : TopCat.disk.{w} n) :
        cubeHomeomorphClosedBall (Fin n) (diskHomeomorphCube n y) =
          diskHomeomorphClosedBall n y := by
      rw [diskHomeomorphCube_apply, Homeomorph.apply_symm_apply]
    rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, cubeBoundaryPairHom_fst_apply, hc,
      diskBoundaryPairToCube_fst_apply_down]
    -- The point `z` of the disk pair is a point of `TopCat.disk n` only up to unfolding.
    erw [hz z]
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    let q := TopPair.Hom.fst (TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j) z
    have h₁ := sigmaDiskBoundaryPairIso_hom_fst_apply_fst (cell C n) n q
    have h₂ := coe_sigmaDiskBoundaryPairIso_hom_fst_apply_snd (cell C n) n q
    refine Eq.trans ?_ (characteristicPairMap_fst_apply C n _).symm
    generalize TopPair.Hom.fst (sigmaDiskBoundaryPairIso (cell C n) n).hom q = p at h₁ h₂ ⊢
    obtain ⟨i, y⟩ := p
    obtain rfl : i = j := h₁
    have hy : y = diskHomeomorphClosedBall n z :=
      Subtype.ext (h₂.trans (coe_diskHomeomorphClosedBall_apply z).symm)
    rw [hy]
  -- On the boundary sphere each map is the restriction of its map of disks.
  have hw (f : diskBoundaryPair.{w} n ⟶ skeletonPair C n) (z : (diskBoundaryPair.{w} n).snd) :
      (TopPair.Hom.snd f z).val = (TopPair.Hom.fst f ((diskBoundaryPair.{w} n).map z)).val :=
    congrArg Subtype.val (TopPair.Hom.w_apply f z)
  ext z : 2
  · exact Subtype.ext ((hw _ z).trans ((key _).trans (hw _ z).symm))
  · exact Subtype.ext (key z)

variable {C} in
/-- **The characteristic cube of a cell is a signed cellular basis vector.** Let `c` be a singular
`n`-cube of the `n`-skeleton reading the characteristic map of the `n`-cell `j` on the cube, through
`TauCeti.cubeHomeomorphClosedBall`. Its class in the relative cubical homology of the skeletal pair
`(Xⁿ, Xⁿ⁻¹)`, read in relative singular homology, is `(-1) ^ (n choose 2)` times the cellular basis
vector of `j`. -/
theorem singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis {n : ℕ} {j : cell C n}
    {c : SingularCube (skeletonPair C n).fst n}
    (hc : ∀ d, (c d).val = map n j (cubeHomeomorphClosedBall (Fin n) d))
    {μ : ((skeletonPair C n).cubicalChainComplex R).homology n}
    (hμ : (skeletonPair C n).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube (skeletonPair C n).fst R c) μ) :
    (TopPair.singularCubicalHomologyIso R (skeletonPair C n) n).inv μ =
      (-1 : R) ^ n.choose 2 • cellularChainBasis C R n j := by
  let f := cubeBoundaryPairHom c (mapsTo_boundary_of_characteristicCube hc)
  obtain ⟨κ, hκ⟩ :=
    TopPair.exists_isCubicalRepresentative_ofCube R (P := cubeBoundaryPair.{w} n) (upCube.{w} n)
    (mapsTo_upCube_boundary.{w} n)
  -- The map of pairs of `c` carries the class of the identity cube to the class of `c`.
  have hfμ : HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap R f) n κ = μ := by
    have hcid : (TopPair.Hom.fst f).hom.comp (upCube.{w} n) = c :=
      ContinuousMap.ext fun y ↦ cubeBoundaryPairHom_fst_apply c _ _
    have h := hκ.map f
    -- The identity cube is a cube of the ambient space of the cube pair only up to unfolding.
    erw [NormalizedCubicalChain.map_ofCube] at h
    rw [hcid] at h
    exact h.unique hμ
  rw [← hfμ, ← ModuleCat.comp_apply, TopPair.singularCubicalHomologyIso_inv_naturality,
    ModuleCat.comp_apply, singularCubicalHomologyIso_inv_upCube R hκ, map_smul,
    singularHomologyCubeBoundaryPairIso_inv, ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← TopPair.singularHomologyMap_comp, diskBoundaryPairToCube_comp_cubeBoundaryPairHom hc,
    cellularChainBasis_apply, ← ModuleCat.comp_apply, ← ι_cellularChainGroupIso_inv]
  -- Both sides are the generator of the disk pair pushed along the same composite of maps.
  rfl

end TauCeti
