/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.CharacteristicCube
public import TauCeti.AlgebraicTopology.Cellular.CharacteristicMap
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Pullback
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Additivity
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.FiberHomotopy.Cube
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule
public import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# The relative homology of the based path fibration over a cube and over the cells of a CW complex

Let `f : Iᵐ⁺¹ → X` be a map from a cube of positive dimension, and `τ` a continuous family of
Moore paths, `τ d` from the basepoint `b` to `f d`. The pullback `f^*P_b X` of the based Moore path
fibration along `f` carries the left action of the Moore loops at `b`, by concatenation in front,
and the section `d ↦ (d, τ d)`, a singular `(m + 1)`-cube `c₀` of `f^*P_b X`
(`TauCeti.MoorePathPullback.sectionCube`). Over the boundary of the cube, `c₀` lies in the
pullback of the boundary, so it is a relative cycle of the pair `(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹})`.

This file shows that acting on `c₀` identifies the homology of the loop space with the relative
homology of this pair, up to the shift by the dimension of the cube:

`H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}; k)`, `[z] ↦ [z · c₀]`,

over every commutative ring `k` (`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv`,
`TauCeti.MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`). Here
`z · c₀` is the left action of chains on loops on chains on the pullback,
`TauCeti.NormalizedCubicalChain.leftAct`. Below degree `m + 1` the relative homology vanishes
(`TauCeti.MoorePathPullback.isZero_cubicalHomology_of_lt`).

The map `(ω, d) ↦ ω · (d, τ d)` from `Ω_b X × Iᵐ⁺¹` to the pullback is, up to the interchange of
the factors, the fibre homotopy trivialization `TauCeti.MoorePathPullback.fiberHomotopyEquiv` of
the pullback, so the isomorphism is the computation
`TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv` of the relative homology of a space
fibre homotopy trivial over a cube. On chains this map carries the cross product `z × [Iᵐ⁺¹]` with
the identity cube to `z · c₀`.

This is the computation of one cell in Brown's construction of a semi-free model of the chains on
the based path space of a CW complex over the chains on its loop space: a free generator attached
for the cell is sent to `c₀`, and the free module it spans, shifted by the dimension of the cell,
is quasi-isomorphic to the relative chains of the pullback over the cell.

The second part of the file assembles the cells. Let `C ⊆ B` be a relative CW complex, `P` the
pullback of `P_b B → B` along the characteristic maps of the `(m + 1)`-cells
(`TauCeti.sigmaCellMap`) and `∂P` its part over their boundary spheres
(`TauCeti.cellPathPullbackPair`). Choose a Moore path from `b` to the centre of each cell, and
follow it by the images of radial segments (`TauCeti.cellRadialPaths`). Reading the disk of each
cell `j` on the cube (`TauCeti.cellCubeMap`), the pullback over that cube is included in `P`
(`TauCeti.cellCubePathPullbackPairι`), and these inclusions exhibit `(P, ∂P)` as the disjoint union
of the pullbacks over the single cubes
(`TauCeti.isColimitCofanCellCubePathPullbackPairι`), an instance of the recognition principle
`TauCeti.isColimitCofanCellCubePairMap` for spaces over the disks of the cells. Additivity of
relative cubical homology (`TopPair.cubicalHomologyDirectSumEquiv`) and the computation over one
cube then identify a direct sum of copies of the homology of the loop
space, one for each `(m + 1)`-cell, with the relative homology of `(P, ∂P)`:

`⨁ⱼ H_q(Ω_b B; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`, `[z]ⱼ ↦ [z · cⱼ]`,

where `cⱼ` is the section cube of the cell `j` (`TauCeti.cellSectionCube`). This is the form in
which free generators, one for each `(m + 1)`-cell, are compared with the relative chains over the
`(m + 1)`-cells in Brown's construction.

## Main definitions

* `TauCeti.MoorePathPullback.sectionCube τ h₀ h₁`: the singular cube `d ↦ (d, τ d)` of the
  pullback.
* `TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q`: the isomorphism
  `H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}; k)`.
* `TauCeti.cellCubeMap C n j`: the disk of the `n`-cell `j`, read on the cube.
* `TauCeti.cellCube C n j`: the characteristic map of the `n`-cell `j`, read on the cube.
* `TauCeti.cellCubePairMap ρ ρ' j ι hρ`: the map of pairs `(Z, ∂) ⟶ (Y, ∂)` of a map from a space
  over the cube to a space over the disks of the cells, lying over the disk of `j`.
* `TauCeti.cellCubeRadialPaths γ j`: the radial paths of the cell `j`, read on its cube.

* `TauCeti.cellRadialPaths C n γ`: the radial paths to the points of the `n`-cells.
* `TauCeti.cellSectionCube C n γ j`: the section cube of the `n`-cell `j` in the pullback over the
  disks of all `n`-cells.
* `TauCeti.cellPathPullbackHomologyEquiv γ k q`: the isomorphism
  `⨁ⱼ H_q(Ω_b B; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`.

## Main results

* `TauCeti.MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`: for a
  cycle `z` of `Ω_b X`, the chain `z · c₀` represents the image of `[z]`.
* `TauCeti.subtypeVal_comp_characteristicCube`, `TauCeti.map_ofCube_characteristicCube`: read in
  `B`, the characteristic cube of a cell in the skeleton, and its chain, are `TauCeti.cellCube`.
* `TauCeti.isColimitCofanCellCubePairMap`: a space over the disks of the `n`-cells is the disjoint
  union of its parts over the single cubes.
* `TauCeti.isColimitCofanCellCubePathPullbackPairι`: the pullback over the disks of the `n`-cells
  is the disjoint union of the pullbacks over the single cells.
* `TauCeti.isCubicalRepresentative_cellPathPullbackHomologyEquiv`: for a cycle `z` of `Ω_b B`, the
  chain `z · cⱼ` represents the image of `[z]` in the summand of the cell `j`.
* `TauCeti.MoorePathPullback.isZero_cubicalHomology_of_lt`,
  `TauCeti.isZero_cubicalHomology_cellPathPullbackPair_of_lt`: below the dimension of the cube, or
  of the cells, the relative homology vanishes.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Limits
open scoped unitInterval

namespace TauCeti.MoorePathPullback

variable {X : Type} [TopologicalSpace X] {b : X} {m : ℕ} {f : C(Fin (m + 1) → I, X)}
  (τ : C(Fin (m + 1) → I, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
  (h₁ : ∀ d, (τ d).target = f d) (k : Type) [CommRing k]

/-- **The relative homology of the based path fibration over a cube**: for a continuous family
`τ` of Moore paths from `b` to the points of `f : Iᵐ⁺¹ → X`, acting on the section cube
`c₀ = TauCeti.MoorePathPullback.sectionCube τ h₀ h₁` is an isomorphism
`H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}; k)`, `[z] ↦ [z · c₀]`
(`TauCeti.MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`), over every
commutative ring `k`. This is `TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv` for the
fibre homotopy trivialization `TauCeti.MoorePathPullback.fiberHomotopyEquiv`. -/
def cubicalHomologyCubeBoundaryEquiv (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homology q ≃ₗ[k]
      ((TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
        (proj f b ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology
          (q + (m + 1)) :=
  (fiberHomotopyEquiv τ h₀ h₁).cubicalHomologyCubeBoundaryEquiv k q

include τ h₀ h₁ in
/-- **The relative homology of the based path fibration over a cube vanishes below the dimension of
the cube**: given a continuous family `τ` of Moore paths from `b` to the points of
`f : Iᵐ⁺¹ → X`, `Hⱼ(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}; k) = 0` for `j < m + 1`, over every commutative
ring `k`. -/
theorem isZero_cubicalHomology_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
      (proj f b ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology j) :=
  (fiberHomotopyEquiv τ h₀ h₁).isZero_cubicalHomology_of_lt k hj

/-- The **section cube** `d ↦ (d, τ d)` of the pullback of the based Moore path fibration along
`f`, given by the family `τ` of paths from `b` to the points `f d`. -/
def sectionCube : SingularCube (MoorePathPullback f b) (m + 1) :=
  (trivializationMap τ h₀ h₁).comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))

@[simp]
theorem point_sectionCube (d : Fin (m + 1) → I) : (sectionCube τ h₀ h₁ d).point = d := by
  simp [sectionCube]

@[simp]
theorem path_sectionCube (d : Fin (m + 1) → I) : (sectionCube τ h₀ h₁ d).path = τ d := by
  simp [sectionCube]

/-- On chains, the trivialization `(ω, d) ↦ ω · (d, τ d)` sends the cross product of a chain `a` of
`Ω_b X` with the identity cube to `a · c₀`, the left action of `a` on the section cube. -/
private theorem map_crossProduct_id {q : ℕ}
    (a : NormalizedCubicalChain (MooreLoopSpace X b) k q) :
    NormalizedCubicalChain.map k ((fiberHomotopyEquiv τ h₀ h₁).toFun.comp ContinuousMap.prodSwap)
        (q + (m + 1)) (NormalizedCubicalChain.crossProduct (MooreLoopSpace X b) (Fin (m + 1) → I)
          k q (m + 1) a (NormalizedCubicalChain.ofCube _ k (ContinuousMap.id _))) =
      NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathPullback f b) k q (m + 1) a
        (NormalizedCubicalChain.ofCube _ k (sectionCube τ h₀ h₁)) := by
  have hF : (fiberHomotopyEquiv τ h₀ h₁).toFun.comp ContinuousMap.prodSwap =
      (leftActMap (MooreLoopSpace X b) (MoorePathPullback f b)).comp
        ((ContinuousMap.id _).prodMap (sectionCube τ h₀ h₁)) := by
    ext1 z
    -- appending `τ d` to the loop `ω` is acting by `ω` on the section `(d, τ d)`
    simpa [sectionCube] using
      (congrArg (fun ω ↦ trivializationMap τ h₀ h₁ (z.2, ω)) (mul_one z.1)).symm.trans
        (trivializationMap_mul τ h₀ h₁ z.2 z.1 1)
  rw [NormalizedCubicalChain.leftAct_def, hF, NormalizedCubicalChain.map_comp, LinearMap.comp_apply,
    NormalizedCubicalChain.map_crossProduct, NormalizedCubicalChain.map_id, LinearMap.id_apply,
    NormalizedCubicalChain.map_ofCube, ContinuousMap.comp_id]

/-- **The isomorphism `H_q(Ω_b X) ≃ H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹})` acts on the section
cube**: for a `q`-cycle `z` of the Moore loops at `b`, the chain `z · c₀`, the left action of `z` on
the section cube `c₀ = TauCeti.MoorePathPullback.sectionCube τ h₀ h₁`, is a relative cycle
representing the image of the class of `z`. -/
theorem isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).cycles q) :
    (TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
        (proj f b ⁻¹' Cube.boundary (Fin (m + 1)))).IsCubicalRepresentative k
      (NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathPullback f b) k q (m + 1)
        (normalizedCubicalChainComplexXEquiv _ q
          (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).iCycles q z))
        (NormalizedCubicalChain.ofCube _ k (sectionCube τ h₀ h₁)))
      (cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q
        (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homologyπ q
          z)) := by
  rw [← map_crossProduct_id]
  exact (fiberHomotopyEquiv τ h₀ h₁).isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv k q z

end TauCeti.MoorePathPullback

/-! ### The cells of a CW complex -/

namespace TauCeti

open Metric Topology Topology.RelCWComplex Limits
open scoped _root_.DirectSum

section Cells

variable {B : Type} [TopologicalSpace B] {b : B} {C D : Set B} [RelCWComplex C D]

variable (C) in
/-- The disk of the `n`-cell `j` read on the cube: the cube is the closed unit ball of the sup norm
on `Fin n → ℝ` through `TauCeti.cubeHomeomorphClosedBall`, included as the disk of `j` in the
disjoint union of the disks of the `n`-cells. -/
def cellCubeMap (n : ℕ) (j : cell C n) :
    C(Fin n → I, Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1) :=
  ⟨fun d ↦ ⟨j, cubeHomeomorphClosedBall (Fin n) d⟩,
    continuous_sigmaMk.comp (cubeHomeomorphClosedBall (Fin n)).continuous⟩

@[simp]
theorem cellCubeMap_apply (n : ℕ) (j : cell C n) (d : Fin n → I) :
    cellCubeMap C n j d = ⟨j, cubeHomeomorphClosedBall (Fin n) d⟩ := (rfl)

/-- The disk of a cell, read on the cube, is an open embedding into the disjoint union of the
disks. -/
theorem isOpenEmbedding_cellCubeMap (n : ℕ) (j : cell C n) :
    IsOpenEmbedding (cellCubeMap C n j) :=
  IsOpenEmbedding.sigmaMk.comp (cubeHomeomorphClosedBall (Fin n)).isOpenEmbedding

section CellCubePair

variable {n : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
  (ρ : C(Y, Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1)) (ρ' : C(Z, Fin n → I))

/-- The map of pairs `(Z, ρ'⁻¹ ∂Iⁿ) ⟶ (Y, ρ⁻¹ ∂Dⁿ)` of a map `ι : Z → Y` from a space over the
cube to a space over the disks of the `n`-cells, lying over the disk of the cell `j` read on the
cube (`TauCeti.cellCubeMap`). -/
def cellCubePairMap (j : cell C n) (ι : C(Z, Y))
    (hρ : ∀ z, ρ (ι z) = cellCubeMap C n j (ρ' z)) :
    TopPair.ofSubset (X := TopCat.of Z) (ρ' ⁻¹' Cube.boundary (Fin n)) ⟶
      TopPair.ofSubset (X := TopCat.of Y) (ρ ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}) :=
  TopPair.ofSubsetMap (TopCat.ofHom ι) fun z hz ↦ by
    simpa [hρ, norm_cubeHomeomorphClosedBall_eq_one_iff] using hz

/-- On the ambient spaces, the map of pairs is `ι`. -/
theorem cellCubePairMap_fst_apply (j : cell C n) (ι : C(Z, Y))
    (hρ : ∀ z, ρ (ι z) = cellCubeMap C n j (ρ' z))
    (z : (TopPair.ofSubset (X := TopCat.of Z) (ρ' ⁻¹' Cube.boundary (Fin n))).fst) :
    TopPair.Hom.fst (cellCubePairMap ρ ρ' j ι hρ) z = ι z :=
  TopPair.ofSubsetMap_fst_apply _ _ z

/-- On the ambient spaces, the map of pairs is `ι`, as a continuous map. -/
theorem cellCubePairMap_fst_hom (j : cell C n) (ι : C(Z, Y))
    (hρ : ∀ z, ρ (ι z) = cellCubeMap C n j (ρ' z)) :
    (TopPair.Hom.fst (cellCubePairMap ρ ρ' j ι hρ)).hom = ι :=
  ContinuousMap.ext (cellCubePairMap_fst_apply ρ ρ' j ι hρ)

end CellCubePair

/-- **A space over the disks of the `n`-cells is the disjoint union of its parts over the single
cubes.** Let `ρ : Y → ⨆ⱼ Dⁿ` be a space over the disks of the `n`-cells and, for each cell `j`,
`ιⱼ : Zⱼ → Y` a map from a space `ρⱼ : Zⱼ → Iⁿ` over the cube, lying over `TauCeti.cellCubeMap`.
If each `ιⱼ` is an open embedding whose image contains the part of `Y` over the disk of `j`, the
maps of pairs `(Zⱼ, ρⱼ⁻¹ ∂Iⁿ) ⟶ (Y, ρ⁻¹ ∂Dⁿ)` they induce (`TauCeti.cellCubePairMap`) exhibit
`(Y, ρ⁻¹ ∂Dⁿ)` as the coproduct of the pairs `(Zⱼ, ρⱼ⁻¹ ∂Iⁿ)` in `TopPair`. Pullbacks to the
disks of the cells, read on the cubes through `TauCeti.cellCubeMap`, are of this form. -/
noncomputable def isColimitCofanCellCubePairMap {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (ρ : C(Y, Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1)) {Z : cell C n → Type}
    [∀ j, TopologicalSpace (Z j)] (ρ' : ∀ j, C(Z j, Fin n → I)) (ι : ∀ j, C(Z j, Y))
    (hρ : ∀ j z, ρ (ι j z) = cellCubeMap C n j (ρ' j z))
    (hι : ∀ j, IsOpenEmbedding (ι j)) (hrange : ∀ j y, (ρ y).1 = j → y ∈ Set.range (ι j)) :
    IsColimit (Cofan.mk _ fun j ↦ cellCubePairMap ρ (ρ' j) j (ι j) (hρ j)) :=
  have hσ : IsHomeomorph fun x : Σ j, Z j ↦ ι x.1 x.2 := by
    refine ⟨continuous_sigma fun j ↦ (ι j).continuous,
      isOpenMap_sigma.2 fun j ↦ (hι j).isOpenMap, fun ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ h ↦ ?_, fun y ↦ ?_⟩
    · -- The cell is read off from the point of the disk, and on a single cell the map is injective.
      have hj := congrArg (fun y ↦ (ρ y).1) h
      simp only [hρ, cellCubeMap_apply] at hj
      subst hj
      exact Sigma.ext rfl <| heq_of_eq <| (hι j₁).injective h
    · obtain ⟨x, hx⟩ := hrange _ y rfl
      exact ⟨⟨_, x⟩, hx⟩
  TopPair.isColimitCofanOfIsHomeomorph _ (show IsHomeomorph fun x : Σ j, Z j ↦
      TopPair.Hom.fst (cellCubePairMap ρ (ρ' x.1) x.1 (ι x.1) (hρ x.1)) x.2 from
    (funext fun x : Σ j, Z j ↦
      cellCubePairMap_fst_apply ρ (ρ' x.1) x.1 (ι x.1) (hρ x.1) x.2) ▸ hσ) fun y ↦ by
    -- A point over a boundary sphere comes from a point over the boundary of its cube.
    obtain ⟨⟨j, x⟩, hx⟩ := hσ.bijective.2 y.val
    have hy : ‖((ρ y.val).2 : Fin n → ℝ)‖ = 1 := y.property
    dsimp only at hx
    rw [← hx, hρ, cellCubeMap_apply, norm_cubeHomeomorphClosedBall_eq_one_iff] at hy
    exact ⟨j, ⟨x, hy⟩, (cellCubePairMap_fst_apply ρ (ρ' j) j (ι j) (hρ j) x).trans hx⟩

variable (C) in
/-- The **characteristic cube** of an `n`-cell `j`: its characteristic map, read on the cube `Iⁿ`
through `TauCeti.cubeHomeomorphClosedBall`. -/
def cellCube (n : ℕ) (j : cell C n) : SingularCube B n :=
  (sigmaCellMap C n).comp (cellCubeMap C n j)

@[simp]
theorem cellCube_apply (n : ℕ) (j : cell C n) (d : Fin n → I) :
    cellCube C n j d = map n j (cubeHomeomorphClosedBall (Fin n) d) := by
  rw [cellCube, ContinuousMap.comp_apply, cellCubeMap_apply, sigmaCellMap_apply]

variable (C) in
/-- The characteristic cube of an `n`-cell lies in the `n`-skeleton `Xⁿ = skeletonLT C (n + 1)`. -/
theorem cellCube_mem_skeletonLT_succ [T2Space B] (n : ℕ) (j : cell C n) (d : Fin n → I) :
    cellCube C n j d ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) := by
  rw [cellCube_apply]
  exact map_mem_skeletonLT_succ j
    (mem_closedBall_zero_iff.1 (cubeHomeomorphClosedBall (Fin n) d).property)

/-- The characteristic cube of a `0`-cell is the `0`-cube at the point of the cell. -/
theorem cellCube_zero (j : cell C 0) : cellCube C 0 j = SingularCube.point (map 0 j 0) := by
  rw [SingularCube.eq_point (cellCube C 0 j), cellCube_apply]
  congr 2
  exact Subsingleton.elim _ _

variable [T2Space B] in
/-- Read in `B`, the characteristic cube `TauCeti.characteristicCube` of a cell, a cube of the
skeleton, is `TauCeti.cellCube`. -/
@[simp]
theorem subtypeVal_comp_characteristicCube (n : ℕ) (j : cell C n) :
    (ContinuousMap.subtypeVal _).comp (characteristicCube C n j) = cellCube C n j :=
  ContinuousMap.ext fun d ↦ (coe_characteristicCube_apply n j d).trans (cellCube_apply n j d).symm

variable [T2Space B] in
/-- Pushed forward to `B`, the chain of the characteristic cube of a cell, a chain of the skeleton,
is the chain of `TauCeti.cellCube`. -/
theorem map_ofCube_characteristicCube (R : Type) [Ring R] (n : ℕ) (j : cell C n) :
    NormalizedCubicalChain.map R (ContinuousMap.subtypeVal _ : C((skeletonPair C n).fst, B)) n
        (NormalizedCubicalChain.ofCube _ R (characteristicCube C n j)) =
      NormalizedCubicalChain.ofCube B R (cellCube C n j) :=
  -- The skeleton is the ambient space of the skeletal pair only up to unfolding.
  (NormalizedCubicalChain.map_ofCube R _ _).trans
    (congrArg _ (subtypeVal_comp_characteristicCube n j))

variable (C) in
/-- The characteristic map of the `n`-cell `j`, on the closed unit ball of the sup norm. -/
private def cellDiskMap (n : ℕ) (j : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, B) :=
  (sigmaCellMap C n).comp
    (ContinuousMap.sigmaMk (X := fun _ : cell C n ↦ closedBall (0 : Fin n → ℝ) 1) j)

variable (C) in
/-- The radial paths in the `n`-cell `j`, after the path `γ` to its centre. -/
private def cellRadialPath (n : ℕ) (j : cell C n) (γ : MoorePathBetween B b (map n j 0)) :
    C(closedBall (0 : Fin n → ℝ) 1, MoorePath B) :=
  MoorePathPullback.radialPaths
    ((convex_closedBall (0 : Fin n → ℝ) 1).starConvex (mem_closedBall_self zero_le_one))
    (mem_closedBall_self zero_le_one) (cellDiskMap C n j)
    (γ.cast rfl (by simp [cellDiskMap]))

variable (C) in
/-- **Radial paths to the points of the `n`-cells.** Given a Moore path `γ j` from `b` to the
centre of each `n`-cell `j`, the path to the image of a point `v` of the disk of `j` follows `γ j`
and then the image of the radial segment from `0` to `v`
(`TauCeti.MoorePathPullback.radialPaths`). -/
def cellRadialPaths (n : ℕ) (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0)) :
    C(Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1, MoorePath B) :=
  ⟨fun q ↦ cellRadialPath C n q.1 (γ q.1) q.2,
    continuous_sigma fun j ↦ (cellRadialPath C n j (γ j)).continuous⟩

@[simp]
theorem source_cellRadialPaths {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (q : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1) : (cellRadialPaths C n γ q).source = b := by
  simp [cellRadialPaths, cellRadialPath]

@[simp]
theorem target_cellRadialPaths {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (q : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1) :
    (cellRadialPaths C n γ q).target = sigmaCellMap C n q := by
  simp [cellRadialPaths, cellRadialPath, cellDiskMap]

@[simp]
theorem length_cellRadialPaths {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (q : Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1) :
    (cellRadialPaths C n γ q).length = (γ q.1).toMoorePath.length + 1 := by
  simp [cellRadialPaths, cellRadialPath]

/-- After the path `γ j` to the centre of the cell `j`, the radial path to the image of `v`
follows the image `t ↦ χⱼ(t • v)` of the radial segment in one unit of Moore time. -/
theorem cellRadialPaths_apply_length_add {n : ℕ}
    (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0)) (j : cell C n)
    (v : closedBall (0 : Fin n → ℝ) 1) (t : I) :
    cellRadialPaths C n γ ⟨j, v⟩ ((γ j).toMoorePath.length + unitInterval.toNNReal t) =
      sigmaCellMap C n ⟨j, ⟨(t : ℝ) • (v : Fin n → ℝ),
        ((convex_closedBall (0 : Fin n → ℝ) 1).starConvex
          (mem_closedBall_self zero_le_one)).smul_mem v.property t.property.1 t.property.2⟩⟩ := by
  have h := MoorePathPullback.radialPaths_apply_length_add
    ((convex_closedBall (0 : Fin n → ℝ) 1).starConvex (mem_closedBall_self zero_le_one))
    (mem_closedBall_self zero_le_one) (cellDiskMap C n j)
    ((γ j).cast rfl (by simp [cellDiskMap])) v t
  simp only [MoorePathBetween.toMoorePath_cast] at h
  exact h.trans (by simp [cellDiskMap, AffineMap.lineMap_apply_module])

variable (b C) in
/-- The pullback `P` of the based Moore path fibration `P_b B → B` to the disks of the `n`-cells,
relative to its part `∂P` over their boundary spheres. -/
abbrev cellPathPullbackPair (n : ℕ) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (MoorePathPullback (sigmaCellMap C n) b))
    (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1})

variable (b C) in
/-- The pullback `Pⱼ` of the based Moore path fibration to the disk of the `n`-cell `j`, read on
the cube through `TauCeti.cellCubeMap`, relative to its part `∂Pⱼ` over the boundary of the cube. -/
abbrev cellCubePathPullbackPair (n : ℕ) (j : cell C n) : TopPair.{0} :=
  TopPair.ofSubset
    (X := TopCat.of (MoorePathPullback ((sigmaCellMap C n).comp (cellCubeMap C n j)) b))
    (MoorePathPullback.proj ((sigmaCellMap C n).comp (cellCubeMap C n j)) b ⁻¹'
      Cube.boundary (Fin n))

variable (b C) in
/-- The inclusion `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` of the pullback over the disk of the `n`-cell `j` into the
pullback over the disks of all `n`-cells. -/
def cellCubePathPullbackPairι (n : ℕ) (j : cell C n) :
    cellCubePathPullbackPair b C n j ⟶ cellPathPullbackPair b C n :=
  cellCubePairMap _ _ j (MoorePathPullback.paramMap (cellCubeMap C n j)) fun _ ↦ by simp

@[simp]
theorem cellCubePathPullbackPairι_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellCubePathPullbackPair b C n j).fst) :
    TopPair.Hom.fst (cellCubePathPullbackPairι b C n j) x =
      MoorePathPullback.paramMap (cellCubeMap C n j) x :=
  cellCubePairMap_fst_apply _ _ _ _ _ x

/-- The inclusion of the pullback over the cube of `j` is the map induced by `TauCeti.cellCubeMap`
on parameters. -/
theorem cellCubePathPullbackPairι_fst_hom (n : ℕ) (j : cell C n) :
    (TopPair.Hom.fst (cellCubePathPullbackPairι b C n j)).hom =
      MoorePathPullback.paramMap (cellCubeMap C n j) :=
  ContinuousMap.ext (cellCubePathPullbackPairι_fst_apply n j)

variable (b C) in
/-- **The pullback over the disks of the `n`-cells is the disjoint union of the pullbacks over the
single disks.** The inclusions `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` exhibit `(P, ∂P)` as the coproduct of the
pairs `(Pⱼ, ∂Pⱼ)` in `TopPair`. -/
def isColimitCofanCellCubePathPullbackPairι (n : ℕ) :
    IsColimit (Cofan.mk (cellPathPullbackPair b C n) (cellCubePathPullbackPairι b C n)) :=
  isColimitCofanCellCubePairMap _ _ (fun j ↦ MoorePathPullback.paramMap (cellCubeMap C n j))
    (fun _ _ ↦ by simp)
    (fun j ↦ MoorePathPullback.isOpenEmbedding_paramMap _ (isOpenEmbedding_cellCubeMap n j))
    fun j y hj ↦ by
      -- A path over a point of the disk of `j` comes from the pullback over the cube of `j`.
      rw [MoorePathPullback.proj_apply] at hj
      subst hj
      rw [MoorePathPullback.range_paramMap]
      exact ⟨(cubeHomeomorphClosedBall (Fin n)).symm y.point.2, by simp⟩

variable (C) in
/-- The **section cube** of the `n`-cell `j`: the cube `d ↦ (χ d, τ (χ d))` of the pullback of the
based Moore path fibration to the disks of the `n`-cells, where `χ = TauCeti.cellCubeMap C n j`
reads the disk of `j` on the cube and `τ = TauCeti.cellRadialPaths C n γ` is the family of radial
paths. -/
def cellSectionCube (n : ℕ) (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (j : cell C n) : SingularCube (MoorePathPullback (sigmaCellMap C n) b) n :=
  (MoorePathPullback.trivializationMap (cellRadialPaths C n γ) (source_cellRadialPaths γ)
    (target_cellRadialPaths γ)).comp ((cellCubeMap C n j).prodMk (ContinuousMap.const _ 1))

@[simp]
theorem point_cellSectionCube {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (j : cell C n) (d : Fin n → I) :
    (cellSectionCube C n γ j d).point = cellCubeMap C n j d := by
  simp [cellSectionCube]

@[simp]
theorem path_cellSectionCube {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (j : cell C n) (d : Fin n → I) :
    (cellSectionCube C n γ j d).path = cellRadialPaths C n γ (cellCubeMap C n j d) := by
  simp [cellSectionCube]

section Homology

variable {m : ℕ} (γ : ∀ j : cell C (m + 1), MoorePathBetween B b (map (m + 1) j 0))
  (k : Type) [CommRing k]

/-- The radial paths of `TauCeti.cellRadialPaths`, read on the cube of the cell `j` through
`TauCeti.cellCubeMap`: a continuous family of Moore paths from `b` to the points of the
characteristic map of `j` on the cube. -/
abbrev cellCubeRadialPaths (j : cell C (m + 1)) : C(Fin (m + 1) → I, MoorePath B) :=
  (cellRadialPaths C (m + 1) γ).comp (cellCubeMap C (m + 1) j)

theorem source_cellCubeRadialPaths (j : cell C (m + 1)) (d : Fin (m + 1) → I) :
    (cellCubeRadialPaths γ j d).source = b := by
  simp

theorem target_cellCubeRadialPaths (j : cell C (m + 1)) (d : Fin (m + 1) → I) :
    (cellCubeRadialPaths γ j d).target =
      ((sigmaCellMap C (m + 1)).comp (cellCubeMap C (m + 1) j)) d := by
  simp

/-- The identification of the homology of the loop space with the relative homology of the
pullback over the cube of the cell `j`, by
`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv` for the radial paths. -/
private def cellCubeHomologyEquiv (j : cell C (m + 1)) (q : ℕ) :=
  MoorePathPullback.cubicalHomologyCubeBoundaryEquiv (cellCubeRadialPaths γ j)
    (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j) k q

include γ in
/-- **The relative homology of the based path fibration over the cells vanishes below their
dimension**: for the pullback `P` of `P_b B → B` to the disks of the `(m + 1)`-cells and its part
`∂P` over the boundary spheres, `Hⱼ(P, ∂P; k) = 0` for `j < m + 1`, over every commutative ring
`k`. It is the sum of the relative homology modules over the single cells. -/
theorem isZero_cubicalHomology_cellPathPullbackPair_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((cellPathPullbackPair b C (m + 1)).cubicalChainComplex k).homology j) :=
  TopPair.isZero_cubicalHomology_of_isColimit k
    (isColimitCofanCellCubePathPullbackPairι b C (m + 1)) fun i ↦
      MoorePathPullback.isZero_cubicalHomology_of_lt (cellCubeRadialPaths γ i)
        (source_cellCubeRadialPaths γ i) (target_cellCubeRadialPaths γ i) k hj

/-- The inclusion of the pullback over the cube of `j` carries its section cube to the section
cube of `j`. -/
private theorem paramMap_comp_sectionCube (j : cell C (m + 1)) :
    (MoorePathPullback.paramMap (cellCubeMap C (m + 1) j)).comp
        (MoorePathPullback.sectionCube (cellCubeRadialPaths γ j) (source_cellCubeRadialPaths γ j)
          (target_cellCubeRadialPaths γ j)) =
      cellSectionCube C (m + 1) γ j :=
  ContinuousMap.ext fun d ↦ MoorePathPullback.ext (by simp) (by simp)

variable [DecidableEq (cell C (m + 1))]

/-- **The relative homology of the based path fibration over the cells of a CW complex.** Let `P`
be the pullback of the based Moore path fibration `P_b B → B` to the disks of the `(m + 1)`-cells
and `∂P` its part over the boundary spheres. Given a Moore path from `b` to the centre of each
`(m + 1)`-cell, acting on the section cubes `TauCeti.cellSectionCube` of the cells identifies a
direct sum of copies of the homology of the loop space, one for each `(m + 1)`-cell, with the
relative homology of `(P, ∂P)`, up to the shift by `m + 1`:

`⨁ⱼ H_q(Ω_b B; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`, `[z]ⱼ ↦ [z · cⱼ]`

(`TauCeti.isCubicalRepresentative_cellPathPullbackHomologyEquiv`), over every commutative ring
`k`. -/
def cellPathPullbackHomologyEquiv (q : ℕ) :
    (⨁ _ : cell C (m + 1),
        ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).homology q) ≃ₗ[k]
      ((cellPathPullbackPair b C (m + 1)).cubicalChainComplex k).homology (q + (m + 1)) :=
  TopPair.cubicalHomologyDirectSumEquiv k (isColimitCofanCellCubePathPullbackPairι b C (m + 1))
    (q + (m + 1)) fun j ↦ cellCubeHomologyEquiv γ k j q

/-- **`TauCeti.cellPathPullbackHomologyEquiv` acts on the section cubes**: for a `q`-cycle `z` of
the Moore loops at `b` and an `(m + 1)`-cell `j`, the chain `z · cⱼ`, the left action of `z` on the
section cube `cⱼ = TauCeti.cellSectionCube C (m + 1) γ j`, is a relative cycle of `(P, ∂P)`
representing the image of the class of `z` in the summand of `j`. -/
theorem isCubicalRepresentative_cellPathPullbackHomologyEquiv (q : ℕ) (j : cell C (m + 1))
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).cycles q) :
    (cellPathPullbackPair b C (m + 1)).IsCubicalRepresentative k
      (NormalizedCubicalChain.leftAct (MooreLoopSpace B b)
        (MoorePathPullback (sigmaCellMap C (m + 1)) b) k q (m + 1)
        (normalizedCubicalChainComplexXEquiv _ q
          (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).iCycles q z))
        (NormalizedCubicalChain.ofCube _ k (cellSectionCube C (m + 1) γ j)))
      (cellPathPullbackHomologyEquiv γ k q (DirectSum.lof k _ _ j
        (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).homologyπ q
          z))) := by
  rw [cellPathPullbackHomologyEquiv, TopPair.cubicalHomologyDirectSumEquiv_lof]
  have h := (MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv
    (cellCubeRadialPaths γ j) (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j)
      k q z).map (cellCubePathPullbackPairι b C (m + 1) j)
  rw [cellCubePathPullbackPairι_fst_hom] at h
  have hc := NormalizedCubicalChain.map_leftAct (R := k)
    (MoorePathPullback.paramMap (b := b) (cellCubeMap C (m + 1) j))
    (fun ω x ↦ by simp)
    (normalizedCubicalChainComplexXEquiv _ q
      (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).iCycles q z))
    (NormalizedCubicalChain.ofCube _ k (MoorePathPullback.sectionCube (cellCubeRadialPaths γ j)
      (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j)))
  rw [NormalizedCubicalChain.map_ofCube, paramMap_comp_sectionCube] at hc
  rw [← hc]
  exact h

end Homology

end Cells

end TauCeti
