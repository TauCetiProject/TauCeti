/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.CharacteristicMap
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Pullback
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Additivity
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Kunneth
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
`TauCeti.NormalizedCubicalChain.leftAct`.

The map `(ω, d) ↦ ω · (d, τ d)` from `Ω_b X × Iᵐ⁺¹` to the pullback is, up to the interchange of
the factors, the fibre homotopy trivialization `TauCeti.MoorePathPullback.fiberHomotopyEquiv` of
the pullback, so it induces isomorphisms of relative homology over `∂Iᵐ⁺¹`. On chains it carries
the relative cross product `z × [Iᵐ⁺¹]` with the fundamental cycle of the cube to `z · c₀`, and the
relative Künneth theorem for the cube pair
(`TauCeti.cubicalHomologyCubeBoundaryPairProdLeftEquiv`) identifies the classes `z × [Iᵐ⁺¹]` with
the homology of `Ω_b X`.

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
(`TauCeti.isColimitCofanCellCubePathPullbackPairι`). Additivity of relative cubical homology and
the computation over one cube then identify a direct sum of copies of the homology of the loop
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

* `TauCeti.cellRadialPaths C n γ`: the radial paths to the points of the `n`-cells.
* `TauCeti.cellSectionCube C n γ j`: the section cube of the `n`-cell `j` in the pullback over the
  disks of all `n`-cells.
* `TauCeti.cellPathPullbackHomologyEquiv γ k q`: the isomorphism
  `⨁ⱼ H_q(Ω_b B; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`.

## Main results

* `TauCeti.MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`: for a
  cycle `z` of `Ω_b X`, the chain `z · c₀` represents the image of `[z]`.
* `TauCeti.isColimitCofanCellCubePathPullbackPairι`: the pullback over the disks of the `n`-cells
  is the disjoint union of the pullbacks over the single cells.
* `TauCeti.isCubicalRepresentative_cellPathPullbackHomologyEquiv`: for a cycle `z` of `Ω_b B`, the
  chain `z · cⱼ` represents the image of `[z]` in the summand of the cell `j`.

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

/-- The fibre homotopy trivialization `TauCeti.MoorePathPullback.fiberHomotopyEquiv`, with the
loop factor first: `(ω, d) ↦ ω · (d, τ d)`. -/
private def loopFiberHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.snd : C(MooreLoopSpace X b × (Fin (m + 1) → I), _))
      (proj f b) :=
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.prodComm _ _) rfl).trans
    (fiberHomotopyEquiv τ h₀ h₁)

private theorem loopFiberHomotopyEquiv_toFun_apply
    (z : MooreLoopSpace X b × (Fin (m + 1) → I)) :
    (loopFiberHomotopyEquiv τ h₀ h₁).toFun z = z.1 • trivializationMap τ h₀ h₁ (z.2, 1) := by
  rw [← trivializationMap_mul, mul_one]
  simp [loopFiberHomotopyEquiv, Prod.swap]

/-- The map of pairs `Ω_b X × (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹})`,
`(ω, d) ↦ ω · (d, τ d)`. -/
private def smulSectionPairMap :
    (cubeBoundaryPair.{0} (m + 1)).prodLeft (TopCat.of (MooreLoopSpace X b)) ⟶
      TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
        (proj f b ⁻¹' Cube.boundary (Fin (m + 1))) :=
  (cubeBoundaryPairProdLeftIso (TopCat.of (MooreLoopSpace X b)) (m + 1)).hom ≫
    (loopFiberHomotopyEquiv τ h₀ h₁).preimagePairMap (Cube.boundary (Fin (m + 1)))

private theorem smulSectionPairMap_fst_apply
    (z : MooreLoopSpace X b × ULift (Fin (m + 1) → I)) :
    TopPair.Hom.fst (smulSectionPairMap τ h₀ h₁) z =
      z.1 • trivializationMap τ h₀ h₁ (z.2.down, 1) := by
  simp only [smulSectionPairMap, TopPair.Hom.fst_comp, FiberHomotopyEquiv.preimagePairMap_fst]
  -- the isomorphism of pairs lowers the cube coordinate, then the trivialization acts
  exact (congrArg (loopFiberHomotopyEquiv τ h₀ h₁).toFun
    (cubeBoundaryPairProdLeftIso_hom_fst_apply (TopCat.of (MooreLoopSpace X b)) (m + 1) z)).trans
      (loopFiberHomotopyEquiv_toFun_apply τ h₀ h₁ (z.1, z.2.down))

/-- The map of pairs `(ω, d) ↦ ω · (d, τ d)` induces isomorphisms of relative homology: it is an
isomorphism of pairs followed by the map of pairs of a fibre homotopy equivalence. -/
private theorem isIso_homologyMap_smulSectionPairMap (n : ℕ) :
    IsIso (homologyMap (TopPair.cubicalChainComplexMap k (smulSectionPairMap τ h₀ h₁)) n) := by
  rw [smulSectionPairMap, TopPair.cubicalChainComplexMap_comp, homologyMap_comp]
  have : IsIso (homologyMap (TopPair.cubicalChainComplexMap k
      ((loopFiberHomotopyEquiv τ h₀ h₁).preimagePairMap (Cube.boundary (Fin (m + 1))))) n) := by
    rw [← FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_hom]
    infer_instance
  infer_instance

/-- **The relative homology of the based path fibration over a cube**: for a continuous family
`τ` of Moore paths from `b` to the points of `f : Iᵐ⁺¹ → X`, acting on the section cube
`c₀ = TauCeti.MoorePathPullback.sectionCube τ h₀ h₁` is an isomorphism
`H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}; k)`, `[z] ↦ [z · c₀]`
(`TauCeti.MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`), over every
commutative ring `k`. -/
def cubicalHomologyCubeBoundaryEquiv (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homology q ≃ₗ[k]
      ((TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
        (proj f b ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology
          (q + (m + 1)) :=
  have := isIso_homologyMap_smulSectionPairMap τ h₀ h₁ k (q + (m + 1))
  cubicalHomologyCubeBoundaryPairProdLeftEquiv k (TopCat.of (MooreLoopSpace X b)) m q ≪≫ₗ
    (asIso (homologyMap (TopPair.cubicalChainComplexMap k (smulSectionPairMap τ h₀ h₁))
      (q + (m + 1)))).toLinearEquiv

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

/-- On chains, the map of pairs `(ω, d) ↦ ω · (d, τ d)` sends the cross product of a chain `a` of
`Ω_b X` with the identity cube to `a · c₀`, the left action of `a` on the section cube. -/
private theorem map_crossProduct_upCube {q : ℕ}
    (a : NormalizedCubicalChain (MooreLoopSpace X b) k q) :
    NormalizedCubicalChain.map k (TopPair.Hom.fst (smulSectionPairMap τ h₀ h₁)).hom (q + (m + 1))
        (NormalizedCubicalChain.crossProduct (MooreLoopSpace X b) (ULift.{0} (Fin (m + 1) → I)) k
          q (m + 1) a (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) =
      NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathPullback f b) k q (m + 1) a
        (NormalizedCubicalChain.ofCube _ k (sectionCube τ h₀ h₁)) := by
  set g : C(ULift.{0} (Fin (m + 1) → I), MoorePathPullback f b) :=
    (sectionCube τ h₀ h₁).comp ⟨ULift.down, continuous_uliftDown⟩
  have hF : ((TopPair.Hom.fst (smulSectionPairMap τ h₀ h₁)).hom :
        C(MooreLoopSpace X b × ULift.{0} (Fin (m + 1) → I), MoorePathPullback f b)) =
      (leftActMap (MooreLoopSpace X b) (MoorePathPullback f b)).comp
        ((ContinuousMap.id _).prodMap g) := by
    ext1 z
    -- the right side is `leftActMap` applied to `(z.1, g z.2) = (z.1, (z.2.down, τ z.2.down))`
    exact (smulSectionPairMap_fst_apply τ h₀ h₁ z).trans
      (leftActMap_apply _ _ ((ContinuousMap.id _).prodMap g z)).symm
  have hc : NormalizedCubicalChain.ofCube _ k (sectionCube τ h₀ h₁) =
      NormalizedCubicalChain.map k g (m + 1)
        (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1))) := by
    rw [NormalizedCubicalChain.map_ofCube]
    -- `g` precomposed with `ULift.up` is `sectionCube τ h₀ h₁`, by the eta rule for `ULift`
    exact congrArg _ (ContinuousMap.ext fun _ ↦ rfl)
  have hx : NormalizedCubicalChain.crossProduct _ _ k q (m + 1) a
      (NormalizedCubicalChain.map k g (m + 1)
        (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) =
      NormalizedCubicalChain.map k ((ContinuousMap.id _).prodMap g) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct _ _ k q (m + 1) a
          (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) := by
    rw [NormalizedCubicalChain.map_crossProduct, NormalizedCubicalChain.map_id, LinearMap.id_apply]
  rw [hc, NormalizedCubicalChain.leftAct_def, hx, ← LinearMap.comp_apply
    (NormalizedCubicalChain.map k (leftActMap _ _) _), ← NormalizedCubicalChain.map_comp]
  exact congrArg (fun φ ↦ NormalizedCubicalChain.map k φ (q + (m + 1)) _) hF

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
  -- The representing relative cycle is the image of `z × [Iᵐ⁺¹]` under the map of pairs.
  refine (TopPair.isCubicalRepresentative_iff _ _).2
    ⟨(cyclesMap (TopPair.cubicalChainComplexMap k (smulSectionPairMap τ h₀ h₁)) _).hom
    ((cyclesMap (cubicalCrossProductRel k _ (cubeBoundaryPair.{0} (m + 1))) (q + (m + 1))).hom
      ((cyclesCross ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b)))
        ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex k) q (m + 1) (q + (m + 1)) rfl).hom
          (z ⊗ₜ cubeBoundaryPairCycle k m))), ?_, ?_⟩
  · -- `z × [Iᵐ⁺¹]` is the class of the cross product of `z` with the identity cube
    rw [moduleCat_iCycles_cyclesMap_apply, iCycles_cyclesMap_cubicalCrossProductRel_cyclesCross
      k _ _ rfl z _ _ ((iCycles_cubeBoundaryPairCycle k m).trans
        (TopPair.cubicalChainOfCube_def k _)), normalizedCubicalChainComplexXEquiv_symm_apply]
    -- and the map of pairs acts on relative chains through the map of ambient spaces; the
    -- identity cube here is typed at the cube model rather than at the ambient space of the cube
    -- pair, so `rw` cannot abstract it and the steps are chained up to definitional unfolding
    refine (congrArg _ ?_).trans (TopPair.π_cubicalChainComplexMap_f_apply k _ _ _).symm
    exact (map_crossProduct_upCube τ h₀ h₁ k _).symm.trans
      (congrArg _ (NormalizedCubicalChain.cast_rfl k _).symm)
  · rw [cubicalHomologyCubeBoundaryEquiv, LinearEquiv.trans_apply,
      cubicalHomologyCubeBoundaryPairProdLeftEquiv_homologyπ, Iso.toLinearEquiv_apply, asIso_hom,
      ← ModuleCat.comp_apply, ← homologyπ_naturality, ModuleCat.comp_apply]

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
    ⟨γ.toMoorePath, γ.source, γ.target.trans (by simp [cellDiskMap])⟩

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
    ⟨(γ j).toMoorePath, (γ j).source, (γ j).target.trans (by simp [cellDiskMap])⟩ v t
  simp only [MoorePathBetween.toMoorePath_mk] at h
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
  TopPair.ofSubsetMap (TopCat.ofHom (MoorePathPullback.paramMap (cellCubeMap C n j)))
    (by intro x hx; simpa [norm_cubeHomeomorphClosedBall_eq_one_iff] using hx)

@[simp]
theorem cellCubePathPullbackPairι_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellCubePathPullbackPair b C n j).fst) :
    TopPair.Hom.fst (cellCubePathPullbackPairι b C n j) x =
      MoorePathPullback.paramMap (cellCubeMap C n j) x :=
  TopPair.ofSubsetMap_fst_apply _ _ x

/-- The inclusion of the pullback over the cube of `j` is the map induced by `TauCeti.cellCubeMap`
on parameters. -/
theorem cellCubePathPullbackPairι_fst_hom (n : ℕ) (j : cell C n) :
    (TopPair.Hom.fst (cellCubePathPullbackPairι b C n j)).hom =
      MoorePathPullback.paramMap (cellCubeMap C n j) :=
  ContinuousMap.ext (cellCubePathPullbackPairι_fst_apply n j)

/-- The disjoint union of the pullbacks over the disks of the `n`-cells maps homeomorphically onto
the pullback over all of them. -/
private theorem isHomeomorph_sigma_paramMap_cellCubeMap (n : ℕ) :
    IsHomeomorph fun x : Σ j : cell C n,
        MoorePathPullback ((sigmaCellMap C n).comp (cellCubeMap C n j)) b ↦
      MoorePathPullback.paramMap (cellCubeMap C n x.1) x.2 := by
  refine ⟨continuous_sigma fun j ↦ (MoorePathPullback.paramMap _).continuous,
    isOpenMap_sigma.2 fun j ↦ (MoorePathPullback.isOpenEmbedding_paramMap _
      (isOpenEmbedding_cellCubeMap n j)).isOpenMap, ?_⟩
  refine ⟨fun ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ h ↦ ?_, fun y ↦ ?_⟩
  · -- The cell is read off from the point of the disk, and on a single cell the map is injective.
    obtain rfl : j₁ = j₂ := by simpa using congrArg (fun y ↦ y.point.1) h
    exact Sigma.ext rfl <| heq_of_eq <| (MoorePathPullback.isOpenEmbedding_paramMap _
      (isOpenEmbedding_cellCubeMap n j₁)).injective h
  · -- A path over a point of the disk of `j` comes from the pullback over the cube of `j`.
    obtain ⟨x, hx⟩ :
        y ∈ Set.range (MoorePathPullback.paramMap (b := b) (cellCubeMap C n y.point.1)) := by
      rw [MoorePathPullback.range_paramMap]
      exact ⟨(cubeHomeomorphClosedBall (Fin n)).symm y.point.2, by simp⟩
    exact ⟨⟨_, x⟩, hx⟩

variable (b C) in
/-- **The pullback over the disks of the `n`-cells is the disjoint union of the pullbacks over the
single disks.** The inclusions `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` exhibit `(P, ∂P)` as the coproduct of the
pairs `(Pⱼ, ∂Pⱼ)` in `TopPair`. -/
def isColimitCofanCellCubePathPullbackPairι (n : ℕ) :
    IsColimit (Cofan.mk (cellPathPullbackPair b C n) (cellCubePathPullbackPairι b C n)) :=
  TopPair.isColimitCofanOfIsHomeomorph _ (by
    simp only [cellCubePathPullbackPairι_fst_apply]
    exact isHomeomorph_sigma_paramMap_cellCubeMap n) fun y ↦ by
    -- A point over a boundary sphere comes from the pullback over its cube, over the boundary.
    obtain ⟨x, hx⟩ :=
      (isHomeomorph_sigma_paramMap_cellCubeMap (b := b) (C := C) n).bijective.2 y.val
    have hy : ‖((MoorePathPullback.proj (sigmaCellMap C n) b y.val).2 : Fin n → ℝ)‖ = 1 :=
      y.property
    rw [← hx, MoorePathPullback.proj_apply, MoorePathPullback.point_paramMap, cellCubeMap_apply,
      norm_cubeHomeomorphClosedBall_eq_one_iff] at hy
    exact ⟨x.1, ⟨x.2, by rwa [Set.mem_preimage, MoorePathPullback.proj_apply]⟩,
      (cellCubePathPullbackPairι_fst_apply n x.1 x.2).trans hx⟩

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

/-- The radial paths of `TauCeti.cellRadialPaths`, read on the cube of the cell `j`. -/
private abbrev cellCubeRadialPaths (j : cell C (m + 1)) : C(Fin (m + 1) → I, MoorePath B) :=
  (cellRadialPaths C (m + 1) γ).comp (cellCubeMap C (m + 1) j)

private theorem source_cellCubeRadialPaths (j : cell C (m + 1)) (d : Fin (m + 1) → I) :
    (cellCubeRadialPaths γ j d).source = b := by
  simp

private theorem target_cellCubeRadialPaths (j : cell C (m + 1)) (d : Fin (m + 1) → I) :
    (cellCubeRadialPaths γ j d).target =
      ((sigmaCellMap C (m + 1)).comp (cellCubeMap C (m + 1) j)) d := by
  simp

/-- The identification of the homology of the loop space with the relative homology of the
pullback over the cube of the cell `j`, by
`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv` for the radial paths. -/
private def cellCubeHomologyEquiv (j : cell C (m + 1)) (q : ℕ) :=
  MoorePathPullback.cubicalHomologyCubeBoundaryEquiv (cellCubeRadialPaths γ j)
    (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j) k q

/-- The map `H_q(Ω_b B) → H_{q+m+1}(P, ∂P)` of the cell `j`: the identification over the cube of
`j`, followed by the inclusion of the pullback over the cube of `j`. -/
private def cellHomologyLeg (q : ℕ) (j : cell C (m + 1)) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).homology q ⟶
      ((cellPathPullbackPair b C (m + 1)).cubicalChainComplex k).homology (q + (m + 1)) :=
  (cellCubeHomologyEquiv γ k j q).toModuleIso.hom ≫ HomologicalComplex.homologyMap
    (TopPair.cubicalChainComplexMap k (cellCubePathPullbackPairι b C (m + 1) j)) (q + (m + 1))

/-- The maps of the cells exhibit the relative homology of the pullback over the disks of all
`(m + 1)`-cells as a coproduct of copies of the homology of the loop space. -/
private def isColimitCofanCellHomologyLeg (q : ℕ) :
    IsColimit (Cofan.mk (((cellPathPullbackPair b C (m + 1)).cubicalChainComplex k).homology
      (q + (m + 1))) (cellHomologyLeg γ k q)) :=
  have : IsIso (Sigma.desc fun j ↦ HomologicalComplex.homologyMap
      (TopPair.cubicalChainComplexMap k (cellCubePathPullbackPairι b C (m + 1) j))
        (q + (m + 1))) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).1
      ⟨TopPair.isColimitCofanCubicalHomologyOfIsColimit k
        (isColimitCofanCellCubePathPullbackPairι b C (m + 1)) (q + (m + 1))⟩
  have : IsIso (Sigma.desc (cellHomologyLeg γ k q)) := by
    -- Each leg is the leg of additivity precomposed with an isomorphism.
    rw [show Sigma.desc (cellHomologyLeg γ k q) =
        (Sigma.mapIso fun j ↦ (cellCubeHomologyEquiv γ k j q).toModuleIso).hom ≫
          Sigma.desc fun j ↦ HomologicalComplex.homologyMap
            (TopPair.cubicalChainComplexMap k (cellCubePathPullbackPairι b C (m + 1) j))
              (q + (m + 1)) from
      Sigma.hom_ext _ _ fun j ↦ by simp [cellHomologyLeg]]
    infer_instance
  Cofan.isColimitOfIsIsoSigmaDesc (hc := this) _

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
  ((ModuleCat.coproductCoconeIsColimit _).coconePointUniqueUpToIso
    (isColimitCofanCellHomologyLeg γ k q)).toLinearEquiv

/-- On the summand of the cell `j`, `TauCeti.cellPathPullbackHomologyEquiv` is the map of `j`. -/
private theorem cellPathPullbackHomologyEquiv_lof (q : ℕ) (j : cell C (m + 1))
    (x : ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace B b))).homology q) :
    cellPathPullbackHomologyEquiv γ k q (DirectSum.lof k _ _ j x) =
      cellHomologyLeg γ k q j x :=
  ConcreteCategory.congr_hom
    ((ModuleCat.coproductCoconeIsColimit _).comp_coconePointUniqueUpToIso_hom
      (isColimitCofanCellHomologyLeg γ k q) ⟨j⟩) x

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
  rw [cellPathPullbackHomologyEquiv_lof, cellHomologyLeg, ModuleCat.comp_apply]
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
  -- `h` names the class through the linear equivalence, the goal through its `ModuleCat` iso.
  exact h

end Homology

end Cells

end TauCeti
