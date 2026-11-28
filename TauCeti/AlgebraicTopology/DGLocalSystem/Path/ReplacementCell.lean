/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Cell
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cubical.Skeleton
public import TauCeti.Topology.PathSpace.Moore.CornerPaths
public import TauCeti.Topology.PathSpace.Moore.Replacement.Pullback

/-!
# The relative homology of the Moore-path replacement over a cube and over the cells of a CW complex

Let `p : E → B` be a continuous map, `E'` the total space of its Moore-path replacement, the pairs
`(e, γ)` of a point `e ∈ E` and a Moore path `γ` starting at `p e`, and `F'_b` its fibre over `b`,
the pairs with `γ` ending at `b`. Let `f : Iᵐ⁺¹ → B` be a map from a cube of positive dimension and
`τ` a continuous family of Moore paths, `τ d` from `b` to `f d`. Appending `τ d` to the points of
`F'_b` (`TauCeti.MooreReplacementPullback.appendSection`)

`F'_b × Iᵐ⁺¹ → f^*E'`,  `((e, γ), d) ↦ (d, (e, γ ⋆ τ d))`

identifies the homology of the fibre with the relative homology of the pullback `f^*E'` over the
boundary of the cube, up to the shift by the dimension of the cube:

`H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(f^*E', f^*E'|_{∂Iᵐ⁺¹}; k)`,  `[z] ↦ [append_*(z × [Iᵐ⁺¹])]`,

over every commutative ring `k`. The append map is, up to the interchange of the factors, the fibre
homotopy trivialization `TauCeti.MooreReplacementPullback.fiberHomotopyEquiv` of the pullback
(`TauCeti.MooreReplacementPullback.fiberHomotopyEquiv_toFun_comp_prodSwap`), so this is the
computation `TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv` for a space fibre
homotopy trivial over a cube, with its representatives
`TauCeti.FiberHomotopyEquiv.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`. Below
degree `m + 1` the relative homology vanishes for every map `f`, whether or not a family `τ` is
given (`TauCeti.MooreReplacementPullback.isZero_cubicalHomology_of_lt`): the images of the
straight segments from a corner of the cube (`TauCeti.MoorePath.cornerPaths`) trivialize the
pullback. Read in `E'`, the representing chain `append_*(z × [Iᵐ⁺¹])` is the image
of `z × [τ]` under the append map `F'_b × P_b B → E'`
(`TauCeti.MooreReplacementPullback.pullbackSnd_comp_appendSection`), the form in which a
chain of `F'_b` and a chain of paths from `b` are paired in the comparison between the twisted
complex of a Brown model, with coefficients in the chains of `F'_b`, and the chains of `E'`.

The second part of the file assembles the cells. Let `C ⊆ B` be a relative CW complex, `P` the
pullback of `E' → B` along the characteristic maps of the `(m + 1)`-cells (`TauCeti.sigmaCellMap`)
and `∂P` its part over their boundary spheres (`TauCeti.cellReplacementPullbackPair`). Choose a
Moore path from `b` to the centre of each cell, and follow it by the images of radial segments
(`TauCeti.cellRadialPaths`). The pullbacks over the cubes of the single cells exhibit `(P, ∂P)` as
their disjoint union (`TauCeti.isColimitCofanCellCubeReplacementPullbackPairι`, an instance of
`TauCeti.isColimitCofanCellCubePairMap`), and additivity of relative cubical homology
(`TopPair.cubicalHomologyDirectSumEquiv`) with the computation over one cube identifies a
direct sum of copies of the homology of `F'_b`, one for each `(m + 1)`-cell, with the relative
homology of `(P, ∂P)`:

`⨁ⱼ H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`, `[z]ⱼ ↦ [append_*(z × [Iᵐ⁺¹])ⱼ]`

(`TauCeti.cellReplacementPullbackHomologyEquiv`,
`TauCeti.isCubicalRepresentative_cellReplacementPullbackHomologyEquiv`), where the `j`-th chain is
pushed forward along the append map of the radial paths of `j` (`TauCeti.cellAppendSection`).

The pair `(P, ∂P)` computes the quotients of the skeletal filtration of the chains on `E'`, the
filtration by the chains supported over the preimages of the skeleta of `C` under the end point
map, whose spectral sequence is the Serre spectral sequence of `E' → B`. Since `E' → B` is a
Hurewicz fibration, pushing chains forward along the projection `P → E'` is a quasi-isomorphism
from `C_*(P, ∂P)` onto the quotient of the chains over the `n`-skeleton by those over the
`(n - 1)`-skeleton (`TauCeti.MooreReplacement.exists_add_differential_sub_mem_preimageSkeleton`),
written on chains: every relative cycle is a relative boundary. Together with the computation of
`H_*(P, ∂P)` above, this is the cell-by-cell input of the comparison between the twisted complex
of a Brown model with coefficients in the chains of `F'_b` and the chains of `E'`, which
`BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_add_eq_of_forall_exists`
(in the namespace `TauCeti`) reduces to the quotients of the skeletal filtrations.

For the inclusion of the point `b`, `E'` is the space of Moore paths from `b` and `F'_b` the space
of Moore loops at `b`, and these are the computations
`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv` and
`TauCeti.cellPathPullbackHomologyEquiv` behind Brown's semi-free model of the chains on the based
path space, which additionally keep track of the action of the Moore loops at `b` by
concatenation in front.

## Main definitions

* `TauCeti.MooreReplacementPullback.appendSection τ h₀ h₁`: the map
  `((e, γ), d) ↦ (d, (e, γ ⋆ τ d))`.
* `TauCeti.cellReplacementPullbackPair p C n`: the pair `(P, ∂P)` over the `n`-cells.
* `TauCeti.cellAppendSection p C n γ j`: appending the radial paths of the `n`-cell `j`.
* `TauCeti.cellReplacementPullbackHomologyEquiv p γ k q`: the isomorphism
  `⨁ⱼ H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`.

## Main results

* `TauCeti.MooreReplacementPullback.fiberHomotopyEquiv_toFun_comp_prodSwap`: the append map is the
  fibre homotopy trivialization of the pullback, so that
  `TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv` computes the relative homology of
  the pullback over a cube.
* `TauCeti.MooreReplacementPullback.isZero_cubicalHomology_of_lt`,
  `TauCeti.isZero_cubicalHomology_cellReplacementPullbackPair_of_lt`: the relative homology
  vanishes below the dimension of the cube, or of the cells.
* `TauCeti.isColimitCofanCellCubeReplacementPullbackPairι`: the pullback over the disks of the
  `n`-cells is the disjoint union of the pullbacks over the single cells.
* `TauCeti.isCubicalRepresentative_cellReplacementPullbackHomologyEquiv`: for a cycle `z` of `F'_b`,
  the chain `append_*(z × [Iᵐ⁺¹])ⱼ` represents the image of `[z]` in the summand of the cell `j`.
* `TauCeti.MooreReplacement.exists_add_differential_sub_mem_preimageSkeleton`: the projection
  from `(P, ∂P)` is a quasi-isomorphism onto the quotient of consecutive stages of the skeletal
  filtration of the chains on `E'`.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.2 (Theorem 7.2.1).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Limits ContinuousMap
open scoped unitInterval

namespace TauCeti.MooreReplacementPullback

open MooreReplacement

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)} {b : B} {m : ℕ}
  {f : C(Fin (m + 1) → I, B)} (τ : C(Fin (m + 1) → I, MoorePath B))
  (h₀ : ∀ d, (τ d).source = b) (h₁ : ∀ d, (τ d).target = f d) (k : Type) [CommRing k]

/-- **Appending the chosen paths to the fibre**: `((e, γ), d) ↦ (d, (e, γ ⋆ τ d))`, the fibre
homotopy trivialization `TauCeti.MooreReplacementPullback.trivializationMap` with the fibre
factor first. -/
def appendSection : C(Fiber p b × (Fin (m + 1) → I), MooreReplacementPullback p f) :=
  (trivializationMap τ h₀ h₁).comp ContinuousMap.prodSwap

@[simp]
theorem appendSection_apply (z : Fiber p b × (Fin (m + 1) → I)) :
    appendSection τ h₀ h₁ z = trivializationMap τ h₀ h₁ (z.2, z.1) := (rfl)

/-- Appending the chosen paths is the fibre homotopy trivialization
`TauCeti.MooreReplacementPullback.fiberHomotopyEquiv`, with the fibre factor first. -/
theorem fiberHomotopyEquiv_toFun_comp_prodSwap :
    (fiberHomotopyEquiv (p := p) τ h₀ h₁).toFun.comp ContinuousMap.prodSwap =
      appendSection τ h₀ h₁ := by
  rw [fiberHomotopyEquiv_toFun]
  rfl

/-- Read in the total space of the replacement, appending the chosen paths is the append map
`F'_b × P_b B → E'` applied to the paths `τ d`, read as Moore paths from `b`. -/
theorem pullbackSnd_comp_appendSection :
    (pullbackSnd ⇑f ⇑(endpoint p)).comp (appendSection τ h₀ h₁) =
      (Fiber.appendFromMap p b).comp ((ContinuousMap.id _).prodMap
        ⟨fun d ↦ ⟨τ d, h₀ d⟩, τ.continuous.subtype_mk _⟩) :=
  ContinuousMap.ext fun _ ↦ by simp

/-- **The relative homology of the Moore-path replacement over a cube vanishes below the
dimension of the cube**: for every map `f : Iᵐ⁺¹ → B`,
`Hⱼ(f^*E', f^*E'|_{∂Iᵐ⁺¹}; k) = 0` for `j < m + 1`, over every commutative ring `k`. Along the
images of the straight segments from a corner of the cube (`TauCeti.MoorePath.cornerPaths`), the
pullback is fibre homotopy equivalent to the product of the cube with the fibre over `f 0`. -/
theorem isZero_cubicalHomology_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((TopPair.ofSubset (X := TopCat.of (MooreReplacementPullback p f))
      (pullbackFst ⇑f ⇑(endpoint p) ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex
        k).homology j) :=
  (fiberHomotopyEquiv (MoorePath.cornerPaths f) (MoorePath.source_cornerPaths f)
    (MoorePath.target_cornerPaths f)).isZero_cubicalHomology_of_lt k hj

end TauCeti.MooreReplacementPullback

/-! ### The cells of a CW complex -/

namespace TauCeti

open Metric Topology Topology.RelCWComplex MooreReplacement
open scoped _root_.DirectSum

section Cells

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {b : B}
  {C D : Set B} [RelCWComplex C D]

variable (C) in
/-- The pullback `P` of the Moore-path replacement `E' → B` of `p` to the disks of the `n`-cells,
relative to its part `∂P` over their boundary spheres. -/
abbrev cellReplacementPullbackPair (n : ℕ) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (MooreReplacementPullback p (sigmaCellMap C n)))
    (pullbackFst ⇑(sigmaCellMap C n) ⇑(endpoint p) ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1})

variable (C) in
/-- The pullback `Pⱼ` of the Moore-path replacement of `p` to the disk of the `n`-cell `j`, read on
the cube through `TauCeti.cellCubeMap`, relative to its part `∂Pⱼ` over the boundary of the cube. -/
abbrev cellCubeReplacementPullbackPair (n : ℕ) (j : cell C n) : TopPair.{0} :=
  TopPair.ofSubset
    (X := TopCat.of (MooreReplacementPullback p ((sigmaCellMap C n).comp (cellCubeMap C n j))))
    (pullbackFst ⇑((sigmaCellMap C n).comp (cellCubeMap C n j)) ⇑(endpoint p) ⁻¹'
      Cube.boundary (Fin n))

/-- The inclusion of the pullback over the cube of the `n`-cell `j` into the pullback over the
disks of all `n`-cells, induced by `TauCeti.cellCubeMap` on parameters. -/
private abbrev cellCubeMapPullbackFst (n : ℕ) (j : cell C n) :
    C(MooreReplacementPullback p ((sigmaCellMap C n).comp (cellCubeMap C n j)),
      MooreReplacementPullback p (sigmaCellMap C n)) :=
  mapPullbackFst (cellCubeMap C n j) rfl ⇑(endpoint p)

variable (C) in
/-- The inclusion `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` of the pullback over the disk of the `n`-cell `j` into the
pullback over the disks of all `n`-cells. -/
def cellCubeReplacementPullbackPairι (n : ℕ) (j : cell C n) :
    cellCubeReplacementPullbackPair p C n j ⟶ cellReplacementPullbackPair p C n :=
  cellCubePairMap _ _ j (cellCubeMapPullbackFst p n j) fun _ ↦ by simp

@[simp]
theorem cellCubeReplacementPullbackPairι_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellCubeReplacementPullbackPair p C n j).fst) :
    TopPair.Hom.fst (cellCubeReplacementPullbackPairι p C n j) x =
      mapPullbackFst (cellCubeMap C n j) rfl ⇑(endpoint p) x :=
  cellCubePairMap_fst_apply _ _ _ _ _ x

/-- The inclusion of the pullback over the cube of `j` is the map induced by `TauCeti.cellCubeMap`
on parameters. -/
theorem cellCubeReplacementPullbackPairι_fst_hom (n : ℕ) (j : cell C n) :
    (TopPair.Hom.fst (cellCubeReplacementPullbackPairι p C n j)).hom =
      mapPullbackFst (cellCubeMap C n j) rfl ⇑(endpoint p) :=
  ContinuousMap.ext (cellCubeReplacementPullbackPairι_fst_apply p n j)

variable (C) in
/-- **The pullback over the disks of the `n`-cells is the disjoint union of the pullbacks over the
single disks.** The inclusions `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` exhibit `(P, ∂P)` as the coproduct of the
pairs `(Pⱼ, ∂Pⱼ)` in `TopPair`. -/
def isColimitCofanCellCubeReplacementPullbackPairι (n : ℕ) :
    IsColimit (Cofan.mk (cellReplacementPullbackPair p C n)
      (cellCubeReplacementPullbackPairι p C n)) :=
  isColimitCofanCellCubePairMap _ _ (cellCubeMapPullbackFst p n) (fun _ _ ↦ by simp)
    (fun j ↦ isOpenEmbedding_mapPullbackFst _ _ _ (isOpenEmbedding_cellCubeMap n j))
    fun j y hj ↦ by
      -- A point over the disk of `j` comes from the pullback over the cube of `j`.
      rw [coe_pullbackFst] at hj
      subst hj
      rw [range_mapPullbackFst]
      exact ⟨(cubeHomeomorphClosedBall (Fin n)).symm y.fst.2, by simp⟩

variable (C) in
/-- **Appending the radial paths of the `n`-cell `j`**: the map
`((e, γ), d) ↦ (χ d, (e, γ ⋆ τ (χ d)))` from `F'_b × Iⁿ` to the pullback of the Moore-path
replacement to the disks of the `n`-cells, where `χ = TauCeti.cellCubeMap C n j` reads the disk of
`j` on the cube and `τ = TauCeti.cellRadialPaths C n γ` is the family of radial paths. -/
def cellAppendSection (n : ℕ) (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (j : cell C n) :
    C(Fiber p b × (Fin n → I), MooreReplacementPullback p (sigmaCellMap C n)) :=
  (MooreReplacementPullback.trivializationMap (cellRadialPaths C n γ) (source_cellRadialPaths γ)
    (target_cellRadialPaths γ)).comp
      ((cellCubeMap C n j).comp ContinuousMap.snd |>.prodMk ContinuousMap.fst)

@[simp]
theorem fst_cellAppendSection {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (j : cell C n) (z : Fiber p b × (Fin n → I)) :
    (cellAppendSection p C n γ j z).fst = cellCubeMap C n j z.2 := by
  simp [cellAppendSection]

@[simp]
theorem snd_cellAppendSection {n : ℕ}
    (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0)) (j : cell C n)
    (z : Fiber p b × (Fin n → I)) :
    (cellAppendSection p C n γ j z).snd =
      z.1.appendFrom ⟨cellRadialPaths C n γ (cellCubeMap C n j z.2), by simp⟩ := by
  simp [cellAppendSection]

section Homology

variable {m : ℕ} (γ : ∀ j : cell C (m + 1), MoorePathBetween B b (map (m + 1) j 0))
  (k : Type) [CommRing k]

/-- The fibre homotopy trivialization of the pullback over the cube of the cell `j` by the radial
paths of `j`. -/
private abbrev cellCubeFiberHomotopyEquiv (j : cell C (m + 1)) :=
  MooreReplacementPullback.fiberHomotopyEquiv (p := p) (cellCubeRadialPaths γ j)
    (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j)

/-- **The relative homology of the Moore-path replacement over the cells vanishes below their
dimension**: for the pullback `P` of `E' → B` to the disks of the `(m + 1)`-cells and its part
`∂P` over the boundary spheres, `Hⱼ(P, ∂P; k) = 0` for `j < m + 1`, over every commutative ring
`k`. It is the sum of the relative homology modules over the single cells. -/
theorem isZero_cubicalHomology_cellReplacementPullbackPair_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((cellReplacementPullbackPair p C (m + 1)).cubicalChainComplex k).homology j) :=
  TopPair.isZero_cubicalHomology_of_isColimit k
    (isColimitCofanCellCubeReplacementPullbackPairι p C (m + 1)) fun _ ↦
      MooreReplacementPullback.isZero_cubicalHomology_of_lt k hj

/-- The inclusion of the pullback over the cube of `j` carries the append map of the cube to the
append map of the cell `j`. -/
private theorem mapPullbackFst_comp_appendSection (j : cell C (m + 1)) :
    (cellCubeMapPullbackFst p (m + 1) j).comp
        (MooreReplacementPullback.appendSection (p := p) (cellCubeRadialPaths γ j)
          (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j)) =
      cellAppendSection p C (m + 1) γ j :=
  ContinuousMap.ext fun z ↦ Function.Pullback.ext (by simp) (by simp)

variable [DecidableEq (cell C (m + 1))]

/-- **The relative homology of the Moore-path replacement over the cells of a CW complex.** Let `P`
be the pullback of the Moore-path replacement `E' → B` of `p` to the disks of the `(m + 1)`-cells
and `∂P` its part over the boundary spheres. Given a Moore path from `b` to the centre of each
`(m + 1)`-cell, appending the radial paths of the cells
(`TauCeti.cellAppendSection`) identifies a direct sum of copies of the homology of the fibre `F'_b`,
one for each `(m + 1)`-cell, with the relative homology of `(P, ∂P)`, up to the shift by `m + 1`:

`⨁ⱼ H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`, `[z]ⱼ ↦ [append_*(z × [Iᵐ⁺¹])ⱼ]`

(`TauCeti.isCubicalRepresentative_cellReplacementPullbackHomologyEquiv`), over every commutative
ring `k`. On the cube of each cell it is
`TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv` for the trivialization by the radial
paths. -/
def cellReplacementPullbackHomologyEquiv (q : ℕ) :
    (⨁ _ : cell C (m + 1),
        ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homology q) ≃ₗ[k]
      ((cellReplacementPullbackPair p C (m + 1)).cubicalChainComplex k).homology (q + (m + 1)) :=
  TopPair.cubicalHomologyDirectSumEquiv k
    (isColimitCofanCellCubeReplacementPullbackPairι p C (m + 1)) (q + (m + 1)) fun j ↦
      (cellCubeFiberHomotopyEquiv p γ j).cubicalHomologyCubeBoundaryEquiv k q

/-- **`TauCeti.cellReplacementPullbackHomologyEquiv` appends the radial paths of the cells**: for a
`q`-cycle `z` of the fibre `F'_b` and an `(m + 1)`-cell `j`, the chain `append_*(z × [Iᵐ⁺¹])`, the
push-forward along `TauCeti.cellAppendSection` of the cross product of `z` with the identity cube,
is a relative cycle of `(P, ∂P)` representing the image of the class of `z` in the summand of
`j`. -/
theorem isCubicalRepresentative_cellReplacementPullbackHomologyEquiv (q : ℕ) (j : cell C (m + 1))
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).cycles q) :
    (cellReplacementPullbackPair p C (m + 1)).IsCubicalRepresentative k
      (NormalizedCubicalChain.map k (cellAppendSection p C (m + 1) γ j) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct (Fiber p b) (Fin (m + 1) → I) k q (m + 1)
          (normalizedCubicalChainComplexXEquiv _ q
            (((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).iCycles q z))
          (NormalizedCubicalChain.ofCube _ k (ContinuousMap.id _))))
      (cellReplacementPullbackHomologyEquiv p γ k q (DirectSum.lof k _ _ j
        (((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homologyπ q z))) := by
  rw [cellReplacementPullbackHomologyEquiv, TopPair.cubicalHomologyDirectSumEquiv_lof]
  have h := (FiberHomotopyEquiv.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv
    (cellCubeFiberHomotopyEquiv p γ j) k q z).map (cellCubeReplacementPullbackPairι p C (m + 1) j)
  rw [cellCubeReplacementPullbackPairι_fst_hom,
    MooreReplacementPullback.fiberHomotopyEquiv_toFun_comp_prodSwap] at h
  -- the inclusion of the cube of `j` after the append map of the cube is the append map of `j`
  rw [← mapPullbackFst_comp_appendSection, NormalizedCubicalChain.map_comp, LinearMap.comp_apply]
  exact h

end Homology

end Cells

/-! ### The skeletal filtration of the chains on the Moore-path replacement -/

section SkeletalFiltration

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] [T2Space B] (p : C(E, B))
  {C D : Set B} [RelCWComplex C D] {R : Type u} [CommRing R] (H : Type*)

/-- The pullback of the Moore-path replacement to the disks of the `n`-cells, as the pullback
`TauCeti.TopCat.cellPullback` of the end point map in `TopCat`. Both are the subtype of the
product of the disks with `E'` cut out by the same equation, so this is the identity on the
underlying pairs. -/
private def cellReplacementPullbackHomeomorph (n : ℕ) :
    MooreReplacementPullback p (sigmaCellMap C n) ≃ₜ
      TopCat.cellPullback (_root_.TopCat.ofHom (endpoint p)) C n :=
  Homeomorph.subtype (Homeomorph.refl _) fun _ ↦ Iff.rfl

omit [T2Space B] in
/-- `cellReplacementPullbackHomeomorph` is the identity on the underlying pairs. -/
private theorem val_cellReplacementPullbackHomeomorph (n : ℕ)
    (z : MooreReplacementPullback p (sigmaCellMap C n)) :
    (cellReplacementPullbackHomeomorph p (C := C) n z).val = z.val :=
  (rfl)

variable {p H} in
/-- **The quotients of the skeletal filtration of the chains on the Moore-path replacement are
computed over the cells.** Let `E'` be the total space of the Moore-path replacement of `p`, `P` the
pullback of its end point map `E' → B` along the characteristic maps of the `n`-cells and `∂P` its
part over the boundary spheres, the pair `TauCeti.cellReplacementPullbackPair`. Pushing chains
forward along the projection `P → E'` is a quasi-isomorphism from the relative chains `C_*(P, ∂P)`
onto the quotient of the chains of `E'` supported over the `n`-skeleton by those supported over the
`(n - 1)`-skeleton, in the following form: if `x` is a chain of `P` whose boundary lies over the
spheres and `y` a chain over the `n`-skeleton such that the push-forward of `x` minus the boundary
of `y` lies over the `(n - 1)`-skeleton, then `x` is the boundary of a chain `u` modulo the chains
over the spheres, and `y` is the push-forward of `u` plus the boundary of a chain `v` over the
`n`-skeleton, modulo the `(n - 1)`-skeleton. -/
theorem MooreReplacement.exists_add_differential_sub_mem_preimageSkeleton {n : ℕ}
    {x : cubicalChainModule (MooreReplacementPullback p (sigmaCellMap C n)) H R}
    {y : cubicalChainModule (MooreReplacement p) H R}
    (hx : cubicalChainModuleDifferential _ H R x ∈ cubicalChainModuleSupportedIn H R
      (pullbackFst ⇑(sigmaCellMap C n) ⇑(endpoint p) ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}))
    (hy : y ∈ cubicalChainModuleSupportedIn H R (preimageSkeleton C (endpoint p) n))
    (hxy : cubicalChainModuleLinearMap R (pullbackSnd ⇑(sigmaCellMap C n) ⇑(endpoint p)) x -
        cubicalChainModuleDifferential _ H R y ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C (endpoint p) (n - 1))) :
    ∃ (u : cubicalChainModule (MooreReplacementPullback p (sigmaCellMap C n)) H R)
      (v : cubicalChainModule (MooreReplacement p) H R),
      v ∈ cubicalChainModuleSupportedIn H R (preimageSkeleton C (endpoint p) n) ∧
        cubicalChainModuleDifferential _ H R u - x ∈ cubicalChainModuleSupportedIn H R
          (pullbackFst ⇑(sigmaCellMap C n) ⇑(endpoint p) ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}) ∧
        cubicalChainModuleLinearMap R (pullbackSnd ⇑(sigmaCellMap C n) ⇑(endpoint p)) u +
            cubicalChainModuleDifferential _ H R v - y ∈
          cubicalChainModuleSupportedIn H R (preimageSkeleton C (endpoint p) (n - 1)) :=
  TopCat.exists_add_differential_sub_mem_preimageSkeleton H
    (isHurewiczFibration_endpoint.{0} p).mem_serreFibrations
    (cellReplacementPullbackHomeomorph p n) (pullbackSnd _ _)
    (fun z ↦ by rw [val_cellReplacementPullbackHomeomorph, coe_pullbackSnd, Function.Pullback.snd])
    (fun z ↦ by
      rw [Set.mem_preimage, coe_pullbackFst, val_cellReplacementPullbackHomeomorph,
        Function.Pullback.fst, Set.mem_ofPred_eq])
    hx hy hxy

end SkeletalFiltration

end TauCeti
