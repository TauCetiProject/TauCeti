/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Cell
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

over every commutative ring `k`
(`TauCeti.MooreReplacementPullback.cubicalHomologyCubeBoundaryEquiv`,
`TauCeti.MooreReplacementPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`). Below
degree `m + 1` the relative homology vanishes
(`TauCeti.MooreReplacementPullback.isZero_cubicalHomology_of_lt`).

The append map is, up to the interchange of the factors, the fibre homotopy trivialization
`TauCeti.MooreReplacementPullback.fiberHomotopyEquiv` of the pullback, so it induces isomorphisms
of relative homology over `∂Iᵐ⁺¹`, and the relative Künneth theorem for the cube pair
(`TauCeti.cubicalHomologyCubeBoundaryPairProdLeftEquiv`) identifies the classes `z × [Iᵐ⁺¹]` with
the homology of `F'_b`. Read in `E'`, the representing chain `append_*(z × [Iᵐ⁺¹])` is the image
of `z × [τ]` under the append map `F'_b × P_b B → E'`
(`TauCeti.MooreReplacementPullback.toMooreReplacement_comp_appendSection`), the form in which a
chain of `F'_b` and a chain of paths from `b` are paired in the comparison between the twisted
complex of a Brown model, with coefficients in the chains of `F'_b`, and the chains of `E'`.

The second part of the file assembles the cells. Let `C ⊆ B` be a relative CW complex, `P` the
pullback of `E' → B` along the characteristic maps of the `(m + 1)`-cells (`TauCeti.sigmaCellMap`)
and `∂P` its part over their boundary spheres (`TauCeti.cellReplacementPullbackPair`). Choose a
Moore path from `b` to the centre of each cell, and follow it by the images of radial segments
(`TauCeti.cellRadialPaths`). The pullbacks over the cubes of the single cells exhibit `(P, ∂P)` as
their disjoint union (`TauCeti.isColimitCofanCellCubeReplacementPullbackPairι`), and additivity of
relative cubical homology with the computation over one cube identifies a direct sum of copies of
the homology of `F'_b`, one for each `(m + 1)`-cell, with the relative homology of `(P, ∂P)`:

`⨁ⱼ H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`, `[z]ⱼ ↦ [append_*(z × [Iᵐ⁺¹])ⱼ]`

(`TauCeti.cellReplacementPullbackHomologyEquiv`,
`TauCeti.isCubicalRepresentative_cellReplacementPullbackHomologyEquiv`), where the `j`-th chain is
pushed forward along the append map of the radial paths of `j` (`TauCeti.cellAppendSection`).

For the inclusion of the point `b`, `E'` is the space of Moore paths from `b` and `F'_b` the space
of Moore loops at `b`, and these are the computations
`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv` and
`TauCeti.cellPathPullbackHomologyEquiv` behind Brown's semi-free model of the chains on the based
path space, which additionally keep track of the action of the Moore loops at `b` by
concatenation in front.

## Main definitions

* `TauCeti.MooreReplacementPullback.appendSection τ h₀ h₁`: the map
  `((e, γ), d) ↦ (d, (e, γ ⋆ τ d))`.
* `TauCeti.MooreReplacementPullback.cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q`: the isomorphism
  `H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(f^*E', f^*E'|_{∂Iᵐ⁺¹}; k)`.
* `TauCeti.cellReplacementPullbackPair p C n`: the pair `(P, ∂P)` over the `n`-cells.
* `TauCeti.cellAppendSection p C n γ j`: appending the radial paths of the `n`-cell `j`.
* `TauCeti.cellReplacementPullbackHomologyEquiv p γ k q`: the isomorphism
  `⨁ⱼ H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`.

## Main results

* `TauCeti.MooreReplacementPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`: for a
  cycle `z` of `F'_b`, the chain `append_*(z × [Iᵐ⁺¹])` represents the image of `[z]`.
* `TauCeti.MooreReplacementPullback.isZero_cubicalHomology_of_lt`,
  `TauCeti.isZero_cubicalHomology_cellReplacementPullbackPair_of_lt`: the relative homology
  vanishes below the dimension of the cube, or of the cells.
* `TauCeti.isColimitCofanCellCubeReplacementPullbackPairι`: the pullback over the disks of the
  `n`-cells is the disjoint union of the pullbacks over the single cells.
* `TauCeti.isCubicalRepresentative_cellReplacementPullbackHomologyEquiv`: for a cycle `z` of `F'_b`,
  the chain `append_*(z × [Iᵐ⁺¹])ⱼ` represents the image of `[z]` in the summand of the cell `j`.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.2 (Theorem 7.2.1).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Limits
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

/-- Read in the total space of the replacement, appending the chosen paths is the append map
`F'_b × P_b B → E'` applied to the paths `τ d`, read as Moore paths from `b`. -/
theorem toMooreReplacement_comp_appendSection :
    (toMooreReplacement p f).comp (appendSection τ h₀ h₁) =
      (Fiber.appendFromMap p b).comp ((ContinuousMap.id _).prodMap
        ⟨fun d ↦ ⟨τ d, h₀ d⟩, τ.continuous.subtype_mk _⟩) :=
  ContinuousMap.ext fun _ ↦ by simp

/-- The fibre homotopy trivialization `TauCeti.MooreReplacementPullback.fiberHomotopyEquiv`, with
the fibre factor first. -/
private def fiberFirstHomotopyEquiv :
    FiberHomotopyEquiv (ContinuousMap.snd : C(Fiber p b × (Fin (m + 1) → I), _)) (proj p f) :=
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.prodComm _ _) rfl).trans
    (fiberHomotopyEquiv τ h₀ h₁)

/-- The map of pairs `F'_b × (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (f^*E', f^*E'|_{∂Iᵐ⁺¹})` of
`TauCeti.MooreReplacementPullback.appendSection`. -/
private def appendSectionPairMap :
    (cubeBoundaryPair.{0} (m + 1)).prodLeft (TopCat.of (Fiber p b)) ⟶
      TopPair.ofSubset (X := TopCat.of (MooreReplacementPullback p f))
        (proj p f ⁻¹' Cube.boundary (Fin (m + 1))) :=
  (cubeBoundaryPairProdLeftIso (TopCat.of (Fiber p b)) (m + 1)).hom ≫
    (fiberFirstHomotopyEquiv τ h₀ h₁).preimagePairMap (Cube.boundary (Fin (m + 1)))

private theorem fiberFirstHomotopyEquiv_toFun_apply (z : Fiber p b × (Fin (m + 1) → I)) :
    (fiberFirstHomotopyEquiv τ h₀ h₁).toFun z = appendSection τ h₀ h₁ z := by
  simp [fiberFirstHomotopyEquiv, Prod.swap]

/-- On the ambient spaces, the map of pairs is `TauCeti.MooreReplacementPullback.appendSection`,
after lowering the cube coordinate out of `ULift`. -/
private theorem appendSectionPairMap_fst :
    (TopPair.Hom.fst (appendSectionPairMap τ h₀ h₁)).hom =
      (appendSection (p := p) τ h₀ h₁).comp
        ((ContinuousMap.id _).prodMap ⟨ULift.down, continuous_uliftDown⟩) := by
  ext1 z
  simp only [appendSectionPairMap, TopPair.Hom.fst_comp, FiberHomotopyEquiv.preimagePairMap_fst]
  -- the isomorphism of pairs lowers the cube coordinate, then the trivialization appends `τ`
  exact (congrArg (fiberFirstHomotopyEquiv τ h₀ h₁).toFun
    (cubeBoundaryPairProdLeftIso_hom_fst_apply (TopCat.of (Fiber p b)) (m + 1) z)).trans
      (fiberFirstHomotopyEquiv_toFun_apply τ h₀ h₁ (z.1, z.2.down))

/-- The map of pairs induces isomorphisms of relative homology: it is an isomorphism of pairs
followed by the map of pairs of a fibre homotopy equivalence. -/
private theorem isIso_homologyMap_appendSectionPairMap (n : ℕ) :
    IsIso (homologyMap (TopPair.cubicalChainComplexMap k
      (appendSectionPairMap (p := p) τ h₀ h₁)) n) := by
  rw [appendSectionPairMap, TopPair.cubicalChainComplexMap_comp, homologyMap_comp]
  have : IsIso (homologyMap (TopPair.cubicalChainComplexMap k
      ((fiberFirstHomotopyEquiv (p := p) τ h₀ h₁).preimagePairMap
        (Cube.boundary (Fin (m + 1))))) n) := by
    rw [← FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_hom]
    infer_instance
  infer_instance

/-- **The relative homology of the Moore-path replacement over a cube**: for a continuous family
`τ` of Moore paths from `b` to the points of `f : Iᵐ⁺¹ → B`, appending `τ` to the fibre `F'_b` is
an isomorphism `H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(f^*E', f^*E'|_{∂Iᵐ⁺¹}; k)`,
`[z] ↦ [append_*(z × [Iᵐ⁺¹])]`
(`TauCeti.MooreReplacementPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`), over
every commutative ring `k`. -/
def cubicalHomologyCubeBoundaryEquiv (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homology q ≃ₗ[k]
      ((TopPair.ofSubset (X := TopCat.of (MooreReplacementPullback p f))
        (proj p f ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology
          (q + (m + 1)) :=
  have := isIso_homologyMap_appendSectionPairMap (p := p) τ h₀ h₁ k (q + (m + 1))
  cubicalHomologyCubeBoundaryPairProdLeftEquiv k (TopCat.of (Fiber p b)) m q ≪≫ₗ
    (asIso (homologyMap (TopPair.cubicalChainComplexMap k (appendSectionPairMap τ h₀ h₁))
      (q + (m + 1)))).toLinearEquiv

/-- The images under `f` of the straight segments from the corner `0` of the cube to its
points. -/
private def cornerPaths (f : C(Fin (m + 1) → I, B)) : C(Fin (m + 1) → I, MoorePath B) :=
  let H : C((Fin (m + 1) → I) × I, B) := f.comp ⟨fun z i ↦ z.2 * z.1 i, by fun_prop⟩
  ⟨fun d ↦ MoorePath.ofUnitPath (H.curry d),
    MoorePath.continuous_ofUnitPath.comp H.curry.continuous⟩

private theorem source_cornerPaths (f : C(Fin (m + 1) → I, B)) (d : Fin (m + 1) → I) :
    (cornerPaths f d).source = f 0 := by
  simp [cornerPaths, Pi.zero_def]

private theorem target_cornerPaths (f : C(Fin (m + 1) → I, B)) (d : Fin (m + 1) → I) :
    (cornerPaths f d).target = f d := by
  simp [cornerPaths]

/-- **The relative homology of the Moore-path replacement over a cube vanishes below the
dimension of the cube**: for every map `f : Iᵐ⁺¹ → B`,
`Hⱼ(f^*E', f^*E'|_{∂Iᵐ⁺¹}; k) = 0` for `j < m + 1`, over every commutative ring `k`. The images
of the straight segments from a corner of the cube give a family of paths from `f 0` to the
points of `f`, along which the pullback is a product with the fibre over `f 0`. -/
theorem isZero_cubicalHomology_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((TopPair.ofSubset (X := TopCat.of (MooreReplacementPullback p f))
      (proj p f ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology j) :=
  have := isIso_homologyMap_appendSectionPairMap (p := p) (cornerPaths f) (source_cornerPaths f)
    (target_cornerPaths f) k j
  (isZero_cubicalHomology_cubeBoundaryPair_prodLeft_of_lt k (TopCat.of (Fiber p (f 0))) m
    hj).of_iso (asIso (homologyMap (TopPair.cubicalChainComplexMap k
      (appendSectionPairMap (cornerPaths f) (source_cornerPaths f) (target_cornerPaths f)))
        j)).symm

/-- On chains, the map of pairs sends the cross product of a chain `a` of `F'_b` with the identity
cube of the cube model to `append_*(a × [Iᵐ⁺¹])`. -/
private theorem map_crossProduct_upCube {q : ℕ} (a : NormalizedCubicalChain (Fiber p b) k q) :
    NormalizedCubicalChain.map k (TopPair.Hom.fst (appendSectionPairMap τ h₀ h₁)).hom
        (q + (m + 1))
        (NormalizedCubicalChain.crossProduct (Fiber p b) (ULift.{0} (Fin (m + 1) → I)) k
          q (m + 1) a (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) =
      NormalizedCubicalChain.map k (appendSection τ h₀ h₁) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct (Fiber p b) (Fin (m + 1) → I) k q (m + 1) a
          (NormalizedCubicalChain.ofCube _ k (ContinuousMap.id _))) := by
  -- lowering the cube coordinate sends the identity cube of the model to the identity cube
  have hc : NormalizedCubicalChain.ofCube (Fin (m + 1) → I) k (ContinuousMap.id _) =
      NormalizedCubicalChain.map k ⟨ULift.down, continuous_uliftDown⟩ (m + 1)
        (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1))) := by
    rw [NormalizedCubicalChain.map_ofCube]
    exact congrArg _ (ContinuousMap.ext fun _ ↦ rfl)
  have hx : NormalizedCubicalChain.crossProduct _ _ k q (m + 1) a
      (NormalizedCubicalChain.map k ⟨ULift.down, continuous_uliftDown⟩ (m + 1)
        (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) =
      NormalizedCubicalChain.map k
        ((ContinuousMap.id _).prodMap ⟨ULift.down, continuous_uliftDown⟩) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct _ _ k q (m + 1) a
          (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) := by
    rw [NormalizedCubicalChain.map_crossProduct, NormalizedCubicalChain.map_id, LinearMap.id_apply]
  rw [hc, hx, ← LinearMap.comp_apply (NormalizedCubicalChain.map k (appendSection τ h₀ h₁) _),
    ← NormalizedCubicalChain.map_comp]
  exact congrArg (fun φ ↦ NormalizedCubicalChain.map k φ (q + (m + 1)) _)
    (appendSectionPairMap_fst τ h₀ h₁)

/-- **The isomorphism `H_q(F'_b) ≃ H_{q+m+1}(f^*E', f^*E'|_{∂Iᵐ⁺¹})` appends the chosen paths**:
for a `q`-cycle `z` of the fibre `F'_b`, the chain `append_*(z × [Iᵐ⁺¹])`, the push-forward along
`TauCeti.MooreReplacementPullback.appendSection` of the cross product of `z` with the identity cube,
is a relative cycle representing the image of the class of `z`. -/
theorem isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).cycles q) :
    (TopPair.ofSubset (X := TopCat.of (MooreReplacementPullback p f))
        (proj p f ⁻¹' Cube.boundary (Fin (m + 1)))).IsCubicalRepresentative k
      (NormalizedCubicalChain.map k (appendSection τ h₀ h₁) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct (Fiber p b) (Fin (m + 1) → I) k q (m + 1)
          (normalizedCubicalChainComplexXEquiv _ q
            (((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).iCycles q z))
          (NormalizedCubicalChain.ofCube _ k (ContinuousMap.id _))))
      (cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q
        (((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homologyπ q z)) := by
  -- The representing relative cycle is the image of `z × [Iᵐ⁺¹]` under the map of pairs.
  refine (TopPair.isCubicalRepresentative_iff _ _).2
    ⟨(cyclesMap (TopPair.cubicalChainComplexMap k (appendSectionPairMap τ h₀ h₁)) _).hom
    ((cyclesMap (cubicalCrossProductRel k _ (cubeBoundaryPair.{0} (m + 1))) (q + (m + 1))).hom
      ((cyclesCross ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b)))
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
    (MooreReplacementPullback.proj p (sigmaCellMap C n) ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1})

variable (C) in
/-- The pullback `Pⱼ` of the Moore-path replacement of `p` to the disk of the `n`-cell `j`, read on
the cube through `TauCeti.cellCubeMap`, relative to its part `∂Pⱼ` over the boundary of the cube. -/
abbrev cellCubeReplacementPullbackPair (n : ℕ) (j : cell C n) : TopPair.{0} :=
  TopPair.ofSubset
    (X := TopCat.of (MooreReplacementPullback p ((sigmaCellMap C n).comp (cellCubeMap C n j))))
    (MooreReplacementPullback.proj p ((sigmaCellMap C n).comp (cellCubeMap C n j)) ⁻¹'
      Cube.boundary (Fin n))

variable (C) in
/-- The inclusion `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` of the pullback over the disk of the `n`-cell `j` into the
pullback over the disks of all `n`-cells. -/
def cellCubeReplacementPullbackPairι (n : ℕ) (j : cell C n) :
    cellCubeReplacementPullbackPair p C n j ⟶ cellReplacementPullbackPair p C n :=
  TopPair.ofSubsetMap (TopCat.ofHom (MooreReplacementPullback.paramMap (cellCubeMap C n j)))
    (by intro x hx; simpa [norm_cubeHomeomorphClosedBall_eq_one_iff] using hx)

@[simp]
theorem cellCubeReplacementPullbackPairι_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellCubeReplacementPullbackPair p C n j).fst) :
    TopPair.Hom.fst (cellCubeReplacementPullbackPairι p C n j) x =
      MooreReplacementPullback.paramMap (cellCubeMap C n j) x :=
  TopPair.ofSubsetMap_fst_apply _ _ x

/-- The inclusion of the pullback over the cube of `j` is the map induced by `TauCeti.cellCubeMap`
on parameters. -/
theorem cellCubeReplacementPullbackPairι_fst_hom (n : ℕ) (j : cell C n) :
    (TopPair.Hom.fst (cellCubeReplacementPullbackPairι p C n j)).hom =
      MooreReplacementPullback.paramMap (cellCubeMap C n j) :=
  ContinuousMap.ext (cellCubeReplacementPullbackPairι_fst_apply p n j)

/-- The disjoint union of the pullbacks over the disks of the `n`-cells maps homeomorphically onto
the pullback over all of them. -/
private theorem isHomeomorph_sigma_paramMap_cellCubeMap (n : ℕ) :
    IsHomeomorph fun x : Σ j : cell C n,
        MooreReplacementPullback p ((sigmaCellMap C n).comp (cellCubeMap C n j)) ↦
      MooreReplacementPullback.paramMap (cellCubeMap C n x.1) x.2 := by
  refine ⟨continuous_sigma fun j ↦ (MooreReplacementPullback.paramMap _).continuous,
    isOpenMap_sigma.2 fun j ↦ (MooreReplacementPullback.isOpenEmbedding_paramMap _
      (isOpenEmbedding_cellCubeMap n j)).isOpenMap, ?_⟩
  refine ⟨fun ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ h ↦ ?_, fun y ↦ ?_⟩
  · -- The cell is read off from the point of the disk, and on a single cell the map is injective.
    obtain rfl : j₁ = j₂ := by simpa using congrArg (fun y ↦ y.point.1) h
    exact Sigma.ext rfl <| heq_of_eq <| (MooreReplacementPullback.isOpenEmbedding_paramMap _
      (isOpenEmbedding_cellCubeMap n j₁)).injective h
  · -- A point over a point of the disk of `j` comes from the pullback over the cube of `j`.
    obtain ⟨x, hx⟩ : y ∈ Set.range
        (MooreReplacementPullback.paramMap (p := p) (cellCubeMap C n y.point.1)) := by
      rw [MooreReplacementPullback.range_paramMap]
      exact ⟨(cubeHomeomorphClosedBall (Fin n)).symm y.point.2, by simp⟩
    exact ⟨⟨_, x⟩, hx⟩

variable (C) in
/-- **The pullback over the disks of the `n`-cells is the disjoint union of the pullbacks over the
single disks.** The inclusions `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` exhibit `(P, ∂P)` as the coproduct of the
pairs `(Pⱼ, ∂Pⱼ)` in `TopPair`. -/
def isColimitCofanCellCubeReplacementPullbackPairι (n : ℕ) :
    IsColimit (Cofan.mk (cellReplacementPullbackPair p C n)
      (cellCubeReplacementPullbackPairι p C n)) :=
  TopPair.isColimitCofanOfIsHomeomorph _ (by
    simp only [cellCubeReplacementPullbackPairι_fst_apply]
    exact isHomeomorph_sigma_paramMap_cellCubeMap (C := C) p n) fun y ↦ by
    -- A point over a boundary sphere comes from the pullback over its cube, over the boundary.
    obtain ⟨x, hx⟩ :=
      (isHomeomorph_sigma_paramMap_cellCubeMap (C := C) p n).bijective.2 y.val
    have hy : ‖((MooreReplacementPullback.proj p (sigmaCellMap C n) y.val).2 : Fin n → ℝ)‖ = 1 :=
      y.property
    rw [← hx, MooreReplacementPullback.proj_apply, MooreReplacementPullback.point_paramMap,
      cellCubeMap_apply, norm_cubeHomeomorphClosedBall_eq_one_iff] at hy
    exact ⟨x.1, ⟨x.2, by rwa [Set.mem_preimage, MooreReplacementPullback.proj_apply]⟩,
      (cellCubeReplacementPullbackPairι_fst_apply p n x.1 x.2).trans hx⟩

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
theorem point_cellAppendSection {n : ℕ} (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0))
    (j : cell C n) (z : Fiber p b × (Fin n → I)) :
    (cellAppendSection p C n γ j z).point = cellCubeMap C n j z.2 := by
  simp [cellAppendSection]

@[simp]
theorem replacement_cellAppendSection {n : ℕ}
    (γ : ∀ j : cell C n, MoorePathBetween B b (map n j 0)) (j : cell C n)
    (z : Fiber p b × (Fin n → I)) :
    (cellAppendSection p C n γ j z).replacement =
      z.1.appendFrom ⟨cellRadialPaths C n γ (cellCubeMap C n j z.2), by simp⟩ := by
  simp [cellAppendSection]

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

/-- The identification of the homology of the fibre with the relative homology of the pullback
over the cube of the cell `j`, by
`TauCeti.MooreReplacementPullback.cubicalHomologyCubeBoundaryEquiv` for the radial paths. -/
private def cellCubeHomologyEquiv (j : cell C (m + 1)) (q : ℕ) :=
  MooreReplacementPullback.cubicalHomologyCubeBoundaryEquiv (p := p) (cellCubeRadialPaths γ j)
    (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j) k q

/-- The map `H_q(F'_b) → H_{q+m+1}(P, ∂P)` of the cell `j`: the identification over the cube of
`j`, followed by the inclusion of the pullback over the cube of `j`. -/
private def cellHomologyLeg (q : ℕ) (j : cell C (m + 1)) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homology q ⟶
      ((cellReplacementPullbackPair p C (m + 1)).cubicalChainComplex k).homology (q + (m + 1)) :=
  (cellCubeHomologyEquiv p γ k j q).toModuleIso.hom ≫ HomologicalComplex.homologyMap
    (TopPair.cubicalChainComplexMap k (cellCubeReplacementPullbackPairι p C (m + 1) j))
      (q + (m + 1))

/-- The maps of the cells exhibit the relative homology of the pullback over the disks of all
`(m + 1)`-cells as a coproduct of copies of the homology of the fibre. -/
private def isColimitCofanCellHomologyLeg (q : ℕ) :
    IsColimit (Cofan.mk (((cellReplacementPullbackPair p C (m + 1)).cubicalChainComplex k).homology
      (q + (m + 1))) (cellHomologyLeg p γ k q)) :=
  have : IsIso (Sigma.desc fun j ↦ HomologicalComplex.homologyMap
      (TopPair.cubicalChainComplexMap k (cellCubeReplacementPullbackPairι p C (m + 1) j))
        (q + (m + 1))) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).1
      ⟨TopPair.isColimitCofanCubicalHomologyOfIsColimit k
        (isColimitCofanCellCubeReplacementPullbackPairι p C (m + 1)) (q + (m + 1))⟩
  have : IsIso (Sigma.desc (cellHomologyLeg p γ k q)) := by
    -- Each leg is the leg of additivity precomposed with an isomorphism.
    rw [show Sigma.desc (cellHomologyLeg p γ k q) =
        (Sigma.mapIso fun j ↦ (cellCubeHomologyEquiv p γ k j q).toModuleIso).hom ≫
          Sigma.desc fun j ↦ HomologicalComplex.homologyMap
            (TopPair.cubicalChainComplexMap k (cellCubeReplacementPullbackPairι p C (m + 1) j))
              (q + (m + 1)) from
      Sigma.hom_ext _ _ fun j ↦ by simp [cellHomologyLeg]]
    infer_instance
  Cofan.isColimitOfIsIsoSigmaDesc (hc := this) _

/-- **The relative homology of the Moore-path replacement over the cells vanishes below their
dimension**: for the pullback `P` of `E' → B` to the disks of the `(m + 1)`-cells and its part
`∂P` over the boundary spheres, `Hⱼ(P, ∂P; k) = 0` for `j < m + 1`, over every commutative ring
`k`. It is the sum of the relative homology modules over the single cells. -/
theorem isZero_cubicalHomology_cellReplacementPullbackPair_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((cellReplacementPullbackPair p C (m + 1)).cubicalChainComplex k).homology j) :=
  (IsZero.iff_id_eq_zero _).2 <| Cofan.IsColimit.hom_ext
    (TopPair.isColimitCofanCubicalHomologyOfIsColimit k
      (isColimitCofanCellCubeReplacementPullbackPairι p C (m + 1)) j) _ _ fun _ ↦
    (MooreReplacementPullback.isZero_cubicalHomology_of_lt (p := p) k hj).eq_of_src _ _

/-- The inclusion of the pullback over the cube of `j` carries the append map of the cube to the
append map of the cell `j`. -/
private theorem paramMap_comp_appendSection (j : cell C (m + 1)) :
    (MooreReplacementPullback.paramMap (cellCubeMap C (m + 1) j)).comp
        (MooreReplacementPullback.appendSection (p := p) (cellCubeRadialPaths γ j)
          (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j)) =
      cellAppendSection p C (m + 1) γ j :=
  ContinuousMap.ext fun z ↦ MooreReplacementPullback.ext (by simp) (by simp)

variable [DecidableEq (cell C (m + 1))]

/-- **The relative homology of the Moore-path replacement over the cells of a CW complex.** Let `P`
be the pullback of the Moore-path replacement `E' → B` of `p` to the disks of the `(m + 1)`-cells
and `∂P` its part over the boundary spheres. Given a Moore path from `b` to the centre of each
`(m + 1)`-cell, appending the radial paths of the cells
(`TauCeti.cellAppendSection`) identifies a direct sum of copies of the homology of the fibre `F'_b`,
one for each `(m + 1)`-cell, with the relative homology of `(P, ∂P)`, up to the shift by `m + 1`:

`⨁ⱼ H_q(F'_b; k) ≃ₗ[k] H_{q+m+1}(P, ∂P; k)`, `[z]ⱼ ↦ [append_*(z × [Iᵐ⁺¹])ⱼ]`

(`TauCeti.isCubicalRepresentative_cellReplacementPullbackHomologyEquiv`), over every commutative
ring `k`. -/
def cellReplacementPullbackHomologyEquiv (q : ℕ) :
    (⨁ _ : cell C (m + 1),
        ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homology q) ≃ₗ[k]
      ((cellReplacementPullbackPair p C (m + 1)).cubicalChainComplex k).homology (q + (m + 1)) :=
  ((ModuleCat.coproductCoconeIsColimit _).coconePointUniqueUpToIso
    (isColimitCofanCellHomologyLeg p γ k q)).toLinearEquiv

/-- On the summand of the cell `j`, `TauCeti.cellReplacementPullbackHomologyEquiv` is the map of
`j`. -/
private theorem cellReplacementPullbackHomologyEquiv_lof (q : ℕ) (j : cell C (m + 1))
    (x : ((normalizedCubicalChainComplex k).obj (TopCat.of (Fiber p b))).homology q) :
    cellReplacementPullbackHomologyEquiv p γ k q (DirectSum.lof k _ _ j x) =
      cellHomologyLeg p γ k q j x :=
  ConcreteCategory.congr_hom
    ((ModuleCat.coproductCoconeIsColimit _).comp_coconePointUniqueUpToIso_hom
      (isColimitCofanCellHomologyLeg p γ k q) ⟨j⟩) x

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
  rw [cellReplacementPullbackHomologyEquiv_lof, cellHomologyLeg, ModuleCat.comp_apply]
  have h := (MooreReplacementPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv
    (cellCubeRadialPaths γ j) (source_cellCubeRadialPaths γ j) (target_cellCubeRadialPaths γ j)
      k q z).map (cellCubeReplacementPullbackPairι p C (m + 1) j)
  rw [cellCubeReplacementPullbackPairι_fst_hom] at h
  -- the inclusion of the cube of `j` after the append map of the cube is the append map of `j`
  rw [← paramMap_comp_appendSection, NormalizedCubicalChain.map_comp, LinearMap.comp_apply]
  -- the pair of the cells is `TopPair.ofSubset` of the pullback only up to unfolding
  exact h

end Homology

end Cells

end TauCeti
