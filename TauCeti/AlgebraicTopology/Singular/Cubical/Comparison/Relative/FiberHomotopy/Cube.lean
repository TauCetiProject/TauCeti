/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.FiberHomotopy.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Kunneth

/-!
# The relative homology of a space fibre homotopy trivial over a cube

Let `π : Y → Iᵐ⁺¹` be a space over a cube of positive dimension, and `e` a fibre homotopy
equivalence over the cube from the product `Iᵐ⁺¹ × F` to `Y`. Then `e` identifies the homology of
the fibre `F` with the relative homology of `Y` over the boundary of the cube, up to the shift by
the dimension of the cube:

`H_q(F; k) ≃ₗ[k] H_{q+m+1}(Y, π⁻¹ ∂Iᵐ⁺¹; k)`,  `[z] ↦ [e_*(z × [Iᵐ⁺¹])]`,

over every commutative ring `k` (`TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv`,
`TauCeti.FiberHomotopyEquiv.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`), where
`z × [Iᵐ⁺¹]` is the cross product of `z` with the identity cube, read in `Iᵐ⁺¹ × F` after
interchanging the factors. Below degree `m + 1` the relative homology vanishes
(`TauCeti.FiberHomotopyEquiv.isZero_cubicalHomology_of_lt`).

The map of pairs `F × (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (Y, π⁻¹ ∂Iᵐ⁺¹)` of `e` induces isomorphisms of relative
homology (`TauCeti.FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv`), and the relative Künneth
theorem for the cube pair (`TauCeti.cubicalHomologyCubeBoundaryPairProdLeftEquiv`) identifies the
classes `z × [Iᵐ⁺¹]` with the homology of `F`.

A continuous family of paths from a base point to the points of a map `f : Iᵐ⁺¹ → B` trivializes the
pullback along `f` of a path fibration up to fibre homotopy, as for the based path fibration
(`TauCeti.MoorePathPullback.fiberHomotopyEquiv`) or the Moore-path replacement of any map
(`TauCeti.MooreReplacementPullback.fiberHomotopyEquiv`). This is the computation of the relative
homology of such a pullback over one cell.

## Main definitions

* `TauCeti.FiberHomotopyEquiv.cubicalHomologyCubeBoundaryEquiv e k q`: the isomorphism
  `H_q(F; k) ≃ₗ[k] H_{q+m+1}(Y, π⁻¹ ∂Iᵐ⁺¹; k)`.

## Main results

* `TauCeti.FiberHomotopyEquiv.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`: for a
  cycle `z` of `F`, the chain `e_*(z × [Iᵐ⁺¹])` represents the image of `[z]`.
* `TauCeti.FiberHomotopyEquiv.isZero_cubicalHomology_of_lt`: the relative homology vanishes below
  degree `m + 1`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 and §7.2.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Limits
open scoped unitInterval

namespace TauCeti.FiberHomotopyEquiv

variable {F Y : Type} [TopologicalSpace F] [TopologicalSpace Y] {m : ℕ}
  {π : C(Y, Fin (m + 1) → I)}
  (e : FiberHomotopyEquiv (ContinuousMap.fst : C((Fin (m + 1) → I) × F, Fin (m + 1) → I)) π)
  (k : Type) [CommRing k]

/-- `e`, with the fibre factor first. -/
private def fiberFirst :
    FiberHomotopyEquiv (ContinuousMap.snd : C(F × (Fin (m + 1) → I), Fin (m + 1) → I)) π :=
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.prodComm _ _) rfl).trans e

private theorem fiberFirst_toFun :
    (fiberFirst e).toFun = e.toFun.comp ContinuousMap.prodSwap :=
  ContinuousMap.ext fun _ ↦ by simp [fiberFirst, Prod.swap]

/-- The map of pairs `F × (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (Y, π⁻¹ ∂Iᵐ⁺¹)` of `e`. -/
private def cubeBoundaryPairMap :
    (cubeBoundaryPair.{0} (m + 1)).prodLeft (TopCat.of F) ⟶
      TopPair.ofSubset (X := TopCat.of Y) (π ⁻¹' Cube.boundary (Fin (m + 1))) :=
  (cubeBoundaryPairProdLeftIso (TopCat.of F) (m + 1)).hom ≫
    (fiberFirst e).preimagePairMap (Cube.boundary (Fin (m + 1)))

/-- On the ambient spaces, the map of pairs is `e` after interchanging the factors and lowering the
cube coordinate out of `ULift`. -/
private theorem cubeBoundaryPairMap_fst :
    (TopPair.Hom.fst (cubeBoundaryPairMap e)).hom =
      (e.toFun.comp ContinuousMap.prodSwap).comp
        ((ContinuousMap.id _).prodMap ⟨ULift.down, continuous_uliftDown⟩) := by
  ext1 z
  simp only [cubeBoundaryPairMap, TopPair.Hom.fst_comp, FiberHomotopyEquiv.preimagePairMap_fst]
  -- the isomorphism of pairs lowers the cube coordinate, then `e` acts with the factors swapped
  exact (congrArg (fiberFirst e).toFun
    (cubeBoundaryPairProdLeftIso_hom_fst_apply (TopCat.of F) (m + 1) z)).trans
      (congrArg (fun φ : C(F × (Fin (m + 1) → I), Y) ↦ φ (z.1, z.2.down)) (fiberFirst_toFun e))

/-- The map of pairs induces isomorphisms of relative homology: it is an isomorphism of pairs
followed by the map of pairs of a fibre homotopy equivalence. -/
private theorem isIso_homologyMap_cubeBoundaryPairMap (n : ℕ) :
    IsIso (homologyMap (TopPair.cubicalChainComplexMap k (cubeBoundaryPairMap e)) n) := by
  rw [cubeBoundaryPairMap, TopPair.cubicalChainComplexMap_comp, homologyMap_comp]
  have : IsIso (homologyMap (TopPair.cubicalChainComplexMap k
      ((fiberFirst e).preimagePairMap (Cube.boundary (Fin (m + 1))))) n) := by
    rw [← FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_hom]
    infer_instance
  infer_instance

/-- **The relative homology of a space fibre homotopy trivial over a cube**: a fibre homotopy
equivalence `e` over `Iᵐ⁺¹` from `Iᵐ⁺¹ × F` to `Y` gives an isomorphism
`H_q(F; k) ≃ₗ[k] H_{q+m+1}(Y, π⁻¹ ∂Iᵐ⁺¹; k)`, `[z] ↦ [e_*(z × [Iᵐ⁺¹])]`
(`TauCeti.FiberHomotopyEquiv.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`), over
every commutative ring `k`. -/
def cubicalHomologyCubeBoundaryEquiv (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of F)).homology q ≃ₗ[k]
      ((TopPair.ofSubset (X := TopCat.of Y)
        (π ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology (q + (m + 1)) :=
  have := isIso_homologyMap_cubeBoundaryPairMap e k (q + (m + 1))
  cubicalHomologyCubeBoundaryPairProdLeftEquiv k (TopCat.of F) m q ≪≫ₗ
    (asIso (homologyMap (TopPair.cubicalChainComplexMap k (cubeBoundaryPairMap e))
      (q + (m + 1)))).toLinearEquiv

include e in
/-- **The relative homology of a space fibre homotopy trivial over a cube vanishes below the
dimension of the cube**: if `Y` is fibre homotopy equivalent over `Iᵐ⁺¹` to a product
`Iᵐ⁺¹ × F`, then `Hⱼ(Y, π⁻¹ ∂Iᵐ⁺¹; k) = 0` for `j < m + 1`, over every commutative ring `k`. -/
theorem isZero_cubicalHomology_of_lt {j : ℕ} (hj : j < m + 1) :
    IsZero (((TopPair.ofSubset (X := TopCat.of Y)
      (π ⁻¹' Cube.boundary (Fin (m + 1)))).cubicalChainComplex k).homology j) :=
  have := isIso_homologyMap_cubeBoundaryPairMap e k j
  (isZero_cubicalHomology_cubeBoundaryPair_prodLeft_of_lt k (TopCat.of F) m hj).of_iso
    (asIso (homologyMap (TopPair.cubicalChainComplexMap k (cubeBoundaryPairMap e)) j)).symm

/-- On chains, the map of pairs sends the cross product of a chain `a` of `F` with the identity
cube of the cube model to `e_*(a × [Iᵐ⁺¹])`. -/
private theorem map_crossProduct_upCube {q : ℕ} (a : NormalizedCubicalChain F k q) :
    NormalizedCubicalChain.map k (TopPair.Hom.fst (cubeBoundaryPairMap e)).hom (q + (m + 1))
        (NormalizedCubicalChain.crossProduct F (ULift.{0} (Fin (m + 1) → I)) k
          q (m + 1) a (NormalizedCubicalChain.ofCube _ k (upCube.{0} (m + 1)))) =
      NormalizedCubicalChain.map k (e.toFun.comp ContinuousMap.prodSwap) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct F (Fin (m + 1) → I) k q (m + 1) a
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
  rw [hc, hx, ← LinearMap.comp_apply
    (NormalizedCubicalChain.map k (e.toFun.comp ContinuousMap.prodSwap) _),
    ← NormalizedCubicalChain.map_comp]
  exact congrArg (fun φ ↦ NormalizedCubicalChain.map k φ (q + (m + 1)) _)
    (cubeBoundaryPairMap_fst e)

/-- **The isomorphism `H_q(F) ≃ H_{q+m+1}(Y, π⁻¹ ∂Iᵐ⁺¹)` is `e_*(· × [Iᵐ⁺¹])`**: for a `q`-cycle
`z` of `F`, the chain `e_*(z × [Iᵐ⁺¹])`, the push-forward along `e` (with the factors interchanged)
of the cross product of `z` with the identity cube, is a relative cycle representing the image of
the class of `z`. -/
theorem isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of F)).cycles q) :
    (TopPair.ofSubset (X := TopCat.of Y)
        (π ⁻¹' Cube.boundary (Fin (m + 1)))).IsCubicalRepresentative k
      (NormalizedCubicalChain.map k (e.toFun.comp ContinuousMap.prodSwap) (q + (m + 1))
        (NormalizedCubicalChain.crossProduct F (Fin (m + 1) → I) k q (m + 1)
          (normalizedCubicalChainComplexXEquiv _ q
            (((normalizedCubicalChainComplex k).obj (TopCat.of F)).iCycles q z))
          (NormalizedCubicalChain.ofCube _ k (ContinuousMap.id _))))
      (cubicalHomologyCubeBoundaryEquiv e k q
        (((normalizedCubicalChainComplex k).obj (TopCat.of F)).homologyπ q z)) := by
  -- The representing relative cycle is the image of `z × [Iᵐ⁺¹]` under the map of pairs.
  refine (TopPair.isCubicalRepresentative_iff _ _).2
    ⟨(cyclesMap (TopPair.cubicalChainComplexMap k (cubeBoundaryPairMap e)) _).hom
    ((cyclesMap (cubicalCrossProductRel k _ (cubeBoundaryPair.{0} (m + 1))) (q + (m + 1))).hom
      ((cyclesCross ((normalizedCubicalChainComplex k).obj (TopCat.of F))
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
    exact (map_crossProduct_upCube e k _).symm.trans
      (congrArg _ (NormalizedCubicalChain.cast_rfl k _).symm)
  · rw [cubicalHomologyCubeBoundaryEquiv, LinearEquiv.trans_apply,
      cubicalHomologyCubeBoundaryPairProdLeftEquiv_homologyπ, Iso.toLinearEquiv_apply, asIso_hom,
      ← ModuleCat.comp_apply, ← homologyπ_naturality, ModuleCat.comp_apply]

end TauCeti.FiberHomotopyEquiv
