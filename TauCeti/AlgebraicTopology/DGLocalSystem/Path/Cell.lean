/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Pullback
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Kunneth
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule

/-!
# The relative homology of the based path fibration over a cube

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

## Main definitions

* `TauCeti.MoorePathPullback.sectionCube τ h₀ h₁`: the singular cube `d ↦ (d, τ d)` of the
  pullback.
* `TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q`: the isomorphism
  `H_q(Ω_b X; k) ≃ₗ[k] H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}; k)`.

## Main results

* `TauCeti.MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv`: for a
  cycle `z` of `Ω_b X`, the chain `z · c₀` represents the image of `[z]`.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
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
