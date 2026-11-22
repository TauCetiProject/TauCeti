/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Cell
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Cycles

/-!
# The Wang map of a cell is multiplication by its boundary loops

Let `f : Iᵐ⁺¹ → X` be a map from a cube sending the boundary of the cube to a point `b`, and `τ` a
continuous family of Moore paths, `τ d` from `b` to `f d`. Over the boundary of the cube the paths
`τ d` are loops at `b`, so the boundary of the cube of paths `d ↦ τ d` is a cycle `y` of the Moore
loops at `b`, of degree `m` (`TauCeti.MoorePathPullback.boundaryLoopCycle`).

The **Wang map** (`TauCeti.MoorePathPullback.wangMap`) is the composite

`H_q(Ω_b X) ≅ H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}) ⟶ H_{q+m+1}(P_b X, Ω_b X) ⟶ H_{q+m}(Ω_b X)`

of the computation of the relative homology of the pulled-back based path fibration over the cube
(`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv`), the map induced by the projection
of the pullback to the based path space `P_b X`, and the connecting morphism of the pair
`(P_b X, Ω_b X)`, where the Moore loops sit in `P_b X` as the fibre of the end point over `b`. This
file computes it: it is right Pontryagin multiplication by `y`, up to the sign `(-1) ^ q`,
`[z] ↦ (-1) ^ q [z · y]` (`TauCeti.MoorePathPullback.wangMap_homologyπ`). The class of `z` is
represented by the chain `z · c₀` of the pullback, `c₀` the section cube; its image in `P_b X` is
`z · c`, `c` the cube of paths, and the boundary of `z · c` is `(-1) ^ q z · ∂ c`, the product of
`z` with `y` read in the fibre.

The based path space is contractible, so the connecting morphism is an isomorphism in positive
degrees (`TopPair.isIso_cubicalHomologyδ_of_contractibleSpace_of_ne_zero`). So whenever the
projection of the pullback induces isomorphisms of relative homology, for instance when `f` is the
characteristic map of the top cell of a sphere, the Wang map is bijective
(`TauCeti.MoorePathPullback.bijective_wangMap`): right multiplication by `y` is an isomorphism
`H_q(Ω_b X) ≅ H_{q+m}(Ω_b X)`. For a sphere this is the input of the computation of the Pontryagin
ring of its loop space.

## Main definitions

* `TauCeti.pathFromLoopPair X b`: the pair `(P_b X, Ω_b X)`.
* `TauCeti.MoorePathPullback.toPathFromLoopPair`: the projection of the pullback, as a map of pairs.
* `TauCeti.MoorePathPullback.boundaryLoopCycle`: the cycle `y` of boundary loops.
* `TauCeti.MoorePathPullback.wangMap`: the Wang map `H_q(Ω_b X) → H_{q+m}(Ω_b X)`.

## Main results

* `TauCeti.MoorePathPullback.wangMap_homologyπ`: the Wang map is `[z] ↦ (-1) ^ q [z · y]`.
* `TauCeti.MoorePathPullback.bijective_wangMap`: it is bijective when the projection of the
  pullback induces isomorphisms of relative homology.

## References

* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* R. Bott, H. Samelson, *On the Pontryagin product in spaces of paths*, Comment. Math. Helv. 27
  (1953), 320–337.
* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Limits Topology
open scoped unitInterval

namespace TauCeti

variable (X : Type) [TopologicalSpace X] (b : X)

/-- The pair `(P_b X, Ω_b X)` of the based Moore path space and the Moore loop space at `b`, the
fibre of the end point map over `b`. -/
abbrev pathFromLoopPair : TopPair.{0} where
  left := TopCat.of (MooreLoopSpace X b)
  right := TopCat.of (MoorePathFrom X b)
  hom := TopCat.ofHom MooreLoopSpace.toMoorePathFrom
  prop := MooreLoopSpace.isEmbedding_toMoorePathFrom

namespace MoorePathPullback

variable {X b} {m : ℕ} {f : C(Fin (m + 1) → I, X)}
  (hf : ∀ d ∈ Cube.boundary (Fin (m + 1)), f d = b)

/-- A point of the pullback over the boundary of the cube has its parameter in the boundary. -/
theorem point_mem_boundary (x : proj f b ⁻¹' Cube.boundary (Fin (m + 1))) :
    x.val.point ∈ Cube.boundary (Fin (m + 1)) := by
  have h := x.property
  rwa [Set.mem_preimage, proj_apply] at h

/-- Over the boundary of the cube, where `f` takes the value `b`, the paths of the pullback are
loops at `b`. -/
def boundaryLoop : C(proj f b ⁻¹' Cube.boundary (Fin (m + 1)), MooreLoopSpace X b) :=
  ⟨fun x ↦ ⟨x.val.path, x.val.source_path, (x.val.target_path).trans (hf _ (point_mem_boundary x))⟩,
    continuous_induced_rng.2 (continuous_path.comp continuous_subtypeVal)⟩

@[simp]
theorem toMoorePath_boundaryLoop (x : proj f b ⁻¹' Cube.boundary (Fin (m + 1))) :
    (boundaryLoop hf x).toMoorePath = x.val.path := (rfl)

/-- The projection of the pullback to the based path space, as a map of pairs
`(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}) ⟶ (P_b X, Ω_b X)`. -/
def toPathFromLoopPair :
    TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
        (proj f b ⁻¹' Cube.boundary (Fin (m + 1))) ⟶ pathFromLoopPair X b :=
  TopPair.ofHom (TopCat.ofHom toMoorePathFrom) (TopCat.ofHom (boundaryLoop hf)) (by
    ext x : 1
    exact MoorePathFrom.ext ((MooreLoopSpace.toMoorePath_toMoorePathFrom _).trans
      ((toMoorePath_boundaryLoop hf x).trans (toMoorePathFrom_toMoorePath x.val).symm)))

/-- The map of pairs `toPathFromLoopPair` is `toMoorePathFrom` on the ambient spaces. -/
@[simp]
theorem fst_toPathFromLoopPair_apply (x : MoorePathPullback f b) :
    TopPair.Hom.fst (toPathFromLoopPair hf) x = toMoorePathFrom x :=
  (rfl)

variable (τ : C(Fin (m + 1) → I, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
  (h₁ : ∀ d, (τ d).target = f d) (k : Type) [CommRing k]

/-- The cube `d ↦ τ d` of Moore paths from `b`, the image in `P_b X` of the section cube of the
pullback. -/
def pathCube : SingularCube (MoorePathFrom X b) (m + 1) :=
  toMoorePathFrom.comp (sectionCube τ h₀ h₁)

@[simp]
theorem toMoorePath_pathCube (d : Fin (m + 1) → I) :
    (pathCube τ h₀ h₁ d).toMoorePath = τ d := by
  simp [pathCube]

include hf in
/-- Over the boundary of the cube the paths `τ d` are loops. -/
theorem mapsTo_pathCube :
    Set.MapsTo (pathCube τ h₀ h₁) (Cube.boundary (Fin (m + 1)))
      (Set.range (pathFromLoopPair X b).map) := fun d hd ↦
  MooreLoopSpace.range_toMoorePathFrom.ge <| (MoorePathFrom.endpoint_apply _).trans <|
    (congrArg MoorePath.target (toMoorePath_pathCube τ h₀ h₁ d)).trans ((h₁ d).trans (hf d hd))

/-- The cycle of Moore loops at `b` swept out by the boundary of the cube of paths `τ`. -/
def boundaryLoopCycle :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).cycles m :=
  TopPair.cubicalBoundaryCycleOfCube k (P := pathFromLoopPair X b) (pathCube τ h₀ h₁)
    (mapsTo_pathCube hf τ h₀ h₁)

/-- The underlying chain of the cycle of boundary loops is the boundary of the cube of paths, read
in the loops. -/
@[simp]
theorem iCycles_boundaryLoopCycle :
    (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).iCycles m).hom
        (boundaryLoopCycle hf τ h₀ h₁ k) =
      TopPair.cubicalBoundaryChainOfCube k (P := pathFromLoopPair X b) (pathCube τ h₀ h₁)
        (mapsTo_pathCube hf τ h₀ h₁) :=
  TopPair.iCycles_cubicalBoundaryCycleOfCube k (P := pathFromLoopPair X b) _ _

/-- The **Wang map** `H_q(Ω_b X) → H_{q+m}(Ω_b X)` of the cube: the isomorphism
`H_q(Ω_b X) ≅ H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹})`, the map to `H_{q+m+1}(P_b X, Ω_b X)` and the
connecting morphism of the pair `(P_b X, Ω_b X)`. -/
def wangMap (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homology q →ₗ[k]
      ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homology
        (q + m) :=
  ((pathFromLoopPair X b).cubicalHomologyδ k (q + (m + 1)) (q + m)).hom ∘ₗ
    (homologyMap (TopPair.cubicalChainComplexMap k (toPathFromLoopPair hf)) (q + (m + 1))).hom ∘ₗ
      (cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q).toLinearMap

/-- The projection of the pullback carries `z · c₀`, the action of a chain `z` of loops on the
section cube, to `z · c`, its action on the cube of paths. -/
private theorem map_leftAct_sectionCube {q : ℕ}
    (z : NormalizedCubicalChain (MooreLoopSpace X b) k q) :
    NormalizedCubicalChain.map k toMoorePathFrom (q + (m + 1))
        (NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathPullback f b) k q (m + 1) z
          (NormalizedCubicalChain.ofCube _ k (sectionCube τ h₀ h₁))) =
      NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathFrom X b) k q (m + 1) z
        (NormalizedCubicalChain.ofCube _ k (pathCube τ h₀ h₁)) :=
  (NormalizedCubicalChain.map_leftAct toMoorePathFrom (fun ω x ↦ toMoorePathFrom_leftAct ω x) _
    _).trans (congrArg _ (NormalizedCubicalChain.map_ofCube _ _ _))

/-- Reading loops as paths carries the product of a chain `z` of loops with the boundary of the
cube of paths, read in the loops, to the action of `z` on the boundary of the cube of paths. -/
private theorem map_mul_cubicalBoundaryChainOfCube {q : ℕ}
    (z : NormalizedCubicalChain (MooreLoopSpace X b) k q) :
    NormalizedCubicalChain.map k MooreLoopSpace.toMoorePathFrom (q + m)
        (NormalizedCubicalChain.mul (MooreLoopSpace X b) k q m z
          (TopPair.cubicalBoundaryChainOfCube k (P := pathFromLoopPair X b) (pathCube τ h₀ h₁)
            (mapsTo_pathCube hf τ h₀ h₁))) =
      NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathFrom X b) k q m z
        (NormalizedCubicalChain.boundary (MoorePathFrom X b) k m
          (NormalizedCubicalChain.ofCube _ k (pathCube τ h₀ h₁))) := by
  refine (congrArg _ (NormalizedCubicalChain.leftAct_eq_mul (G := MooreLoopSpace X b) _
    _).symm).trans ?_
  refine (NormalizedCubicalChain.map_leftAct _ (fun ω ω' ↦ by
    rw [smul_eq_mul]; exact MooreLoopSpace.toMoorePathFrom_mul ω ω') _ _).trans ?_
  exact congrArg _ (TopPair.map_cubicalBoundaryChainOfCube k (P := pathFromLoopPair X b) _ _)

/-- The product of a cycle of loops with the cycle of boundary loops is the product of chains. -/
private theorem iCycles_mulCycles_boundaryLoopCycle {q : ℕ}
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).cycles q) :
    (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).iCycles
        (q + m)).hom (NormalizedCubicalChain.mulCycles k z (boundaryLoopCycle hf τ h₀ h₁ k)) =
      (normalizedCubicalChainComplexXEquiv _ (q + m)).symm
        (NormalizedCubicalChain.mul (MooreLoopSpace X b) k q m
          (normalizedCubicalChainComplexXEquiv _ q
            ((((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).iCycles
              q).hom z))
          (TopPair.cubicalBoundaryChainOfCube k (P := pathFromLoopPair X b) (pathCube τ h₀ h₁)
            (mapsTo_pathCube hf τ h₀ h₁))) := by
  rw [NormalizedCubicalChain.iCycles_mulCycles, iCycles_boundaryLoopCycle]
  -- the identification `normalizedCubicalChainComplexXEquiv` of degree `m` is the identity
  -- (`normalizedCubicalChainComplexXEquiv_apply`), which `rw` cannot use here because the boundary
  -- chain is typed as a chain of `(pathFromLoopPair X b).snd`
  rfl

/-- **The Wang map is right multiplication by the boundary loops**: it sends the class of a cycle
`z` of degree `q` to `(-1) ^ q` times the class of `z · y`, `y` the cycle `boundaryLoopCycle`. -/
theorem wangMap_homologyπ (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).cycles q) :
    wangMap hf τ h₀ h₁ k q
        ((((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).homologyπ q).hom
          z) =
      (-1 : k) ^ q • (((normalizedCubicalChainComplex k).obj
        (TopCat.of (MooreLoopSpace X b))).homologyπ (q + m)).hom
          (NormalizedCubicalChain.mulCycles k z (boundaryLoopCycle hf τ h₀ h₁ k)) := by
  obtain ⟨r, hr, hrz⟩ := (TopPair.isCubicalRepresentative_iff _ _).1
    (isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv τ h₀ h₁ k q z)
  -- the image of `[z]` in `H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹})` is the class of `r`, and its
  -- image in `H_{q+m+1}(P_b X, Ω_b X)` is the class of the image of `r`
  rw [wangMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hrz,
    ← ModuleCat.comp_apply (homologyπ _ _), homologyπ_naturality, ModuleCat.comp_apply, ← map_smul,
    TopPair.cubicalHomologyδ_def k (pathFromLoopPair X b) (q + (m + 1)) (q + m)]
  refine (TopPair.shortExact_cubicalChainComplexShortComplex k
    (pathFromLoopPair X b)).moduleCat_δ_homologyπ (q + (m + 1)) (q + m) rfl _
    ((normalizedCubicalChainComplexXEquiv _ _).symm
      (NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathFrom X b) k q (m + 1)
        (normalizedCubicalChainComplexXEquiv _ q
          ((((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace X b))).iCycles
            q).hom z))
        (NormalizedCubicalChain.ofCube _ k (pathCube τ h₀ h₁)))) ?_ _ ?_
  · rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, ← hr]
    exact Eq.symm <| (TopPair.π_cubicalChainComplexMap_f_apply k _ _ _).trans
      (congrArg _ (map_leftAct_sectionCube τ h₀ h₁ k _))
  · refine Eq.trans ?_ (NormalizedCubicalChain.d_leftAct_of_d_eq_zero _
      (fun j ↦ HomologicalComplex.moduleCat_d_iCycles_apply _ _ j z) _).symm
    -- the boundary of `z · c` is `(-1) ^ q • z · ∂ c`, and `∂ c` is the cycle `y` read in `P_b X`
    refine (normalizedCubicalChainComplex_map_f_apply _ _ _).trans ?_
    refine (congrArg (NormalizedCubicalChain.map k _ (q + m)) ((map_smul _ _ _).trans
      (congrArg _ (iCycles_mulCycles_boundaryLoopCycle hf τ h₀ h₁ k z)))).trans ?_
    rw [map_smul]
    exact (map_smul _ _ _).trans (congrArg _ (map_mul_cubicalBoundaryChainOfCube hf τ h₀ h₁ k _))

/-- **The Wang map is bijective** in every degree `q` with `q + m ≥ 1` in which the projection of
the pullback induces an isomorphism
`H_{q+m+1}(f^*P_b X, f^*P_b X|_{∂Iᵐ⁺¹}) ≅ H_{q+m+1}(P_b X, Ω_b X)`, for instance when `f` is the
characteristic map of the top cell of a sphere. -/
theorem bijective_wangMap (q : ℕ)
    (hg : IsIso (homologyMap (TopPair.cubicalChainComplexMap k (toPathFromLoopPair hf))
      (q + (m + 1)))) (hqm : q + m ≠ 0) :
    Function.Bijective (wangMap hf τ h₀ h₁ k q) := by
  -- the based path space is contractible, so the connecting morphism is an isomorphism
  have : ContractibleSpace (pathFromLoopPair X b).fst :=
    inferInstanceAs (ContractibleSpace (MoorePathFrom X b))
  have := TopPair.isIso_cubicalHomologyδ_of_contractibleSpace_of_ne_zero k (pathFromLoopPair X b)
    (n := q + (m + 1)) rfl hqm
  rw [wangMap, LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (ConcreteCategory.bijective_of_isIso
    ((pathFromLoopPair X b).cubicalHomologyδ k (q + (m + 1)) (q + m) rfl)).comp
      ((ConcreteCategory.bijective_of_isIso _).comp (LinearEquiv.bijective _))

end MoorePathPullback

end TauCeti
