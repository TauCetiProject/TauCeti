/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Geometry.Lie.UniversalCover.FiniteCover
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
import Mathlib.Topology.Separation.Connected
import TauCeti.AlgebraicTopology.EilenbergMacLane.QuotientProd
import TauCeti.Geometry.Lie.ThirdHomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Higher homotopy groups of a compact connected Lie group through its semisimple factor

Let `G` be a compact connected Lie group, `U` its universal covering group with covering
projection `π`, `𝔷` the centre of its Lie algebra and `K` the compact simply connected subgroup of
`U` integrating the derived algebra, so that `G` is the quotient `(𝔷 × K) ⧸ Γ` of `𝔷 × K` by a
discrete central subgroup (`TauCeti.UniversalCover.quotientKerCenterProdDerivedProjHom`).

Since `𝔷` is contractible and `𝔷 × K → G` is a covering map, the map `k ↦ π(k)` from `K` to `G`
(`TauCeti.UniversalCover.derivedFactorMap`) induces a bijection on every homotopy group of
dimension at least two (`TauCeti.UniversalCover.bijective_homotopyGroupMap_derivedFactorMap`). So
the higher homotopy of `G` is that of `K`.

The group `K` is a compact connected Lie group with finite centre. If it is nontrivial, it is
therefore not commutative, and its third homotopy group is nontrivial
(`TauCeti.UniversalCover.nontrivial_homotopyGroup_three_derivedFactor`): the Cartan three-form of
its Killing form detects a homomorphism from `Spin(3) ≅ S³` into `K`
(`TauCeti.Lie.nontrivial_homotopyGroup_three_of_not_isMulCommutative`). Hence `π₃(G)` is
nontrivial exactly when `K` is nontrivial
(`TauCeti.UniversalCover.nontrivial_homotopyGroup_three_iff_nontrivial_derivedFactor`).

For instance, for `G = U(n)` the factor `K` is `SU(n)`, and for a torus `K` is trivial.

## Main definitions

* `TauCeti.UniversalCover.derivedFactorMap`: the continuous homomorphism `K → G`, `k ↦ π(k)`.

## Main results

* `TauCeti.UniversalCover.bijective_homotopyGroupMap_derivedFactorMap`: `K → G` is bijective on
  `π_(n + 2)`.
* `TauCeti.UniversalCover.nontrivial_homotopyGroup_three_derivedFactor`: `π₃(K) ≠ 0` for
  nontrivial `K`.
* `TauCeti.UniversalCover.nontrivial_homotopyGroup_three_iff_nontrivial_derivedFactor`:
  `π₃(G) ≠ 0` exactly when `K` is nontrivial.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, Theorem 8.1.
* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.31).
-/

public section

open Function LieAlgebra
open scoped ContDiff Manifold Topology Topology.Homotopy

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti.UniversalCover

attribute [local instance] Lie.ImmersedLieSubgroupData.group
  Lie.ImmersedLieSubgroupData.topologicalSpace Lie.ImmersedLieSubgroupData.normedAddCommGroup
  Lie.ImmersedLieSubgroupData.normedSpace Lie.ImmersedLieSubgroupData.finiteDimensional
  Lie.ImmersedLieSubgroupData.modelTopology Lie.ImmersedLieSubgroupData.chartedSpace
  Lie.ImmersedLieSubgroupData.lieGroup Lie.ImmersedLieSubgroupData.connectedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsTopologicalGroup G] [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  [T2Space G] [SecondCountableTopology G] [CompactSpace G]

/-- The continuous homomorphism `K → G`, `k ↦ π(k)`, from the subgroup `K` of the universal
covering group integrating the derived algebra: the restriction of the covering homomorphism
`𝔷 × K → G` (`TauCeti.UniversalCover.centerProdDerivedProjHom`) to `{0} × K`. -/
noncomputable def derivedFactorMap : derivedFactor I G →ₜ* G where
  toMonoidHom := (centerProdDerivedProjHom I G).comp (MonoidHom.inr _ _)
  continuous_toFun :=
    (continuous_centerProdDerivedProjHom I G).comp (continuous_const.prodMk continuous_id)

@[simp]
theorem derivedFactorMap_apply (k : derivedFactor I G) :
    derivedFactorMap I G k = centerProdDerivedProjHom I G (1, k) :=
  (rfl)

variable [ConnectedSpace G]

/-- **The higher homotopy groups of a compact connected Lie group are those of `K`.** The map
`k ↦ π(k)` from the subgroup `K` of the universal covering group integrating the derived algebra
induces a bijection `π_(n + 2)(K, k) → π_(n + 2)(G, π(k))`. -/
theorem bijective_homotopyGroupMap_derivedFactorMap (k : derivedFactor I G) (n : ℕ) :
    Bijective (HomotopyGroup.map (N := Fin (n + 2)) (derivedFactorMap I G : C(_, G)) rfl :
      π_ (n + 2) (derivedFactor I G) k → π_ (n + 2) G (derivedFactorMap I G k)) := by
  have : ContractibleSpace (Multiplicative (centerFactor I G)) :=
    inferInstanceAs (ContractibleSpace (centerFactor I G))
  -- `k ↦ π(k)` is `k ↦ [(1, k)]` followed by the identification `(𝔷 × K) ⧸ Γ ≃ₜ G`.
  let e := (quotientKerCenterProdDerivedProjHom I G).toHomeomorph
  let q : C(derivedFactor I G, (Multiplicative (centerFactor I G) × derivedFactor I G) ⧸
      (centerProdDerivedProjHom I G).ker) :=
    ⟨fun k ↦ (((1 : Multiplicative (centerFactor I G)), k) : _ ⧸ _), by fun_prop⟩
  have heq : (e : C(_, G)).comp q = derivedFactorMap I G := by
    ext k
    exact quotientKerCenterProdDerivedProjHom_apply_mk I G (1, k)
  -- Split `HomotopyGroup.map` along this factorisation.
  rw [← HomotopyGroup.map_comp_map_of_comp_eq heq (DFunLike.congr_fun heq k) rfl]
  exact (HomotopyGroup.homeomorphEquivOfEq e (DFunLike.congr_fun heq k)).bijective.comp
    ((centerProdDerivedProjHom I G).ker.bijective_homotopyGroupMap_quotientMk_inr k n)

omit [T2Space G] in
/-- **The semisimple factor `K` has nontrivial third homotopy group** as soon as it is
nontrivial, at every base point. -/
theorem nontrivial_homotopyGroup_three_derivedFactor [Nontrivial (derivedFactor I G)]
    (k : derivedFactor I G) : Nontrivial (π_ 3 (derivedFactor I G) k) := by
  let S := (derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
    LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))))
  refine Lie.nontrivial_homotopyGroup_three_of_not_isMulCommutative
    (J := (S.integralLeafSubgroupData (I := I)).I') (fun hK ↦ ?_) k
  -- A commutative `K` is its own centre, which is finite, and a finite connected Hausdorff space
  -- is a point.
  have : T2Space (derivedFactor I G) :=
    (S.integralLeafSubgroupData (I := I)).I'.t2Space_of_lieGroup ∞
  have : Finite (derivedFactor I G) :=
    Finite.of_surjective (fun z : Subgroup.center (derivedFactor I G) ↦ (z : derivedFactor I G))
      fun k ↦ ⟨⟨k, Subgroup.mem_center_iff.2 fun g ↦ hK.is_comm.comm g k⟩, rfl⟩
  exact not_subsingleton (derivedFactor I G) PreconnectedSpace.trivial_of_discrete

/-- **A compact connected Lie group has nontrivial third homotopy group exactly when its
semisimple factor `K` is nontrivial**, at every base point. -/
theorem nontrivial_homotopyGroup_three_iff_nontrivial_derivedFactor (g : G) :
    Nontrivial (π_ 3 G g) ↔ Nontrivial (derivedFactor I G) := by
  -- `π₃(G, g)` is `π₃(G, 1)`, by left translation, hence `π₃(K, 1)`.
  let eG : π_ 3 G (derivedFactorMap I G 1) ≃ π_ 3 G g :=
    HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (by simp)
  let e : π_ 3 (derivedFactor I G) 1 ≃ π_ 3 G g :=
    (Equiv.ofBijective _ (bijective_homotopyGroupMap_derivedFactorMap I G 1 1)).trans eG
  refine ⟨fun h ↦ ?_, fun h ↦
    have := nontrivial_homotopyGroup_three_derivedFactor I G 1
    e.symm.nontrivial⟩
  by_contra hK
  have : Subsingleton (derivedFactor I G) := not_nontrivial_iff_subsingleton.1 hK
  exact not_subsingleton (π_ 3 G g) e.symm.subsingleton

end TauCeti.UniversalCover
