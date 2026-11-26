/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LieAlgebra
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Classification
import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Lie.Adjoint.Compact
import TauCeti.Geometry.Lie.CartanThreeForm
import TauCeti.Geometry.Lie.Exponential.Commute
import TauCeti.Geometry.Lie.Integration
import TauCeti.Geometry.Lie.ModelTransport
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SimplyConnected
import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# The third homotopy group of a compact Lie group

A compact Lie group `G` whose Lie algebra is not abelian has nontrivial third homotopy group
(`TauCeti.Lie.nontrivial_homotopyGroup_three`). Consequently a compact connected Lie group with
trivial third homotopy group is a torus
(`TauCeti.Lie.nonempty_continuousMulEquiv_pi_circle_of_subsingleton_homotopyGroup_three`).

The nontrivial class is represented by a homomorphism out of `Spin(3) ≅ S³`.

* The Lie algebra of `G` contains a copy of `so(3)` as soon as it is not abelian
  (`TauCeti.Lie.exists_injective_lieHom_soThree_of_compactSpace`), and `so(3)` is the Lie algebra
  of `Spin(3)` (`TauCeti.CliffordAlgebra.realSpinLieEquivSo`). Since `Spin(3)` is simply
  connected, the inclusion integrates to a smooth homomorphism `φ : Spin(3) → G` with injective
  differential (`LieHom.integrate`).
* Take `y, z` in the Lie algebra of `Spin(3)` with `x = ⁅y, z⁆ ≠ 0`. Then `dφ x` is a nonzero
  element of the derived algebra of the Lie algebra of `G`, which meets the centre only in `0`,
  so the Killing form `B` of `G` takes a nonzero (negative) value at `dφ x`. Hence the Cartan
  three-form `B(·, ⁅·, ·⁆)` pulls back along `φ` to a nonzero top form, and `φ` is not
  null-homotopic (`ContMDiffMonoidMorphism.not_nullhomotopic_of_lie_eq_of_apply_ne_zero`).
* `Spin(3)` is homeomorphic to the unit sphere `S³` of `ℝ⁴`, so `φ` gives a map `S³ → G`, based
  at any chosen `g ∈ G` after a left translation, which is not null-homotopic. Its class in
  `π₃(G, g)` is therefore nontrivial (`HomotopyGroup.nontrivial_of_not_nullhomotopic`).

The integration step asks the model of `G` to be boundaryless and to live in the lowest universe,
as `LieHom.integrate` does.

Conversely, if `π₃(G, g)` is trivial, the Lie algebra of `G` is abelian, so for connected `G`
the group itself is commutative (`ContMDiffMonoidMorphism.commute_of_lie_lieMap_eq_zero`), hence
a product of circles (`TauCeti.nonempty_continuousMulEquiv_pi_circle`).

## Main results

* `TauCeti.Lie.exists_contMDiffMonoidMorphism_realSpinThree_not_nullhomotopic`: a compact Lie
  group with non-abelian Lie algebra receives a smooth homomorphism from `Spin(3)` with injective
  differential which is not null-homotopic.
* `TauCeti.Lie.nontrivial_homotopyGroup_three`: such a group has nontrivial `π₃`.
* `TauCeti.Lie.nontrivial_homotopyGroup_three_of_not_isMulCommutative`: so has a noncommutative
  compact connected Lie group, for any model with corners.
* `TauCeti.Lie.nonempty_continuousMulEquiv_pi_circle_of_subsingleton_homotopyGroup_three`: a
  compact connected Lie group with trivial `π₃` is a torus.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, proof of Proposition 6.31.
* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, §§8 and 12.
-/

public section

open scoped ContDiff Manifold
open LieAlgebra Metric TauCeti.CliffordAlgebra _root_.CliffordAlgebra

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G]

/-- In the Lie algebra of compact `Spin(3)`, some bracket is nonzero. -/
private theorem exists_lie_ne_zero_realSpinThree :
    ∃ y z : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel 3) (spinGroup (realCliffordForm 3 0)),
      ⁅y, z⁆ ≠ 0 := by
  let e := realSpinLieEquivSo 3
  refine ⟨e.symm (soThreeEquiv ℝ (Pi.single 1 1)), e.symm (soThreeEquiv ℝ (Pi.single 2 1)), ?_⟩
  rw [← LieEquiv.map_lie, lie_soThreeEquiv]
  refine e.symm.toLinearEquiv.map_ne_zero_iff.2 ((soThreeEquiv ℝ).map_ne_zero_iff.2 fun h ↦ ?_)
  simpa [cross_apply] using congrFun h 0

/-- **A compact Lie group with non-abelian Lie algebra receives an essential homomorphism from
`Spin(3)`.** It is a smooth homomorphism with injective differential which is not
null-homotopic. -/
theorem exists_contMDiffMonoidMorphism_realSpinThree_not_nullhomotopic
    (hG : ¬IsLieAbelian (LeftInvariantDerivation I G)) :
    ∃ φ : ContMDiffMonoidMorphism 𝓘(ℝ, realSpinLieModel 3) I ∞
        (spinGroup (realCliffordForm 3 0)) G,
      Function.Injective (lieMap φ) ∧
        ¬(φ : C(spinGroup (realCliffordForm 3 0), G)).Nullhomotopic := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology G := ChartedSpace.secondCountable_of_sigmaCompact H G
  have : SecondCountableTopology (spinGroup (realCliffordForm 3 0)) :=
    have := (𝓘(ℝ, realSpinLieModel 3)).secondCountableTopology
    ChartedSpace.secondCountable_of_sigmaCompact (realSpinLieModel 3) _
  have : SimplyConnectedSpace (spinGroup (realCliffordForm 3 0)) :=
    simplyConnectedSpace_realCliffordSpinGroupZero_three
  obtain ⟨f, hf⟩ := exists_injective_lieHom_soThree_of_compactSpace hG
  let φ := (f.comp (realSpinLieEquivSo 3).toLieHom).integrate
  have hφ : Function.Injective (lieMap φ) := by
    rw [LieHom.lieMap_integrate]
    exact hf.comp (realSpinLieEquivSo 3).injective
  refine ⟨φ, hφ, ?_⟩
  let eS := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, realSpinLieModel 3)) (n := ∞) (by simp)
      (1 : spinGroup (realCliffordForm 3 0)))
  let eG := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have hκ : ∀ x y z : LeftInvariantDerivation I G,
      killingForm ℝ _ ⁅x, y⁆ z = -killingForm ℝ _ y ⁅x, z⁆ :=
    LieModule.traceForm_apply_lie_apply' ℝ _ _
  obtain ⟨y, z, hyz⟩ := exists_lie_ne_zero_realSpinThree
  refine φ.not_nullhomotopic_of_lie_eq_of_apply_ne_zero ?_
    ((killingForm ℝ _).compl₁₂ eG.symm.toLinearMap eG.symm.toLinearMap)
    (LinearMap.BilinMap.compl₁₂_lieInvariant hκ eG.symm.toLieHom)
    (x := eS ⁅y, z⁆) (y := eS y) (z := eS z) (eS.map_lie y z).symm ?_
  · rw [← finrank_leftInvariantDerivation_eq_modelVectorSpace
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, realSpinLieModel 3)) (n := ∞) (by simp)
        (1 : spinGroup (realCliffordForm 3 0))),
      (realSpinLieEquivSo 3).toLinearEquiv.finrank_eq, finrank_so_three]
  · -- The differential of `φ` at the identity is `lieMap φ`, read through `eS` and `eG`.
    have hd : eG.symm (φ.toMonoidHom.groupLieAlgebraMap _ I (eS ⁅y, z⁆)) = lieMap φ ⁅y, z⁆ :=
      leftInvariantDerivationLieEquivGroupLieAlgebra_symm_groupLieAlgebraMap φ ⁅y, z⁆
    simp only [LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, hd]
    rw [ne_eq, LeftInvariantDerivation.killingForm_self_eq_zero_iff]
    intro hc
    -- `dφ ⁅y, z⁆` is central and in the derived algebra, hence zero.
    have hder : lieMap φ ⁅y, z⁆ ∈ derivedSeries ℝ (LeftInvariantDerivation I G) 1 := by
      rw [LieHom.map_lie]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    have h0 := (isCompl_center_derivedSeries_one_of_compactSpace (I := I) (G := G)).inf_eq_bot
    have : lieMap φ ⁅y, z⁆ = 0 := by
      rw [← LieSubmodule.mem_bot (R := ℝ) (L := LeftInvariantDerivation I G), ← h0]
      exact ⟨hc, hder⟩
    exact hyz (hφ (this.trans (map_zero _).symm))

/-- **A compact Lie group with non-abelian Lie algebra has nontrivial third homotopy group**, at
every base point. The nontrivial class is that of an essential homomorphism `Spin(3) → G`
(`TauCeti.Lie.exists_contMDiffMonoidMorphism_realSpinThree_not_nullhomotopic`), read on the
sphere `S³ ≅ Spin(3)` and translated to the base point. -/
theorem nontrivial_homotopyGroup_three (hG : ¬IsLieAbelian (LeftInvariantDerivation I G))
    (g : G) : Nontrivial (HomotopyGroup (Fin 3) G g) := by
  obtain ⟨φ, -, hφ⟩ := exists_contMDiffMonoidMorphism_realSpinThree_not_nullhomotopic hG
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The composite `S³ ≃ₜ Spin(3) → G`, translated in `G` so that the north pole goes to `g`.
  let h : sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1 ≃ₜ spinGroup (realCliffordForm 3 0) :=
    (sphereHomeomorphOfFinrankEq (by simp [Quaternion.finrank_eq_four])).trans
      realSpinThreeHomeomorphQuaternionSphere.symm
  let t := Homeomorph.mulLeft (g * (φ (h (sphereNorthPole 3)))⁻¹)
  let r : C(sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1, G) :=
    (t : C(G, G)).comp ((φ : C(spinGroup (realCliffordForm 3 0), G)).comp h)
  have hr : r (sphereNorthPole 3) = g := by simp [r, t]
  have hrφ : (φ : C(spinGroup (realCliffordForm 3 0), G)) =
      (t.symm : C(G, G)).comp (r.comp h.symm) := by
    ext s
    simp [r]
  refine hr ▸ HomotopyGroup.nontrivial_of_not_nullhomotopic r fun hn ↦ hφ ?_
  rw [hrφ]
  exact (hn.comp_left _).comp_right _

section Transport

attribute [local instance] BoundarylessModel.interiorChartedSpace

omit [I.Boundaryless] [ChartedSpace H G] [LieGroup I ∞ G] in
/-- **A noncommutative compact connected Lie group has nontrivial third homotopy group**, at every
base point, for a Lie group modelled with corners on any finite-dimensional real normed space in
the lowest universe. -/
theorem nontrivial_homotopyGroup_three_of_not_isMulCommutative {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E H'} [ChartedSpace H' G] [LieGroup J ∞ G] [PreconnectedSpace G]
    (hG : ¬IsMulCommutative G) (g : G) : Nontrivial (HomotopyGroup (Fin 3) G g) := by
  -- A connected Lie group with abelian Lie algebra is commutative, so the Lie algebra of `G` is not
  -- abelian, and neither is that of its copy modelled on `E` itself, which has the same topology.
  have hab : ¬IsLieAbelian (LeftInvariantDerivation 𝓘(ℝ, E) (BoundarylessModel J G)) := fun h ↦
    hG (have : IsLieAbelian (LeftInvariantDerivation J G) :=
      (BoundarylessModel.interiorLieEquiv J (M := G)).injective.isLieAbelian h
    isMulCommutative_of_isLieAbelian J)
  have := nontrivial_homotopyGroup_three hab (BoundarylessModel.homeomorph J G g)
  exact (HomotopyGroup.homeomorphEquiv (BoundarylessModel.homeomorph J G) g).nontrivial

end Transport

include I in
/-- **A compact connected Lie group with trivial third homotopy group is a torus**: it is
isomorphic, as a topological group, to a product of circles, one for each dimension. -/
theorem nonempty_continuousMulEquiv_pi_circle_of_subsingleton_homotopyGroup_three
    [ConnectedSpace G] (g : G) [Subsingleton (HomotopyGroup (Fin 3) G g)] :
    Nonempty (G ≃ₜ* (Fin (Module.finrank ℝ E) → Circle)) := by
  have hab : IsLieAbelian (LeftInvariantDerivation I G) := by
    by_contra hG
    have := nontrivial_homotopyGroup_three hG g
    exact not_subsingleton (HomotopyGroup (Fin 3) G g) inferInstance
  have : IsMulCommutative G := ⟨⟨fun a b ↦ by
    simpa only [ContMDiffMonoidMorphism.coe_id, id_eq] using
      ((ContMDiffMonoidMorphism.id (I := I) (G := G)).commute_of_lie_lieMap_eq_zero
        ContMDiffMonoidMorphism.id (fun X Y ↦ by simp [lieMap_id, hab.trivial]) a b).eq⟩⟩
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : T2Space G := I.t2Space_of_lieGroup ∞
  exact nonempty_continuousMulEquiv_pi_circle (I := I)

end TauCeti.Lie
