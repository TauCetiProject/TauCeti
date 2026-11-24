/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action
public import TauCeti.AlgebraicTopology.Singular.Cubical.TotallyDisconnected

/-!
# The chain module of a totally disconnected space

Let `Y` be a totally disconnected space with a continuous right action of a topological monoid
`G`, for instance the discrete fibre of a covering map with the action of the Moore loops. The
normalized cubical chains of `Y` of positive dimension vanish
(`TauCeti.NormalizedCubicalChain.instSubsingletonSuccOfTotallyDisconnectedSpace`), so the DG right
module `C^□_*(Y; R)` over the chains of `G` is concentrated in degree zero
(`TauCeti.isConcentratedInDegreeZero_cubicalChainModuleDG`), and as a module it is the free module
on the points of `Y` (`TauCeti.cubicalChainModuleFinsuppEquiv`). Under this identification the
`0`-chain of `g ∈ G` acts by the permutation of the basis that `g` induces on `Y`
(`TauCeti.cubicalChainModuleFinsuppEquiv_op_smul`): the chain module is the permutation module of
the action.

## Main definitions

* `TauCeti.cubicalChainModuleFinsuppEquiv`: the chain module of a totally disconnected space is
  the free module on its points.

## Main results

* `TauCeti.isConcentratedInDegreeZero_cubicalChainModuleDG`: the chain module is concentrated in
  degree zero.
* `TauCeti.cubicalChainModuleFinsuppEquiv_op_smul`: a point of `G` acts by permuting the basis.
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite NormalizedCubicalChain

variable {Y G : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {R : Type*} [CommRing R]

section Carrier

variable (Y G R) in
/-- **The chain module of a totally disconnected space is the free module on its points**: it
consists of its `0`-chains, the formal combinations of points. -/
def cubicalChainModuleFinsuppEquiv : cubicalChainModule Y G R ≃ₗ[R] (Y →₀ R) :=
  LinearEquiv.ofLinearMap
    (cubicalChainModuleDesc fun
      | 0 => (zeroEquiv Y R).toLinearMap
      | _ + 1 => 0)
    (cubicalChainModuleLof Y G R 0 ∘ₗ (zeroEquiv Y R).symm.toLinearMap)
    (LinearMap.ext fun x ↦ by simp)
    (cubicalChainModule_linearMap_ext fun n c ↦ by
      cases n with
      | zero => simp
      | succ n => simp [Subsingleton.elim c 0])

/-- On `0`-chains the identification with the free module on the points is `zeroEquiv`. -/
@[simp]
theorem cubicalChainModuleFinsuppEquiv_lof_zero (c : NormalizedCubicalChain Y R 0) :
    cubicalChainModuleFinsuppEquiv Y G R (cubicalChainModuleLof Y G R 0 c) = zeroEquiv Y R c :=
  cubicalChainModuleDesc_lof _ c

/-- The `0`-chain of a point is the indicator of that point. -/
theorem cubicalChainModuleFinsuppEquiv_lof_ofCube_point (y : Y) :
    cubicalChainModuleFinsuppEquiv Y G R
        (cubicalChainModuleLof Y G R 0 (ofCube Y R (SingularCube.point y))) =
      Finsupp.single y 1 := by
  simp

/-- The indicator of a point is the `0`-chain of that point. -/
@[simp]
theorem cubicalChainModuleFinsuppEquiv_symm_single (y : Y) (r : R) :
    (cubicalChainModuleFinsuppEquiv Y G R).symm (Finsupp.single y r) =
      r • cubicalChainModuleLof Y G R 0 (ofCube Y R (SingularCube.point y)) := by
  rw [LinearEquiv.symm_apply_eq, map_smul, cubicalChainModuleFinsuppEquiv_lof_ofCube_point,
    Finsupp.smul_single_one]

end Carrier

section Action

variable [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y]

variable (Y G R) in
/-- **The chain module of a totally disconnected space is concentrated in degree zero.** -/
theorem isConcentratedInDegreeZero_cubicalChainModuleDG :
    (cubicalChainModuleDG Y G R).IsConcentratedInDegreeZero :=
  DGRightModuleCat.isConcentratedInDegreeZero_iff.2 fun q hq ↦
    (Submodule.eq_bot_iff _).2 fun x hx ↦ by
      rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
      · rfl
      · cases n with
        | zero => omega
        | succ n => rw [Subsingleton.elim c 0, map_zero]

/-- **A point of `G` permutes the basis**: under the identification of the chain module with the
free module on the points of `Y`, the `0`-chain of `g` acts by the map induced by `y ↦ y · g`. -/
@[simp]
theorem cubicalChainModuleFinsuppEquiv_op_smul (g : G) (m : cubicalChainModule Y G R) :
    cubicalChainModuleFinsuppEquiv Y G R
        (op (cubicalChainLof G R 0 (ofCube G R (SingularCube.point g))) • m) =
      Finsupp.mapDomain (fun y ↦ op g • y) (cubicalChainModuleFinsuppEquiv Y G R m) := by
  rw [← (cubicalChainModuleFinsuppEquiv Y G R).symm_apply_apply m]
  induction cubicalChainModuleFinsuppEquiv Y G R m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, smul_add, map_add, ha, hb, map_add, Finsupp.mapDomain_add]
  | single y r =>
    simp [smul_comm, op_lof_smul_cubicalChainModuleLof]

end Action

end TauCeti
