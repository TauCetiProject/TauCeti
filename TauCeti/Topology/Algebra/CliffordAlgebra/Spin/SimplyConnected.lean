/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Three
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
public import TauCeti.Topology.Algebra.Quaternion.Unitary

import TauCeti.AlgebraicTopology.FundamentalGroup.Product
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.AlgebraicTopology.Sphere.Equator
import TauCeti.AlgebraicTopology.Sphere.Puncture
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Orbit.Bundle
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Simple-connectedness of compact Spin groups

The algebraic equivalence from compact `Spin(3)` to the unit Hamilton quaternions is continuous.
Compactness of the source upgrades it to a continuous multiplicative equivalence. Unit quaternions
form the unit sphere in the four-dimensional real space `ℍ`, so the existing simple-connectedness
theorem for spheres proves that compact `Spin(3)` is simply connected.

For higher dimensions, two trivializations of the sphere bundle
`Spin(n) → Spin(n + 1) → Sⁿ`, centred at antipodal points, cover the total group. Each chart is a
product of `Spin(n)` with a punctured sphere, while their overlap retracts to the equator. The
two-set van Kampen theorem therefore gives the inductive step and proves that compact `Spin(n)` is
simply connected for every `n ≥ 3`.

## Main results

* `TauCeti.realSpinThreeContinuousMulEquivQuaternionUnitary` upgrades the quaternion model of
  compact `Spin(3)` to an equivalence of topological groups.
* `TauCeti.realSpinThreeHomeomorphQuaternionSphere` identifies compact `Spin(3)` with the unit
  quaternion sphere.
* `CliffordAlgebra.simplyConnectedSpace_realCliffordSpinGroupZero_three` proves that compact
  `Spin(3)` is simply connected.
* `CliffordAlgebra.simplyConnectedSpace_realCliffordSpinGroupZero_succ` is the sphere-bundle
  induction step.
* `CliffordAlgebra.simplyConnectedSpace_realCliffordSpinGroupZero` proves the result for every
  dimension at least three.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §6.
* A. Hatcher, *Algebraic Topology* (2002), Theorem 1.20.
-/

public section

open Metric
open scoped Quaternion

namespace TauCeti

/-- The algebraic equivalence from compact `Spin(3)` to the unit Hamilton quaternions is
continuous. -/
theorem continuous_realSpinThreeEquivQuaternionUnitary :
    Continuous (realSpinThreeEquivQuaternionUnitary :
      spinGroup (realCliffordForm 3 0) → unitary ℍ[ℝ]) := by
  apply continuous_induced_rng.2
  have hfun : Subtype.val ∘ (realSpinThreeEquivQuaternionUnitary :
      spinGroup (realCliffordForm 3 0) → unitary ℍ[ℝ]) =
      fun s ↦ realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) := by
    funext s
    exact coe_realSpinThreeEquivQuaternionUnitary_apply s
  rw [hfun]
  let _ : IsTopologicalAddGroup (CliffordAlgebra.even (realCliffordForm 3 0)) :=
    (CliffordAlgebra.even (realCliffordForm 3 0)).toSubmodule.isTopologicalAddGroup
  have hinner : Continuous (fun s ↦
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
        (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) := by
    apply continuous_induced_rng.2
    have hinnerFun : Subtype.val ∘ (fun s ↦
        CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 3 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 3 0) s)) =
        fun s : spinGroup (realCliffordForm 3 0) ↦
          (s : CliffordAlgebra (realCliffordForm 3 0)) := by
      funext s
      simp only [Function.comp_apply, CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
        CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
      rfl
    rw [hinnerFun]
    exact continuous_subtype_val
  exact realCliffordThreeZeroEvenEquivQuaternion.toLinearMap.continuous_of_finiteDimensional.comp
    hinner

/-- Compact `Spin(3)` is continuously multiplicatively equivalent to the unit Hamilton
quaternions. -/
noncomputable def realSpinThreeContinuousMulEquivQuaternionUnitary :
    spinGroup (realCliffordForm 3 0) ≃ₜ* unitary ℍ[ℝ] :=
  ContinuousMulEquiv.mk realSpinThreeEquivQuaternionUnitary
    continuous_realSpinThreeEquivQuaternionUnitary
    (continuous_realSpinThreeEquivQuaternionUnitary.continuous_symm_of_equiv_compact_to_t2
      (f := realSpinThreeEquivQuaternionUnitary.toEquiv))

/-- The topological quaternion equivalence has the existing algebraic equivalence as its forward
map. -/
@[simp]
theorem realSpinThreeContinuousMulEquivQuaternionUnitary_apply
    (s : spinGroup (realCliffordForm 3 0)) :
    realSpinThreeContinuousMulEquivQuaternionUnitary s =
      realSpinThreeEquivQuaternionUnitary s := by
  rw [realSpinThreeContinuousMulEquivQuaternionUnitary]
  rfl

/-- The inverse topological quaternion equivalence has the existing algebraic inverse as its
map. -/
@[simp]
theorem realSpinThreeContinuousMulEquivQuaternionUnitary_symm_apply
    (q : unitary ℍ[ℝ]) :
    realSpinThreeContinuousMulEquivQuaternionUnitary.symm q =
      realSpinThreeEquivQuaternionUnitary.symm q := by
  rw [realSpinThreeContinuousMulEquivQuaternionUnitary]
  rfl

/-- Compact `Spin(3)` is homeomorphic to the unit sphere in the real quaternion space. -/
noncomputable def realSpinThreeHomeomorphQuaternionSphere :
    spinGroup (realCliffordForm 3 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 :=
  realSpinThreeContinuousMulEquivQuaternionUnitary.toHomeomorph.trans
    Quaternion.unitaryHomeomorphSphere

/-- The homeomorphism from compact `Spin(3)` to the quaternion sphere applies the existing
quaternion equivalence to the underlying element. -/
@[simp]
theorem coe_realSpinThreeHomeomorphQuaternionSphere_apply
    (s : spinGroup (realCliffordForm 3 0)) :
    (realSpinThreeHomeomorphQuaternionSphere s : ℍ[ℝ]) =
      realSpinThreeEquivQuaternionUnitary s := by
  rw [realSpinThreeHomeomorphQuaternionSphere, Homeomorph.trans_apply,
    Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact congrArg Subtype.val (realSpinThreeContinuousMulEquivQuaternionUnitary_apply s)

/-- The inverse sphere homeomorphism is the inverse of the existing algebraic equivalence after
viewing a sphere point as a unitary quaternion. -/
@[simp]
theorem realSpinThreeHomeomorphQuaternionSphere_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1) :
    realSpinThreeHomeomorphQuaternionSphere.symm q =
      realSpinThreeEquivQuaternionUnitary.symm
        (Quaternion.unitaryHomeomorphSphere.symm q) := by
  rw [realSpinThreeHomeomorphQuaternionSphere, Homeomorph.symm_trans_apply]
  rw [ContinuousMulEquiv.toHomeomorph_eq_coe,
    ContinuousMulEquiv.coe_toHomeomorph_symm]
  exact realSpinThreeContinuousMulEquivQuaternionUnitary_symm_apply
    (Quaternion.unitaryHomeomorphSphere.symm q)

end TauCeti

namespace CliffordAlgebra

open TauCeti
open Metric Set Topology

/-- The compact three-dimensional real Spin group is simply connected. -/
theorem simplyConnectedSpace_realCliffordSpinGroupZero_three :
    SimplyConnectedSpace (realCliffordSpinGroupZero 3) := by
  let _ : SimplyConnectedSpace (sphere (0 : ℍ[ℝ]) 1) := by
    apply simplyConnectedSpace_sphere
    · rw [Quaternion.rank_eq_four]
      norm_num
    · positivity
  exact realSpinThreeHomeomorphQuaternionSphere.toHomotopyEquiv.simplyConnectedSpace

private theorem contractibleSpace_realCliffordUnitLevel_compl_singleton {n : ℕ}
    (x : realCliffordUnitLevel n) :
    ContractibleSpace ({x}ᶜ : Set (realCliffordUnitLevel n)) := by
  let e := realCliffordUnitLevelHomeomorphSphere n
  let _ : ContractibleSpace ({e x}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    contractibleSpace_sphere_compl_singleton (e x)
  let punctureEquiv : ({x}ᶜ : Set (realCliffordUnitLevel n)) ≃ₜ
      ({e x}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    e.subtype (p := fun y ↦ y ∈ ({x}ᶜ : Set (realCliffordUnitLevel n)))
      (q := fun y ↦ y ∈ ({e x}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
      fun y ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact not_congr e.injective.eq_iff.symm
  exact punctureEquiv.contractibleSpace

private theorem pathConnectedSpace_realCliffordUnitLevel_compl_antipodal {n : ℕ}
    (hn : 2 ≤ n) (p : realCliffordUnitLevel (n + 1)) :
    PathConnectedSpace
      ({p}ᶜ ∩ {realCliffordUnitLevelAntipode p}ᶜ : Set (realCliffordUnitLevel (n + 1))) := by
  let e := realCliffordUnitLevelHomeomorphSphere (n + 1)
  let q := e p
  have hneg : e (realCliffordUnitLevelAntipode p) = -q := by
    apply Subtype.ext
    simp only [e, q, coe_realCliffordUnitLevelHomeomorphSphere_apply,
      coe_realCliffordUnitLevelAntipode, coe_neg_sphere, map_neg]
  let eOverlap :
      ({p}ᶜ ∩ {realCliffordUnitLevelAntipode p}ᶜ : Set (realCliffordUnitLevel (n + 1))) ≃ₜ
        ({q}ᶜ ∩ {-q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    e.subtype
      (p := fun x ↦ x ∈
        ({p}ᶜ ∩ {realCliffordUnitLevelAntipode p}ᶜ : Set (realCliffordUnitLevel (n + 1))))
      (q := fun x ↦ x ∈
        ({q}ᶜ ∩ {-q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
      fun x ↦ by
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
      dsimp only [q]
      rw [← hneg]
      exact and_congr (not_congr e.injective.eq_iff.symm)
        (not_congr e.injective.eq_iff.symm)
  let K := (ℝ ∙ (q : EuclideanSpace ℝ (Fin (n + 1))))ᗮ
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  have hfinrank : Module.finrank ℝ K = n := by
    exact Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere q)
  have hrank : 1 < Module.rank ℝ K := by
    rw [← Module.finrank_eq_rank, hfinrank]
    exact_mod_cast hn
  let _ : PathConnectedSpace (sphere (0 : K) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank 0 zero_le_one)
  let _ : PathConnectedSpace
      ({q}ᶜ ∩ {-q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    (equatorHomotopyEquiv q).symm.pathConnectedSpace
  exact eOverlap.symm.toHomotopyEquiv.pathConnectedSpace

private theorem simplyConnectedSpace_realCliffordSpinOrbitTrivialization_source
    (n : ℕ) [SimplyConnectedSpace (realCliffordSpinGroupZero n)]
    (y : realCliffordUnitLevel (n + 1))
    (e : Bundle.Trivialization (realCliffordSpinGroupZero n)
      (realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n)))
    (he : e.baseSet = {realCliffordUnitLevelAntipode y}ᶜ) :
    SimplyConnectedSpace e.source := by
  let _ : ContractibleSpace
      ({realCliffordUnitLevelAntipode y}ᶜ : Set (realCliffordUnitLevel (n + 1))) :=
    contractibleSpace_realCliffordUnitLevel_compl_singleton _
  let _ : SimplyConnectedSpace
      ({realCliffordUnitLevelAntipode y}ᶜ : Set (realCliffordUnitLevel (n + 1))) := inferInstance
  let baseEquiv : e.baseSet ≃ₜ
      ({realCliffordUnitLevelAntipode y}ᶜ : Set (realCliffordUnitLevel (n + 1))) :=
    Homeomorph.setCongr he
  let _ : SimplyConnectedSpace e.baseSet :=
    baseEquiv.toHomotopyEquiv.simplyConnectedSpace
  let _ : SimplyConnectedSpace (e.baseSet × realCliffordSpinGroupZero n) := inferInstance
  exact e.sourceHomeomorphBaseSetProd.toHomotopyEquiv.simplyConnectedSpace

/-- If compact `Spin(n)` is simply connected for `n ≥ 2`, then compact `Spin(n + 1)` is simply
connected. This is the induction step from the sphere bundle
`Spin(n) → Spin(n + 1) → Sⁿ`. -/
theorem simplyConnectedSpace_realCliffordSpinGroupZero_succ (n : ℕ) (hn : 2 ≤ n)
    [SimplyConnectedSpace (realCliffordSpinGroupZero n)] :
    SimplyConnectedSpace (realCliffordSpinGroupZero (n + 1)) := by
  let _ : NeZero n := ⟨by omega⟩
  let p := realCliffordSpinLastUnit n
  let p' := realCliffordUnitLevelAntipode p
  let proj := realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n)
  obtain ⟨e, he⟩ := exists_realCliffordSpinOrbitTrivialization n p
  obtain ⟨e', he'⟩ := exists_realCliffordSpinOrbitTrivialization n p'
  have hsimple : SimplyConnectedSpace e.source :=
    simplyConnectedSpace_realCliffordSpinOrbitTrivialization_source n p e he
  have hsimple' : SimplyConnectedSpace e'.source :=
    simplyConnectedSpace_realCliffordSpinOrbitTrivialization_source n p' e' he'
  let S := e.baseSet ∩ e'.baseSet
  have hS : S = {p}ᶜ ∩ {p'}ᶜ := by
    dsimp only [S]
    rw [he, he', realCliffordUnitLevelAntipode_antipode, inter_comm]
  let _ : PathConnectedSpace ({p}ᶜ ∩ {p'}ᶜ : Set (realCliffordUnitLevel (n + 1))) :=
    pathConnectedSpace_realCliffordUnitLevel_compl_antipodal hn p
  let SEquiv : S ≃ₜ ({p}ᶜ ∩ {p'}ᶜ : Set (realCliffordUnitLevel (n + 1))) :=
    Homeomorph.setCongr hS
  let _ : PathConnectedSpace S := SEquiv.symm.toHomotopyEquiv.pathConnectedSpace
  let _ : PathConnectedSpace (S × realCliffordSpinGroupZero n) := inferInstance
  have hsourceInter : e.source ∩ e'.source = proj ⁻¹' S := by
    ext x
    simp only [Set.mem_inter_iff, e.mem_source, e'.mem_source, Set.mem_preimage, S, proj]
  let sourceInterEquiv : ↥(e.source ∩ e'.source) ≃ₜ S × realCliffordSpinGroupZero n :=
    (Homeomorph.setCongr hsourceInter).trans (e.preimageHomeomorph inter_subset_left)
  have hInter : IsPathConnected (e.source ∩ e'.source) :=
    isPathConnected_iff_pathConnectedSpace.mpr
      sourceInterEquiv.symm.toHomotopyEquiv.pathConnectedSpace
  have hCover : e.source ∪ e'.source = univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true, e.mem_source, e'.mem_source]
    rw [he, he']
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hp' : realCliffordUnitLevelAntipode p' = p := by
      dsimp only [p']
      exact realCliffordUnitLevelAntipode_antipode p
    rw [hp']
    by_cases hx : proj x = p'
    · right
      exact fun hx' ↦ ne_realCliffordUnitLevelAntipode p (hx'.symm.trans hx)
    · exact Or.inl hx
  let _ : SimplyConnectedSpace e.source := hsimple
  let _ : SimplyConnectedSpace e'.source := hsimple'
  apply simplyConnectedSpace_of_interior_union (A := e.source) (B := e'.source)
  · simpa only [e.open_source.interior_eq, e'.open_source.interior_eq] using hCover
  · exact hInter

/-- The compact real Spin group is simply connected in every dimension at least three. -/
theorem simplyConnectedSpace_realCliffordSpinGroupZero (n : ℕ) (hn : 3 ≤ n) :
    SimplyConnectedSpace (realCliffordSpinGroupZero n) := by
  induction n, hn using Nat.le_induction with
  | base => exact simplyConnectedSpace_realCliffordSpinGroupZero_three
  | succ n hn ih =>
      let _ : SimplyConnectedSpace (realCliffordSpinGroupZero n) := ih
      exact simplyConnectedSpace_realCliffordSpinGroupZero_succ n (by omega)

end CliffordAlgebra
