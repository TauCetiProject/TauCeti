/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.Basic

/-!
# Sections of a Hermitian quadric by a linear coordinate

For a vector `z` with invertible self-pairing `B z z = u`, the fibre of `B z` over `t` is the
translate of its kernel by `(t * u⁻¹) • z`. On a Hermitian quadric `B y y = c`, this identifies
the slice with the quadric of level `c - star t * t * u⁻¹` in the kernel. The unit condition,
rather than a nonzero condition over a field, permits finite products of local fields.

The last-entry coordinates follow the statements of `New.Floors.vectorOfLastEntry` and
`New.Floors.lastEntrySphereIndex` in `grh/src/New/Spanning/Frames/StandardLevel.lean` and
`FiberMeasures.lean` of [grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open Topology

namespace LinearMap

variable {R V : Type*} [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
variable {B : V →ₛₗ[starRingEnd R] V →ₗ[R] R} {z : V} {u : Rˣ}

/-- The self-pairing on a coordinate fibre is the orthogonal self-pairing plus
`star t * t * u⁻¹` from the distinguished line. -/
theorem IsSymm.apply_self_add_smul_inv_unit (hB : B.IsSymm) (hz : B z z = (u : R))
    (t : R) (x : (B z).ker) :
    B ((x : V) + (t * (↑u⁻¹ : R)) • z) ((x : V) + (t * (↑u⁻¹ : R)) • z) =
      B x x + star t * t * (↑u⁻¹ : R) := by
  let a : R := t * (↑u⁻¹ : R)
  have hzx : B z x = 0 := (B z).map_coe_ker x
  have hxz : B x z = 0 := hB.eq_iff.mp hzx
  have hstar : star (u : R) = (u : R) := by
    simpa only [hz, starRingEnd_apply] using hB.eq z z
  have hstarInv : star (↑u⁻¹ : R) = (↑u⁻¹ : R) := by
    have hu : star u = u := Units.ext ((Units.coe_star u).trans hstar)
    rw [← Units.coe_star_inv, hu]
  have hx : B x ((x : V) + a • z) = B x x := by simp [hxz]
  have hza : B z ((x : V) + a • z) = t := by simp [a, hzx, hz, mul_assoc]
  calc
    B ((x : V) + a • z) ((x : V) + a • z) = B x x + star a * t := by
      simp only [B.map_add₂, hx, B.map_smulₛₗ₂, hza, starRingEnd_apply, smul_eq_mul]
    _ = _ := by rw [star_mul, hstarInv]; ring

/-- The chart inserts a point into the prescribed quadric slice exactly when its
orthogonal component has the shifted self-pairing. -/
theorem IsSymm.add_smul_inv_unit_mem_quadricFiber_iff (hB : B.IsSymm)
    (hz : B z z = (u : R)) (t c : R) (x : (B z).ker) :
    (x : V) + (t * (↑u⁻¹ : R)) • z ∈ {y | B z y = t ∧ B y y = c} ↔
      B x x = c - star t * t * (↑u⁻¹ : R) := by
  have ht : B z ((x : V) + (t * (↑u⁻¹ : R)) • z) = t := by
    simp [(B z).map_coe_ker x, hz, mul_assoc]
  simp only [Set.mem_ofPred_eq, ht, true_and, hB.apply_self_add_smul_inv_unit hz]
  exact eq_sub_iff_add_eq.symm

section Topology

/-- The affine chart is a closed embedding when the coordinate `B z` is continuous. -/
theorem isClosedEmbedding_add_smul_inv_unit [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousAdd V] [T1Space R] (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (z : V) (u : Rˣ) (hcont : Continuous (B z)) (t : R) :
    IsClosedEmbedding (fun x : (B z).ker ↦ (x : V) + (t * (↑u⁻¹ : R)) • z) :=
  (Homeomorph.addRight ((t * (↑u⁻¹ : R)) • z)).isClosedEmbedding.comp
    (ContinuousLinearMap.isClosed_ker (⟨B z, hcont⟩ : V →L[R] R)).isClosedEmbedding_subtypeVal

variable [TopologicalSpace V] [ContinuousAdd V]

/-- The slice of a Hermitian quadric of level `c` with coordinate `B z y = t` is homeomorphic
to the quadric of level `c - star t * t * u⁻¹` in the orthogonal complement of `z`. -/
def IsSymm.quadricFiberHomeomorph (hB : B.IsSymm)
    (hz : B z z = (u : R)) (t c : R) :
    {x : (B z).ker // B x x = c - star t * t * (↑u⁻¹ : R)} ≃ₜ
      {y : V // B z y = t ∧ B y y = c} where
  toFun x := ⟨(x.val : V) + (t * (↑u⁻¹ : R)) • z,
    (hB.add_smul_inv_unit_mem_quadricFiber_iff hz t c x.val).mpr x.property⟩
  invFun y := by
    let x : (B z).ker := ⟨y - (t * (↑u⁻¹ : R)) • z, by simp [y.property.1, hz, mul_assoc]⟩
    refine ⟨x, (hB.add_smul_inv_unit_mem_quadricFiber_iff hz t c x).mp ?_⟩
    have hx : (x : V) + (t * (↑u⁻¹ : R)) • z = y := sub_add_cancel _ _
    rw [hx]
    exact y.property
  left_inv x := by ext; exact add_sub_cancel_right _ _
  right_inv y := by ext; exact sub_add_cancel _ _
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).add_const _ |>.subtype_mk _
  continuous_invFun := by
    refine (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _)
    simp only [sub_eq_add_neg]
    exact continuous_subtypeVal.add_const _

/-- The forward chart adds the unique multiple of `z` giving last entry `t`. -/
@[simp] theorem IsSymm.quadricFiberHomeomorph_apply_coe (hB : B.IsSymm)
    (hz : B z z = (u : R)) (t c : R)
    (x : {x : (B z).ker // B x x = c - star t * t * (↑u⁻¹ : R)}) :
    (hB.quadricFiberHomeomorph hz t c x : V) = (x.val : V) + (t * (↑u⁻¹ : R)) • z := (rfl)

/-- The inverse chart removes the component along `z`. -/
@[simp] theorem IsSymm.quadricFiberHomeomorph_symm_apply_coe (hB : B.IsSymm)
    (hz : B z z = (u : R)) (t c : R) (y : {y : V // B z y = t ∧ B y y = c}) :
    (((hB.quadricFiberHomeomorph hz t c).symm y).val : V) =
      (y : V) - (t * (↑u⁻¹ : R)) • z := (rfl)

end Topology

end LinearMap
