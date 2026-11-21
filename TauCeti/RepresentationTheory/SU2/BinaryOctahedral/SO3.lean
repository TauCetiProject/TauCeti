/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinFour.Cube
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.RepresentationTheory.SU2.BinaryOctahedral.Basic

/-!
# The SO(3) image of the binary octahedral subgroup

Under the double cover `TauCeti.SU2.toSO3 : SU(2) →* SO(3)`, the binary octahedral subgroup
`TauCeti.SU2.binaryOctahedralSubgroup` maps onto the real cube rotation group
`(TauCeti.cubeRotationToSpecialOrthogonalGroup ℝ).range` of order 24, and is its full preimage
under `toSO3`. Combining this identification with `TauCeti.cubeRotationEquiv` yields the
isomorphism
`TauCeti.SU2.binaryOctahedralMapToSO3EquivPerm : binaryOctahedralSubgroup.map toSO3 ≃* S₄`.

## Main definitions

* `TauCeti.SU2.binaryOctahedralMapToSO3EquivPerm`: the isomorphism of the `SO(3)` image of `2O`
  with `S₄`.

## Main results

* `TauCeti.SU2.ker_toSO3_le_binaryOctahedralSubgroup` and
  `TauCeti.SU2.comap_map_toSO3_binaryOctahedralSubgroup`: `2O` contains the kernel `{1, -1}` of
  `toSO3`, hence equals the preimage of its `SO(3)` image.
* `TauCeti.SU2.natCard_map_toSO3_binaryOctahedralSubgroup`: the `SO(3)` image has `24` elements.
* `TauCeti.SU2.map_toSO3_binaryOctahedralSubgroup` and
  `TauCeti.SU2.comap_toSO3_range_cubeRotationToSpecialOrthogonalGroup`: the `SO(3)` image is the
  cube rotation group and `2O` is its full preimage under `toSO3`.
-/

public section

namespace TauCeti.SU2

open Quaternion

private theorem coe_torusHom_neg_one : (torusHom (-1) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [← weylElement_inv_sq_eq_torusHom_neg_one, coe_weylElement_inv_sq]

private theorem ker_toSO3_eq_pair : (toSO3.ker : Set SU2) = {1, torusHom (-1)} := by
  ext g
  rw [SetLike.mem_coe, MonoidHom.mem_ker, toSO3_eq_one_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ← Subtype.coe_inj, OneMemClass.coe_one,
    coe_torusHom_neg_one]

/-- The kernel `{1, -1}` of the double cover `SU(2) →* SO(3)` lies in the binary octahedral
subgroup. -/
theorem ker_toSO3_le_binaryOctahedralSubgroup : toSO3.ker ≤ binaryOctahedralSubgroup := by
  intro g hg
  rcases (ker_toSO3_eq_pair ▸ hg : g ∈ ({1, torusHom (-1)} : Set SU2)) with rfl | rfl
  · exact binaryOctahedralSubgroup.one_mem
  · exact torusHom_neg_one_mem_binaryOctahedralSubgroup

private theorem natCard_ker_toSO3 : Nat.card toSO3.ker = 2 := by
  have hne : (1 : SU2) ≠ torusHom (-1) := by
    rw [← map_one torusHom, ne_eq, torusHom_injective.eq_iff]
    intro h
    have := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at this
  change Nat.card (toSO3.ker : Set SU2) = 2
  rw [ker_toSO3_eq_pair, Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- The binary octahedral subgroup is the full preimage of its `SO(3)` image under the double
cover `toSO3`. -/
theorem comap_map_toSO3_binaryOctahedralSubgroup :
    (binaryOctahedralSubgroup.map toSO3).comap toSO3 = binaryOctahedralSubgroup :=
  Subgroup.comap_map_eq_self ker_toSO3_le_binaryOctahedralSubgroup

/-- **The `SO(3)` image of the binary octahedral subgroup has `24` elements.** -/
theorem natCard_map_toSO3_binaryOctahedralSubgroup :
    Nat.card (binaryOctahedralSubgroup.map toSO3) = 24 := by
  let f := toSO3.domRestrict binaryOctahedralSubgroup
  have hker_card : Nat.card f.ker = 2 := by
    rw [MonoidHom.ker_domRestrict,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ker_toSO3_le_binaryOctahedralSubgroup).toEquiv,
      natCard_ker_toSO3]
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hker_card, MonoidHom.domRestrict_range, natCard_binaryOctahedralSubgroup] at hmul
  omega

/-- The image of the eighth-turn `τ = (1 + i) / √2` under `toSO3` is a cube rotation. -/
private theorem toSO3_binaryDihedralRotation_four_mem_range :
    toSO3 (binaryDihedralRotation 4) ∈ (cubeRotationToSpecialOrthogonalGroup ℝ).range := by
  let A : cubeRotationGroup :=
    ⟨⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩,
      mem_cubeRotationGroup_iff.mpr
        ⟨Equiv.swap 0 1, ![-1, 1, 1], fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_cubeRotationToSpecialOrthogonalGroup, binaryDihedralRotation_def, coe_toSO3_torusHom]
  have hz : ((ZMod.toCircle (1 : ZMod (2 * 4)) : ℂ) ^ 2) = Complex.I := by
    have h1 := ZMod.toCircle_natCast (N := 2 * 4) 1
    rw [Nat.cast_one] at h1
    rw [h1, ← Complex.exp_natCast_mul]
    convert Complex.exp_pi_div_two_mul_I using 2
    push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, hz]

/-- The image of `ω = (-1 + i + j + k) / 2` under `toSO3` is a cube rotation. -/
private theorem toSO3_binaryTetrahedralOmega_mem_range :
    toSO3 binaryTetrahedralOmega ∈ (cubeRotationToSpecialOrthogonalGroup ℝ).range := by
  let A : cubeRotationGroup :=
    ⟨⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩,
      mem_cubeRotationGroup_iff.mpr
        ⟨[0, 1, 2].formPerm, ![1, 1, 1], fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_cubeRotationToSpecialOrthogonalGroup]
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [coe_toSO3, pauliRotation_mulVec, Submonoid.coe_inclusion, coe_binaryTetrahedralOmega,
    ← map_star]
  ext i
  fin_cases i <;>
    simp [A, pauliCoord_apply, pauli_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      toComplexMatrix_apply] <;> ring

/-- **The `SO(3)` image of the binary octahedral subgroup is the cube rotation group** embedded
into `SO(3, ℝ)` by `TauCeti.cubeRotationToSpecialOrthogonalGroup ℝ`. -/
theorem map_toSO3_binaryOctahedralSubgroup :
    binaryOctahedralSubgroup.map toSO3 = (cubeRotationToSpecialOrthogonalGroup ℝ).range := by
  have hle : binaryOctahedralSubgroup.map toSO3 ≤
      (cubeRotationToSpecialOrthogonalGroup ℝ).range := by
    rw [binaryOctahedralSubgroup_eq_closure_pair, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, rfl | rfl, rfl⟩
    · exact toSO3_binaryDihedralRotation_four_mem_range
    · exact toSO3_binaryTetrahedralOmega_mem_range
  have hcard : Nat.card (cubeRotationToSpecialOrthogonalGroup ℝ).range = 24 := by
    rw [← Nat.card_congr
      (MonoidHom.ofInjective (cubeRotationToSpecialOrthogonalGroup_injective ℝ)).toEquiv,
      natCard_cubeRotationGroup]
  have : Finite (cubeRotationToSpecialOrthogonalGroup ℝ).range :=
    Finite.of_equiv _
      (MonoidHom.ofInjective (cubeRotationToSpecialOrthogonalGroup_injective ℝ)).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, natCard_map_toSO3_binaryOctahedralSubgroup])

/-- **The binary octahedral subgroup is the full preimage of the real cube rotation group under
`toSO3`.** -/
theorem comap_toSO3_range_cubeRotationToSpecialOrthogonalGroup :
    (cubeRotationToSpecialOrthogonalGroup ℝ).range.comap toSO3 = binaryOctahedralSubgroup := by
  rw [← map_toSO3_binaryOctahedralSubgroup, comap_map_toSO3_binaryOctahedralSubgroup]

/-- **The `SO(3)` image of the binary octahedral subgroup is isomorphic to `S₄`**, via the
identification with the cube rotation group (`TauCeti.cubeRotationEquiv`). -/
noncomputable def binaryOctahedralMapToSO3EquivPerm :
    binaryOctahedralSubgroup.map toSO3 ≃* Equiv.Perm (Fin 4) :=
  ((MulEquiv.subgroupCongr map_toSO3_binaryOctahedralSubgroup).trans
    (MonoidHom.ofInjective (cubeRotationToSpecialOrthogonalGroup_injective ℝ)).symm).trans
    cubeRotationEquiv

/-- The inverse of `binaryOctahedralMapToSO3EquivPerm` sends a permutation of the four body
diagonals to the corresponding cube rotation matrix in `SO(3)`. -/
@[simp]
theorem coe_binaryOctahedralMapToSO3EquivPerm_symm (σ : Equiv.Perm (Fin 4)) :
    (binaryOctahedralMapToSO3EquivPerm.symm σ : Matrix.specialOrthogonalGroup (Fin 3) ℝ) =
      cubeRotationToSpecialOrthogonalGroup ℝ (cubeRotationEquiv.symm σ) := by
  simp only [binaryOctahedralMapToSO3EquivPerm, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.subgroupCongr_symm_apply]
  exact MonoidHom.ofInjective_apply (cubeRotationToSpecialOrthogonalGroup_injective ℝ)

end TauCeti.SU2
