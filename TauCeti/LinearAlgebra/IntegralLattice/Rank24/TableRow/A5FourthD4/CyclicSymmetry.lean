/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.A5FourthD4

import TauCeti.Data.Fin.Cast

/-!
# The coupled triality symmetry of the table row `A₅⁴ D₄`

In the rootful rank-24 table, `TauCeti.RootfulNiemeierType.a5FourthD4` is the unique row whose
parenthesized pattern symmetry is not a pure coordinate glue symmetry: rotating the three marked
`A₅` positions `1, 2, 3` (`TauCeti.RootfulNiemeierType.a5FourthD4BlockRotation`) while leaving the
`D₄` label in position `4` unchanged sends `[33001]` outside the glue subgroup
(`TauCeti.RootfulNiemeierType.a5FourthD4BlockRotation_notMem_glueSymmetries`).

Coupling the block rotation with `D₄` triality (`TauCeti.DynkinType.typeD4Triality`) on the `D₄`
component preserves `a5FourthD4.glueSubgroup`
(`TauCeti.RootfulNiemeierType.a5FourthD4TrialityGlueIsometry_mem_glueSubgroup_iff`), yielding the
order-three, determinant-one self-isometry
`TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation` (= `a5FourthD4TrialityIsometry`) of
`TauCeti.niemeierA5FourthD4`.  This yields a faithful action
`TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom` of the cyclic pattern's symmetry group on
`niemeierA5FourthD4`.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation`: the order-three, determinant-one
  (`orderOf_a5FourthD4TrialityRotation`, `det_a5FourthD4TrialityRotation`) self-isometry of
  `niemeierA5FourthD4` rotating the three marked `A₅` components and applying `typeD4Triality` on
  the `D₄` component.
* `TauCeti.RootfulNiemeierType.mem_symmetries_cyclic_a5FourthD4_iff`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.exists_a5FourthD4CyclicSymmetryHom_eq_pow`,
  `TauCeti.RootfulNiemeierType.det_a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom_injective`: membership characterization
  and faithful determinant-one action of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` on
  `niemeierA5FourthD4`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Re-exporting the coupled triality rotation on `niemeierA5FourthD4` -/

/-- **The coupled triality rotation of `niemeierA5FourthD4`**: the self-isometry moving the three
marked `A₅` components by `1 ↦ 2 ↦ 3 ↦ 1`, fixing the leading `A₅` component `0`, and applying
`TauCeti.DynkinType.typeD4Triality` on the `D₄` component `4`. -/
noncomputable def a5FourthD4TrialityRotation :
    Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  a5FourthD4TrialityIsometry

private theorem a5FourthD4TrialityRotation_apply_of_eq
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ)
    {k b : Fin a5FourthD4.components.length}
    (hk : k ≠ a5FourthD4D4Index) (hkb : a5FourthD4BlockRotation.symm k = b)
    (hb : (a5FourthD4.componentType k).rank = (a5FourthD4.componentType b).rank := by rfl) :
    a5FourthD4TrialityRotation x k = fun j ↦ x b (Fin.cast hb j) := by
  funext j
  exact (a5FourthD4TrialityIsometry_apply_of_ne x hk j).trans
    (Fin.apply_cast_eq_apply_cast x hkb _ hb j)

@[simp]
theorem a5FourthD4TrialityRotation_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (0 : Fin 5) = x (0 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_eq x (k := ⟨0, by decide⟩) (b := ⟨0, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_zero (by decide))

@[simp]
theorem a5FourthD4TrialityRotation_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (1 : Fin 5) = x (3 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_eq x (k := ⟨1, by decide⟩) (b := ⟨3, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_one (by decide))

@[simp]
theorem a5FourthD4TrialityRotation_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (2 : Fin 5) = x (1 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_eq x (k := ⟨2, by decide⟩) (b := ⟨1, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_two (by decide))

@[simp]
theorem a5FourthD4TrialityRotation_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (3 : Fin 5) = x (2 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_eq x (k := ⟨3, by decide⟩) (b := ⟨2, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_three (by decide))

@[simp]
theorem a5FourthD4TrialityRotation_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (4 : Fin 5) =
      typeD4Triality (isSimplyLaced_D 4) (x (4 : Fin 5)) :=
  a5FourthD4TrialityIsometry_apply_four x

/-- **The coupled triality rotation has order dividing three.** -/
@[simp]
theorem a5FourthD4TrialityRotation_pow_three : a5FourthD4TrialityRotation ^ 3 = 1 :=
  a5FourthD4TrialityIsometry_pow_three

/-- `a5FourthD4TrialityRotation` has exact order `3`. -/
@[simp]
theorem orderOf_a5FourthD4TrialityRotation : orderOf a5FourthD4TrialityRotation = 3 :=
  orderOf_a5FourthD4TrialityIsometry

/-- `a5FourthD4TrialityRotation` is nontrivial. -/
theorem a5FourthD4TrialityRotation_ne_one : a5FourthD4TrialityRotation ≠ 1 := by
  intro h
  have h3 := orderOf_a5FourthD4TrialityRotation
  rw [h, orderOf_one] at h3
  exact absurd h3 (by decide)

/-- **`a5FourthD4TrialityRotation` is a proper isometry (`det = 1`).** -/
@[simp]
theorem det_a5FourthD4TrialityRotation :
    Isometry.det niemeierA5FourthD4 a5FourthD4TrialityRotation = 1 :=
  Isometry.det_eq_one_of_pow_eq_one (by decide : Odd 3) a5FourthD4TrialityRotation_pow_three

/-! ### Faithful action of `[2(024)0].symmetries` on `niemeierA5FourthD4` -/

/-- The symmetry group of `[2(024)0]` is the cyclic subgroup generated by
`a5FourthD4BlockRotation`. -/
theorem symmetries_cyclic_a5FourthD4 :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries =
      Subgroup.zpowers (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) := by
  refine (GluePattern.symmetries_cyclic [2] [0, 2, 4] [0]).trans (congrArg Subgroup.zpowers ?_)
  ext i
  have hi := congrArg Fin.val (Equiv.congr_fun permCongr_finSumPerm_finRotate ⟨i.val, i.isLt⟩)
  rw [Equiv.permCongr_apply, finCongr_apply, Fin.val_cast, finCongr_symm, finCongr_apply] at hi
  have hcast : Fin.cast (by decide : 1 + 3 + 1 = a5FourthD4.components.length).symm
      (⟨i.val, i.isLt⟩ : Fin a5FourthD4.components.length) = i :=
    Fin.ext (Fin.val_cast _ _)
  exact (congrArg (fun j : Fin (1 + 3 + 1) ↦ ((Equiv.Perm.finSumPerm
    (Equiv.Perm.finSumPerm (1 : Equiv.Perm (Fin 1)) (finRotate 3))
    (1 : Equiv.Perm (Fin 1))) j).val) hcast).symm.trans hi

/-- `a5FourthD4BlockRotation` belongs to the symmetry group of the cyclic pattern `[2(024)0]`. -/
theorem a5FourthD4BlockRotation_mem_symmetries :
    (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ∈
      (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries := by
  rw [symmetries_cyclic_a5FourthD4]
  exact Subgroup.mem_zpowers _

private theorem mem_zpowers_a5FourthD4BlockRotation_iff
    (g : Equiv.Perm (Fin a5FourthD4.components.length)) :
    g ∈ Subgroup.zpowers a5FourthD4BlockRotation ↔
      g = 1 ∨ g = a5FourthD4BlockRotation ∨ g = a5FourthD4BlockRotation ^ 2 := by
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_a5FourthD4BlockRotation]
  simp only [Finset.range_add_one, Finset.range_zero, Finset.mem_image, Finset.mem_insert,
    Finset.notMem_empty, exists_eq_or_imp, pow_zero, pow_one]
  tauto

/-- **The symmetries of the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`** are `1`,
`a5FourthD4BlockRotation`, and `a5FourthD4BlockRotation ^ 2`. -/
theorem mem_symmetries_cyclic_a5FourthD4_iff (g : Equiv.Perm (Fin 5)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ∨
        g = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ^ 2 :=
  (SetLike.ext_iff.mp symmetries_cyclic_a5FourthD4 g).trans
    (mem_zpowers_a5FourthD4BlockRotation_iff g)

private theorem forall_mem_zpowers_a5FourthD4BlockRotation
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    g ∈ Subgroup.zpowers
      (⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
        a5FourthD4BlockRotation_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((SetLike.ext_iff.mp symmetries_cyclic_a5FourthD4 g.val).mp g.property)
  exact ⟨k, Subtype.ext hk⟩

private theorem orderOf_a5FourthD4BlockRotation_mk_eq_orderOf_a5FourthD4TrialityRotation_mk :
    orderOf (⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
        a5FourthD4BlockRotation_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) =
      orderOf (⟨a5FourthD4TrialityRotation, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers a5FourthD4TrialityRotation) :=
  (Subgroup.orderOf_mk (a5FourthD4BlockRotation : Equiv.Perm (Fin 5))
      a5FourthD4BlockRotation_mem_symmetries).trans
    ((show orderOf (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) = 3 from
        orderOf_a5FourthD4BlockRotation).trans
      (orderOf_a5FourthD4TrialityRotation.symm.trans (Subgroup.orderOf_mk _ _).symm))

/-- **The indicated symmetry group of `[2(024)0]` acts on `niemeierA5FourthD4`** by powers of
`a5FourthD4TrialityRotation`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  (Subgroup.zpowers a5FourthD4TrialityRotation).subtype.comp
    (mulEquivOfOrderOfEq forall_mem_zpowers_a5FourthD4BlockRotation
      (Subgroup.forall_zpowers.mpr fun m ↦ ⟨m, rfl⟩)
      orderOf_a5FourthD4BlockRotation_mk_eq_orderOf_a5FourthD4TrialityRotation_mk).toMonoidHom

/-- The generator `a5FourthD4BlockRotation` of `[2(024)0].symmetries` acts as
`a5FourthD4TrialityRotation`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_blockRot :
    a5FourthD4CyclicSymmetryHom
        ⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
          a5FourthD4BlockRotation_mem_symmetries⟩ =
      a5FourthD4TrialityRotation := by
  simp [a5FourthD4CyclicSymmetryHom, mulEquivOfOrderOfEq_apply_gen]

/-- Every symmetry of `[2(024)0]` acts on the component positions as `a5FourthD4BlockRotation ^ k`
(`k < 3`) and on `niemeierA5FourthD4` as the matching power `a5FourthD4TrialityRotation ^ k`. -/
theorem exists_a5FourthD4CyclicSymmetryHom_eq_pow
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    ∃ k < 3,
      g.val = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ^ k ∧
        a5FourthD4CyclicSymmetryHom g = a5FourthD4TrialityRotation ^ k := by
  obtain ⟨k, hk, hgk⟩ : ∃ k < 3, g.val = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ^ k := by
    rcases (mem_symmetries_cyclic_a5FourthD4_iff g.val).mp g.property with h | h | h
    · exact ⟨0, by decide, h.trans (pow_zero _).symm⟩
    · exact ⟨1, by decide, h.trans (pow_one _).symm⟩
    · exact ⟨2, by decide, h⟩
  refine ⟨k, hk, hgk, ?_⟩
  rw [show g = ⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
      a5FourthD4BlockRotation_mem_symmetries⟩ ^ k from Subtype.ext hgk,
    map_pow, a5FourthD4CyclicSymmetryHom_blockRot]

/-- Every symmetry of the cyclic pattern `[2(024)0]` acts on `niemeierA5FourthD4` with
determinant `1`. -/
@[simp]
theorem det_a5FourthD4CyclicSymmetryHom
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    Isometry.det niemeierA5FourthD4 (a5FourthD4CyclicSymmetryHom g) = 1 := by
  obtain ⟨k, -, -, hg⟩ := exists_a5FourthD4CyclicSymmetryHom_eq_pow g
  rw [hg, map_pow, det_a5FourthD4TrialityRotation, one_pow]

/-- **The cyclic pattern `[2(024)0]` acts faithfully on `niemeierA5FourthD4`.** -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom :=
  (Subgroup.subtype_injective _).comp (MulEquiv.injective _)

end RootfulNiemeierType

end TauCeti
