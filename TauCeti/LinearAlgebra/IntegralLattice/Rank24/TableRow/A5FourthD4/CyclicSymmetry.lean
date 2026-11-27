/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.A5FourthD4

import TauCeti.Data.Fin.Cast
import TauCeti.GroupTheory.Perm.PermCongr

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
order-three self-isometry `TauCeti.RootfulNiemeierType.a5FourthD4TrialityIsometry`
of `TauCeti.niemeierA5FourthD4`.  This yields a faithful action
`TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom` of the cyclic pattern's symmetry group on
`niemeierA5FourthD4`.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4TrialityIsometry_apply_zero`,
  `TauCeti.RootfulNiemeierType.a5FourthD4TrialityIsometry_apply_one`,
  `TauCeti.RootfulNiemeierType.a5FourthD4TrialityIsometry_apply_two`,
  `TauCeti.RootfulNiemeierType.a5FourthD4TrialityIsometry_apply_three`:
  `A₅`-coordinate corollaries for `TauCeti.RootfulNiemeierType.a5FourthD4TrialityIsometry`.
* `TauCeti.RootfulNiemeierType.mem_symmetries_cyclic_a5FourthD4_iff`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom_injective`: membership characterization
  and faithful action of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` on
  `niemeierA5FourthD4`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### `A₅`-coordinate corollaries for `a5FourthD4TrialityIsometry` -/

private theorem a5FourthD4TrialityIsometry_apply_of_eq
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ)
    {k b : Fin a5FourthD4.components.length}
    (hk : k ≠ a5FourthD4D4Index) (hkb : a5FourthD4BlockRotation.symm k = b)
    (hb : (a5FourthD4.componentType k).rank = (a5FourthD4.componentType b).rank := by rfl) :
    a5FourthD4TrialityIsometry x k = fun j ↦ x b (Fin.cast hb j) := by
  funext j
  exact (a5FourthD4TrialityIsometry_apply_of_ne x hk j).trans
    (Fin.apply_cast_eq_apply_cast x hkb _ hb j)

@[simp]
theorem a5FourthD4TrialityIsometry_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityIsometry x (0 : Fin 5) = x (0 : Fin 5) :=
  a5FourthD4TrialityIsometry_apply_of_eq x (k := ⟨0, by decide⟩) (b := ⟨0, by decide⟩)
    (by decide) (by rw [Fin.mk_zero', a5FourthD4BlockRotation_symm_apply_zero])

@[simp]
theorem a5FourthD4TrialityIsometry_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityIsometry x (1 : Fin 5) = x (3 : Fin 5) :=
  a5FourthD4TrialityIsometry_apply_of_eq x (k := ⟨1, by decide⟩) (b := ⟨3, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_one (by decide))

@[simp]
theorem a5FourthD4TrialityIsometry_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityIsometry x (2 : Fin 5) = x (1 : Fin 5) :=
  a5FourthD4TrialityIsometry_apply_of_eq x (k := ⟨2, by decide⟩) (b := ⟨1, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_two (by decide))

@[simp]
theorem a5FourthD4TrialityIsometry_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityIsometry x (3 : Fin 5) = x (2 : Fin 5) :=
  a5FourthD4TrialityIsometry_apply_of_eq x (k := ⟨3, by decide⟩) (b := ⟨2, by decide⟩)
    (by decide) (a5FourthD4BlockRotation_symm_apply_mk_three (by decide))

/-! ### Faithful action of `[2(024)0].symmetries` on `niemeierA5FourthD4` -/

private theorem mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers
    (g : Equiv.Perm (Fin a5FourthD4.components.length)) :
    -- Align the definitionally equal `Fin 5` index types for `Subgroup.mem_map_iff_mem`.
    (show Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length) from g) ∈
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g ∈ Subgroup.zpowers a5FourthD4BlockRotation := by
  have he : (finCongr (length_eq_of_mem_gluePatterns
      cyclic_mem_gluePatterns_a5FourthD4)).permCongr
        (show Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length) from g) = g := by
    ext x
    rfl
  rw [← map_symmetries_cyclic_a5FourthD4, ← he]
  exact (Subgroup.mem_map_iff_mem (f := (finCongr (length_eq_of_mem_gluePatterns
    cyclic_mem_gluePatterns_a5FourthD4)).permCongrHom.toMonoidHom)
    (MulEquiv.injective _)).symm

/-- **The symmetries of the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`** are `1`,
`a5FourthD4BlockRotation`, and `a5FourthD4BlockRotation ^ 2`. -/
theorem mem_symmetries_cyclic_a5FourthD4_iff (g : Equiv.Perm (Fin 5)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ∨
        g = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ^ 2 := by
  let g' : Equiv.Perm (Fin a5FourthD4.components.length) := g
  refine (mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers g').trans ?_
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_a5FourthD4BlockRotation]
  simp only [Finset.range_add_one, Finset.range_zero, Finset.mem_image, Finset.mem_insert,
    Finset.notMem_empty, exists_eq_or_imp, pow_zero, pow_one]
  tauto

/-- `a5FourthD4BlockRotation` belongs to the symmetry group of the cyclic pattern `[2(024)0]`. -/
theorem a5FourthD4BlockRotation_mem_symmetries :
    (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ∈
      (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries :=
  (mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers _).mpr (Subgroup.mem_zpowers _)

private theorem forall_mem_zpowers_a5FourthD4BlockRotation
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    g ∈ Subgroup.zpowers
      (⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
        a5FourthD4BlockRotation_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers g.val).mp g.property)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩

private theorem orderOf_a5FourthD4BlockRotation_mk_eq_orderOf_a5FourthD4TrialityIsometry_mk :
    orderOf (⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
        a5FourthD4BlockRotation_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) =
      orderOf (⟨a5FourthD4TrialityIsometry, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers a5FourthD4TrialityIsometry) :=
  (Subgroup.orderOf_mk (a5FourthD4BlockRotation : Equiv.Perm (Fin 5))
      a5FourthD4BlockRotation_mem_symmetries).trans
    ((show orderOf (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) = 3 from
        orderOf_a5FourthD4BlockRotation).trans
      (orderOf_a5FourthD4TrialityIsometry.symm.trans (Subgroup.orderOf_mk _ _).symm))

/-- **The indicated symmetry group of `[2(024)0]` acts on `niemeierA5FourthD4`** by powers of
`a5FourthD4TrialityIsometry`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  (Subgroup.zpowers a5FourthD4TrialityIsometry).subtype.comp
    (mulEquivOfOrderOfEq forall_mem_zpowers_a5FourthD4BlockRotation
      (Subgroup.forall_zpowers.mpr fun m ↦ ⟨m, rfl⟩)
      orderOf_a5FourthD4BlockRotation_mk_eq_orderOf_a5FourthD4TrialityIsometry_mk).toMonoidHom

/-- The generator `a5FourthD4BlockRotation` of `[2(024)0].symmetries` acts as
`a5FourthD4TrialityIsometry`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_blockRot :
    a5FourthD4CyclicSymmetryHom
        ⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
          a5FourthD4BlockRotation_mem_symmetries⟩ =
      a5FourthD4TrialityIsometry := by
  simp [a5FourthD4CyclicSymmetryHom, mulEquivOfOrderOfEq_apply_gen]

/-- **The cyclic pattern `[2(024)0]` acts faithfully on `niemeierA5FourthD4`.** -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom :=
  (Subgroup.subtype_injective _).comp (MulEquiv.injective _)

end RootfulNiemeierType

end TauCeti
