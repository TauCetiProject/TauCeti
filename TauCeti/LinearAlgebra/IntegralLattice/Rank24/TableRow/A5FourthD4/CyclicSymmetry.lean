/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.A5FourthD4.Basic

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

/-! ### Faithful action of `[2(024)0].symmetries` on `niemeierA5FourthD4` -/

private noncomputable def a5FourthD4BlockRotationFin :
    Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length) :=
  (finCongr (length_eq_of_mem_gluePatterns cyclic_mem_gluePatterns_a5FourthD4)).symm.permCongr
    a5FourthD4BlockRotation

private theorem a5FourthD4BlockRotationFin_eq :
    a5FourthD4BlockRotationFin = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) :=
  -- Both `(GluePattern.cyclic [2] [0, 2, 4] [0]).length` and `a5FourthD4.components.length`
  -- reduce definitionally to `5`, so the `finCongr` casts act as the identity.
  Equiv.ext fun _ ↦ Fin.ext rfl

private theorem orderOf_a5FourthD4BlockRotationFin : orderOf a5FourthD4BlockRotationFin = 3 := by
  change orderOf ((finCongr (length_eq_of_mem_gluePatterns
    cyclic_mem_gluePatterns_a5FourthD4)).symm.permCongrHom a5FourthD4BlockRotation) = 3
  rw [MulEquiv.orderOf_eq, orderOf_a5FourthD4BlockRotation]

private theorem mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers
    (g : Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g ∈ Subgroup.zpowers a5FourthD4BlockRotationFin := by
  let e := (finCongr (length_eq_of_mem_gluePatterns
    cyclic_mem_gluePatterns_a5FourthD4)).permCongrHom.toMonoidHom
  have he : e a5FourthD4BlockRotationFin = a5FourthD4BlockRotation :=
    (finCongr (length_eq_of_mem_gluePatterns
      cyclic_mem_gluePatterns_a5FourthD4)).permCongrHom.apply_symm_apply a5FourthD4BlockRotation
  rw [← Subgroup.mem_map_iff_mem (f := e)
      ((finCongr (length_eq_of_mem_gluePatterns
        cyclic_mem_gluePatterns_a5FourthD4)).permCongrHom.injective),
    map_symmetries_cyclic_a5FourthD4, ← he, ← MonoidHom.map_zpowers,
    Subgroup.mem_map_iff_mem ((finCongr (length_eq_of_mem_gluePatterns
      cyclic_mem_gluePatterns_a5FourthD4)).permCongrHom.injective)]

private theorem mem_symmetries_cyclic_a5FourthD4_iff_fin
    (g : Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = a5FourthD4BlockRotationFin ∨ g = a5FourthD4BlockRotationFin ^ 2 := by
  rw [mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers, mem_zpowers_iff_mem_range_orderOf,
    orderOf_a5FourthD4BlockRotationFin]
  simp only [Finset.range_add_one, Finset.range_zero, Finset.mem_image, Finset.mem_insert,
    Finset.notMem_empty, exists_eq_or_imp, pow_zero, pow_one]
  tauto

private theorem a5FourthD4BlockRotationFin_mem_symmetries :
    a5FourthD4BlockRotationFin ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries :=
  (mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers _).mpr (Subgroup.mem_zpowers _)

/-- **The symmetries of the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`** are `1`,
`a5FourthD4BlockRotation`, and `a5FourthD4BlockRotation ^ 2`. -/
theorem mem_symmetries_cyclic_a5FourthD4_iff (g : Equiv.Perm (Fin 5)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ∨
        g = (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ^ 2 := by
  -- Both `(GluePattern.cyclic [2] [0, 2, 4] [0]).length` and `a5FourthD4.components.length`
  -- reduce definitionally to `5`.
  rw [← a5FourthD4BlockRotationFin_eq]
  exact mem_symmetries_cyclic_a5FourthD4_iff_fin g

/-- `a5FourthD4BlockRotation` belongs to the symmetry group of the cyclic pattern `[2(024)0]`. -/
theorem a5FourthD4BlockRotation_mem_symmetries :
    (a5FourthD4BlockRotation : Equiv.Perm (Fin 5)) ∈
      (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries := by
  -- `a5FourthD4.components.length` reduces definitionally to `5`.
  exact a5FourthD4BlockRotationFin_eq ▸ a5FourthD4BlockRotationFin_mem_symmetries

private theorem forall_mem_zpowers_a5FourthD4BlockRotation
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    g ∈ Subgroup.zpowers
      (⟨a5FourthD4BlockRotationFin, a5FourthD4BlockRotationFin_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((mem_symmetries_cyclic_a5FourthD4_iff_mem_zpowers g.val).mp g.property)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩

private theorem orderOf_a5FourthD4BlockRotation_mk_eq_orderOf_a5FourthD4TrialityIsometry_mk :
    orderOf (⟨a5FourthD4BlockRotationFin, a5FourthD4BlockRotationFin_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) =
      orderOf (⟨a5FourthD4TrialityIsometry, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers a5FourthD4TrialityIsometry) := by
  rw [Subgroup.orderOf_mk, orderOf_a5FourthD4BlockRotationFin,
    ← orderOf_a5FourthD4TrialityIsometry, Subgroup.orderOf_mk]

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
theorem a5FourthD4CyclicSymmetryHom_blockRotation :
    a5FourthD4CyclicSymmetryHom
        ⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
          a5FourthD4BlockRotation_mem_symmetries⟩ =
      a5FourthD4TrialityIsometry := by
  -- `a5FourthD4.components.length` reduces definitionally to `5`.
  have hgen : (⟨(a5FourthD4BlockRotation : Equiv.Perm (Fin 5)),
      a5FourthD4BlockRotation_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) =
      ⟨a5FourthD4BlockRotationFin, a5FourthD4BlockRotationFin_mem_symmetries⟩ :=
    Subtype.ext a5FourthD4BlockRotationFin_eq.symm
  rw [hgen]
  simp [a5FourthD4CyclicSymmetryHom, mulEquivOfOrderOfEq_apply_gen]

/-- **The cyclic pattern `[2(024)0]` acts faithfully on `niemeierA5FourthD4`.** -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom :=
  (Subgroup.subtype_injective _).comp (MulEquiv.injective _)

end RootfulNiemeierType

end TauCeti
