/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.ScalarCenter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Frobenius

/-!
# The scalar denominator of the E7 fixed-point candidate

The native candidate is the intrinsic derived subgroup of the Steinberg fixed points modulo
its center. This file identifies that precise denominator: its members have scalar matrices,
and the scalar belongs to the field of definition. No order, perfectness, simplicity, or
identification of the minuscule carrier with the pinned Chevalley group is asserted.
-/

public section

namespace TauCeti.TypeE7LieIndex

variable (d : TypeE7LieIndex)

/-- The denominator of the native `E₇(q)` candidate consists exactly of the scalar elements
of the intrinsic derived subgroup of the Steinberg fixed points. -/
theorem mem_center_commutator_fixedSubgroup_steinberg_iff
    (g : commutator (fixedSubgroup d.steinberg)) :
    g ∈ Subgroup.center (commutator (fixedSubgroup d.steinberg)) ↔
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
          Matrix (Fin 56) (Fin 56) d.1.Closure) =
        ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
          Matrix (Fin 56) (Fin 56) d.1.Closure) 0 0 • 1 := by
  apply E7Minuscule.mem_center_commutator_iff_eq_smul_one
  intro i
  rw [steinberg_def]
  exact E7Minuscule.rootSubgroupPoints_one_mem_fixedSubgroup_frobenius _ _ _ i

/-- A central derived element is a scalar matrix with scalar in the field of definition. -/
theorem exists_scalar_mem_fixedField_of_mem_center_commutator_fixedSubgroup_steinberg
    (g : commutator (fixedSubgroup d.steinberg))
    (hg : g ∈ Subgroup.center (commutator (fixedSubgroup d.steinberg))) :
    ∃ c : d.1.fixedField,
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) = (c : d.1.Closure) • 1 := by
  have hfixed := (d.mem_fixedSubgroup_steinberg_iff g.val.val).mp g.val.property 0 0
  exact ⟨⟨_, hfixed⟩, (d.mem_center_commutator_fixedSubgroup_steinberg_iff g).mp hg⟩

end TauCeti.TypeE7LieIndex
