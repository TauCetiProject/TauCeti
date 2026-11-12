/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.ScalarCenter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Frobenius

/-!
# The centre of the derived Steinberg fixed points of `E₇(q)`

`TauCeti.TypeE7LieIndex.Group`, the candidate group `FixedPointCandidate d.steinberg` attached to
an `E₇` index `d`, is the derived subgroup of the Steinberg fixed points modulo the centre of that
derived subgroup. This file identifies that centre: its members have scalar matrices, and the
scalar lies in the field of definition. No order, perfectness, simplicity, or identification of
the minuscule carrier with the pinned Chevalley group is asserted.

## Main results

* `TauCeti.TypeE7LieIndex.mem_center_commutator_fixedSubgroup_steinberg_iff`: the centre of the
  derived subgroup of the Steinberg fixed points consists exactly of its scalar elements.
* `exists_scalar_mem_fixedField_of_mem_center_commutator_fixedSubgroup_steinberg`, in the same
  namespace: such a scalar lies in the field of definition.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 11, for the centre and perfectness of the
  Chevalley groups.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.TypeE7LieIndex

variable (d : TypeE7LieIndex)

/-- The centre of the derived subgroup of the Steinberg fixed points, the subgroup
`TauCeti.TypeE7LieIndex.Group` quotients by, consists exactly of its scalar elements. -/
theorem mem_center_commutator_fixedSubgroup_steinberg_iff
    (g : commutator (fixedSubgroup d.steinberg)) :
    g ∈ Subgroup.center (commutator (fixedSubgroup d.steinberg)) ↔
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
          Matrix (Fin 56) (Fin 56) d.1.Closure) =
        ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
          Matrix (Fin 56) (Fin 56) d.1.Closure) 0 0 • 1 := by
  revert g
  rw [steinberg_def]
  exact E7Minuscule.mem_center_commutator_fixedSubgroup_frobenius_iff _ _ _

/-- A central element of the derived Steinberg fixed points is a scalar matrix whose scalar lies
in the field of definition. -/
theorem exists_scalar_mem_fixedField_of_mem_center_commutator_fixedSubgroup_steinberg
    (g : commutator (fixedSubgroup d.steinberg))
    (hg : g ∈ Subgroup.center (commutator (fixedSubgroup d.steinberg))) :
    ∃ c : d.1.fixedField,
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) = (c : d.1.Closure) • 1 := by
  have hfixed := (d.mem_fixedSubgroup_steinberg_iff g.val.val).mp g.val.property 0 0
  exact ⟨⟨_, hfixed⟩, (d.mem_center_commutator_fixedSubgroup_steinberg_iff g).mp hg⟩

end TauCeti.TypeE7LieIndex
