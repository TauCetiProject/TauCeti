/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import TauCeti.NumberTheory.LocalField.Norm.Open

/-!
# Local norm subgroups

An open normal subgroup `V` of the absolute Galois group of a nonarchimedean local field cuts out
the finite Galois extension `classField K V`. This file attaches to `V` the concrete norm subgroup
`N_{classField K V/K}(classField K V)ˣ` of `Kˣ` and proves that it is open and has finite index.

The topology statement is inherited from the local inverse-function theorem for the field norm;
finite index follows from the valuation--unit decomposition of `Kˣ`.

## Main definitions

* `TauCeti.ClassFieldTheory.localNormSubgroup`: the norm subgroup of the class field cut out by an
  open normal subgroup of the absolute Galois group.

## Main results

* `TauCeti.ClassFieldTheory.isOpen_localNormSubgroup`: local norm subgroups are open.
* `TauCeti.ClassFieldTheory.finiteIndex_localNormSubgroup`: local norm subgroups have finite index.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ValuativeRel

variable (K : Type*) [Field K]

/-- **The local norm subgroup cut out by an open normal subgroup.** It is the image in `Kˣ` of
the field norm from the finite Galois extension `classField K V`. -/
def localNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) : Subgroup Kˣ :=
  normGroup K (classField K V)

/-- The local norm subgroup of `V` is the norm group of the class field `classField K V`. -/
theorem localNormSubgroup_def (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    localNormSubgroup K V = normGroup K (classField K V) :=
  (rfl)

/-- Membership in a local norm subgroup means being the norm of a nonzero element of the
corresponding class field. -/
@[simp]
theorem mem_localNormSubgroup_iff {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {x : Kˣ} :
    x ∈ localNormSubgroup K V ↔
      ∃ y : (classField K V)ˣ, Algebra.norm K (y : classField K V) = x := by
  rw [localNormSubgroup_def, mem_normGroup_iff]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Local norm subgroups are open.** -/
theorem isOpen_localNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    IsOpen ((localNormSubgroup K V : Subgroup Kˣ) : Set Kˣ) := by
  rw [localNormSubgroup_def]
  exact isOpen_normGroup

/-- **Local norm subgroups have finite index.** -/
theorem finiteIndex_localNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (localNormSubgroup K V).FiniteIndex := by
  rw [localNormSubgroup_def]
  exact finiteIndex_normGroup

end TauCeti.ClassFieldTheory
