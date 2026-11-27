/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MazurFiniteness
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.NumberTheory.LocalField.Cohomology
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit

/-!
# Mazur's finiteness condition for local Galois groups

Every open subgroup of the absolute Galois group of a nonarchimedean local field `K` is the
absolute Galois group of its fixed field (`absoluteGaloisGroupEquivFixingSubgroup`). This finite
extension is itself a local field. The finiteness of its degree-one Galois cohomology
(`finite_cohomFp_one_absoluteGaloisGroup`) gives finiteness of its continuous `ℤ/p`-valued
characters when `p` is nonzero in `K`. For prime `p` this is Mazur's finiteness hypothesis for
deformations of residual representations in characteristic `p`.

## References

* T. Gee, *Modularity lifting theorems*, Essential Number Theory 1 (2022), §3.1.
* M. Kisin, *Lectures on deformations of Galois representations*, Lecture 1, (1.2).
-/

public section

namespace TauCeti

open IntermediateField

/-- The absolute Galois group of a nonarchimedean local field satisfies Mazur's finiteness
condition at every `p` nonzero in the field. In characteristic zero this includes every prime,
including the residue characteristic. -/
theorem mazurFiniteness_absoluteGaloisGroup (p : ℕ) (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [NeZero (p : K)] :
    MazurFiniteness p (Field.absoluteGaloisGroup K) := by
  refine (absoluteGaloisGroupRestrictEquiv K).mazurFiniteness_iff.mpr
    (mazurFiniteness_iff_forall_finite.mpr fun U ↦ ?_)
  let L := fixedField U.toSubgroup
  let := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have : NeZero (p : L) := NeZero.nat_of_injective (algebraMap K L).injective
  have hU : L.val.fieldRange.fixingSubgroup = U.toSubgroup := by
    rw [fieldRange_val, toSubgroup_eq_fixingSubgroup_of_fixedField_eq (E := L) rfl]
  let e : Field.absoluteGaloisGroup L ≃ₜ* U.toSubgroup := hU ▸
    (absoluteGaloisGroupRestrictEquiv L).trans (absoluteGaloisGroupEquivFixingSubgroup K L L.val)
  have : Finite (continuousZModDual p (Field.absoluteGaloisGroup L)) := Finite.of_equiv _
    (cohomFpLinearEquivContinuousZModDual p (Field.absoluteGaloisGroup L)).toEquiv
  exact Finite.of_injective _ e.continuousZModDualMap_bijective.1

end TauCeti
