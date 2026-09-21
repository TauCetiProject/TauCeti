/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Compatibility of local-field structures in towers

For a finite tower `M/L/K` of extensions of a nonarchimedean local field, the valuative
relation and topology constructed on `M` do not depend on whether the construction starts
from `K` or from `L`. Thus constructions on finite subextensions can be compared without
postulating compatible structures on the top field.

The norms themselves are not asserted equal: the normalized absolute values on `K` and `L`
can have different normalizations. Uniqueness of the extended valuative relation identifies
their orders, and hence their topologies.

## Main results

* `TauCeti.finiteExtensionValuativeRel_tower`: equality of the constructed valuative relations.
* `TauCeti.finiteExtensionNormedFieldTopology_tower`: equality of the constructed topologies.
* `TauCeti.finiteExtension_valuativeExtension_tower`: the construction over `K` also extends
  the valuative relation on `L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (uniqueness of extended valuations).
-/

public section

namespace TauCeti

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
  [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Module.Finite K M]

/-- Extending the valuative relation through an intermediate local field agrees with
extending it directly from the base field. No valuative relation on `M` is assumed. -/
theorem finiteExtensionValuativeRel_tower :
    letI := Module.Finite.of_restrictScalars_finite K L M
    finiteExtensionValuativeRel K M = finiteExtensionValuativeRel L M := by
  have := Module.Finite.of_restrictScalars_finite K L M
  let _ := finiteExtensionValuativeRel L M
  have := finiteExtension_valuativeExtension L M
  have := ValuativeExtension.trans K L M
  exact finiteExtensionValuativeRel_eq K M

/-- The spectral-norm topology on a finite extension is unchanged when constructed through
an intermediate local field. No topology on `M` is assumed. -/
theorem finiteExtensionNormedFieldTopology_tower :
    letI := Module.Finite.of_restrictScalars_finite K L M
    finiteExtensionNormedFieldTopology K M = finiteExtensionNormedFieldTopology L M := by
  have := Module.Finite.of_restrictScalars_finite K L M
  let _ := finiteExtensionValuativeRel L M
  let _ := finiteExtensionNormedFieldTopology L M
  have := finiteExtension_isValuativeTopology L M
  have : ValuativeExtension K M := by
    have h := finiteExtension_valuativeExtension K M
    rw [finiteExtensionValuativeRel_tower K L M] at h
    exact h
  exact finiteExtensionNormedFieldTopology_eq K M

/-- With the valuative relation constructed directly over `K`, the top field of a finite
tower is a valuative extension of the intermediate field as well. -/
theorem finiteExtension_valuativeExtension_tower :
    let _ := finiteExtensionValuativeRel K M
    ValuativeExtension L M := by
  have := Module.Finite.of_restrictScalars_finite K L M
  rw [finiteExtensionValuativeRel_tower K L M]
  exact finiteExtension_valuativeExtension L M

end TauCeti
