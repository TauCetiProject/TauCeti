/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# Compatibility of local-field structures in towers

For a tower `M/L/K`, where `K` and `L` are nonarchimedean local fields and `M/K` is algebraic,
the valuative relation and topology constructed on `M` do not depend on whether the construction
starts from `K` or from `L`. Thus constructions on algebraic subextensions can be compared without
postulating compatible structures on the top field.

The norms themselves are not asserted equal: the normalized absolute values on `K` and `L`
can have different normalizations. Uniqueness of the extended valuative relation identifies
their orders, and hence their topologies.

## Main results

* `TauCeti.algebraicExtensionValuativeRel_tower`: equality of the constructed valuative relations.
* `TauCeti.algebraicExtensionNormedFieldTopology_tower`: equality of the constructed topologies.
* `TauCeti.algebraicExtension_valuativeExtension_tower`: the construction over `K` also extends
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
  [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Algebra.IsAlgebraic K M]

/-- Extending the valuative relation through an intermediate local field agrees with
extending it directly from the base field. No valuative relation on `M` is assumed. -/
theorem algebraicExtensionValuativeRel_tower :
    letI := Algebra.IsAlgebraic.tower_top (K := K) (A := M) L
    algebraicExtensionValuativeRel K M = algebraicExtensionValuativeRel L M := by
  have := Algebra.IsAlgebraic.tower_top (K := K) (A := M) L
  let _ := algebraicExtensionValuativeRel L M
  have := algebraicExtension_valuativeExtension L M
  have := ValuativeExtension.trans K L M
  exact algebraicExtensionValuativeRel_eq K M

/-- The spectral-norm topology on an algebraic extension is unchanged when constructed through
an intermediate local field. No topology on `M` is assumed. -/
theorem algebraicExtensionNormedFieldTopology_tower :
    letI := Algebra.IsAlgebraic.tower_top (K := K) (A := M) L
    algebraicExtensionNormedFieldTopology K M = algebraicExtensionNormedFieldTopology L M := by
  have := Algebra.IsAlgebraic.tower_top (K := K) (A := M) L
  let _ := algebraicExtensionValuativeRel L M
  let _ := algebraicExtensionNormedFieldTopology L M
  have := algebraicExtension_isValuativeTopology L M
  have : ValuativeExtension K M := by
    have h := algebraicExtension_valuativeExtension K M
    rw [algebraicExtensionValuativeRel_tower K L M] at h
    exact h
  exact algebraicExtensionNormedFieldTopology_eq K M

/-- With the valuative relation constructed directly over `K`, the top field of an algebraic
tower is a valuative extension of the intermediate field as well. -/
theorem algebraicExtension_valuativeExtension_tower :
    let _ := algebraicExtensionValuativeRel K M
    ValuativeExtension L M := by
  have := Algebra.IsAlgebraic.tower_top (K := K) (A := M) L
  rw [algebraicExtensionValuativeRel_tower K L M]
  exact algebraicExtension_valuativeExtension L M

end TauCeti
