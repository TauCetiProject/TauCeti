/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Roots of a polynomial in an intermediate field

For an intermediate field `L` of `E / K` and a polynomial `p` over `K`, the roots of `p` in `L`,
with multiplicities, are the roots of `p` in `E` that lie in `L`. This is Mathlib's
`Polynomial.filter_roots_map_range_eq_map_roots` for the inclusion `L → E`, whose range is `L`.
It lets root counts in different subfields of one ambient field be compared inside that field.
-/

public section

open Polynomial

namespace IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The roots in `E` of a polynomial over `K` that lie in an intermediate field `L` are its roots
in `L`, with the same multiplicities. -/
theorem filter_aroots_eq_map_aroots (L : IntermediateField K E) (p : K[X])
    [DecidablePred (· ∈ L)] :
    (p.aroots E).filter (· ∈ L) = (p.aroots L).map (↑) := by
  classical
  have h := filter_roots_map_range_eq_map_roots (algebraMap L E).injective
    (p.map (algebraMap K L))
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, ← aroots_def, ← aroots_def] at h
  convert h using 1
  · exact Multiset.filter_congr fun x _ ↦ ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩
  · exact Multiset.map_congr rfl fun x _ ↦ (algebraMap_apply L x).symm

end IntermediateField
