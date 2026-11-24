/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
import TauCeti.Topology.DiscreteSubset

/-!
# A set converging along the cofinite filter is a one-point compactification

Let `s` be a subset of a Hausdorff space `X` whose inclusion tends to a point `a` along the
cofinite filter: every neighbourhood of `a` contains all but finitely many points of `s`. Away
from `a` the set `s` is then discrete (`Filter.Tendsto.discreteTopology_diff_singleton`), and
adding `a` to it produces a compact space in which `a` is the only point that may be non-isolated,
so `insert a s` is the one-point compactification of the discrete space `s \ {a}`, with `a` as the
point at infinity (`Filter.Tendsto.onePointHomeomorphInsert`).

This is the topological form of a set converging to `1` in a profinite group: for such a set `s`,
the pointed space `(insert 1 s, 1)` is the pointed one-point compactification `((s \ {1})⁺, ∞)`,
which is what identifies the free pro-`p` group on it with the free pro-`p` group on a pointed
one-point compactification.

## Main results

* `Filter.Tendsto.discreteTopology_diff_singleton`: a set converging to `a` along the cofinite
  filter is discrete once `a` is removed.
* `Filter.Tendsto.onePointHomeomorphInsert`: the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` sending
  `∞` to `a`.
-/

public section

open Filter Set Topology
open scoped OnePoint

namespace Filter.Tendsto

variable {X : Type*} [TopologicalSpace X] [T2Space X] {s : Set X} {a : X}

/-- A set whose inclusion tends to `a` along the cofinite filter is discrete once `a` is
removed. -/
theorem discreteTopology_diff_singleton
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) : DiscreteTopology ↥(s \ {a}) :=
  discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    -- The inclusion of `s \ {a}` into `X` factors through `s`, so it also tends to `a`.
    have h' := h.comp (inclusion_injective (sdiff_subset (t := {a}))).tendsto_cofinite
    rw [val_comp_inclusion] at h'
    exact h'.isOpen_singleton_of_cofinite continuous_subtypeVal.continuousAt x.property.2

/-- **A set converging to `a` along the cofinite filter, with `a` added, is the one-point
compactification of its complement of `a`**: the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` that is
the inclusion on `s \ {a}` and sends `∞` to `a`. -/
noncomputable def onePointHomeomorphInsert
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) : OnePoint ↥(s \ {a}) ≃ₜ ↥(insert a s) :=
  haveI : CompactSpace ↥(insert a s) := isCompact_iff_compactSpace.mp
    (by simpa only [Subtype.range_coe] using h.isCompact_insert_range_of_cofinite)
  OnePoint.equivOfIsEmbeddingOfRangeEq ⟨a, mem_insert a s⟩
    (inclusion (sdiff_subset.trans (subset_insert a s))) (IsEmbedding.inclusion _) (by
      ext
      simp only [range_inclusion]
      grind)

/-- The homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` is the inclusion on `s \ {a}`. -/
@[simp]
theorem onePointHomeomorphInsert_apply_coe
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) (x : ↥(s \ {a})) :
    h.onePointHomeomorphInsert x = ⟨x, mem_insert_of_mem a x.property.1⟩ :=
  (rfl)

/-- The homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` sends the point at infinity to `a`. -/
@[simp]
theorem onePointHomeomorphInsert_apply_infty
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) :
    h.onePointHomeomorphInsert ∞ = ⟨a, mem_insert a s⟩ :=
  (rfl)

/-- The inverse of the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` sends `a` to the point at
infinity. -/
@[simp]
theorem onePointHomeomorphInsert_symm_apply_left
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) :
    h.onePointHomeomorphInsert.symm ⟨a, mem_insert a s⟩ = ∞ := by
  rw [Homeomorph.symm_apply_eq, h.onePointHomeomorphInsert_apply_infty]

/-- The inverse of the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` is the inclusion on the points
other than `a`. -/
@[simp]
theorem onePointHomeomorphInsert_symm_apply_of_ne
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) (y : ↥(insert a s)) (hy : (y : X) ≠ a) :
    h.onePointHomeomorphInsert.symm y =
      ((⟨y, y.property.resolve_left hy, hy⟩ : ↥(s \ {a})) : OnePoint ↥(s \ {a})) := by
  rw [Homeomorph.symm_apply_eq, h.onePointHomeomorphInsert_apply_coe]

end Filter.Tendsto
