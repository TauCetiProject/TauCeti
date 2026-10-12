/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.DiscreteSubset

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

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {s : Set X} {a : X}

/-- A set whose inclusion tends to `a` along the cofinite filter is discrete once `a` is
removed. -/
theorem _root_.Filter.Tendsto.discreteTopology_diff_singleton
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) : DiscreteTopology ↥(s \ {a}) := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
  obtain ⟨U, V, hU, hV, haU, hxV, hUV⟩ := t2_separation (Ne.symm x.2.2)
  refine isOpen_singleton_of_finite_mem_nhds x
    ((hV.preimage continuous_subtype_val).mem_nhds hxV) ?_
  -- Only finitely many points of `s` lie outside `U`, and `V` is disjoint from `U`.
  refine ((eventually_cofinite.mp (h (hU.mem_nhds haU))).preimage
    (inclusion_injective sdiff_subset).injOn).subset fun y hy hyU ↦ ?_
  exact disjoint_left.mp hUV hyU hy

/-- **A set converging to `a` along the cofinite filter, with `a` added, is the one-point
compactification of its complement of `a`**: the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` that is
the inclusion on `s \ {a}` and sends `∞` to `a`. -/
noncomputable def _root_.Filter.Tendsto.onePointHomeomorphInsert
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) : OnePoint ↥(s \ {a}) ≃ₜ ↥(insert a s) :=
  haveI : CompactSpace ↥(insert a s) := isCompact_iff_compactSpace.mp
    (by simpa only [Subtype.range_coe] using h.isCompact_insert_range_of_cofinite)
  OnePoint.equivOfIsEmbeddingOfRangeEq ⟨a, mem_insert a s⟩
    (inclusion (sdiff_subset.trans (subset_insert a s))) (IsEmbedding.inclusion _) (by
      ext ⟨y, hy⟩
      simp only [range_inclusion, mem_ofPred_eq, Set.mem_sdiff, mem_singleton_iff, mem_compl_iff,
        Subtype.mk.injEq]
      exact ⟨fun hy' ↦ hy'.2, fun hya ↦ ⟨hy.resolve_left hya, hya⟩⟩)

/-- The homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` is the inclusion on `s \ {a}`. -/
@[simp]
theorem _root_.Filter.Tendsto.onePointHomeomorphInsert_apply_coe
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) (x : ↥(s \ {a})) :
    h.onePointHomeomorphInsert x = ⟨x, mem_insert_of_mem a x.2.1⟩ :=
  (rfl)

/-- The homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` sends the point at infinity to `a`. -/
@[simp]
theorem _root_.Filter.Tendsto.onePointHomeomorphInsert_apply_infty
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) :
    h.onePointHomeomorphInsert ∞ = ⟨a, mem_insert a s⟩ :=
  (rfl)

/-- The inverse of the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` sends `a` to the point at
infinity. -/
@[simp]
theorem _root_.Filter.Tendsto.onePointHomeomorphInsert_symm_apply_left
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) :
    h.onePointHomeomorphInsert.symm ⟨a, mem_insert a s⟩ = ∞ := by
  rw [Homeomorph.symm_apply_eq, h.onePointHomeomorphInsert_apply_infty]

/-- The inverse of the homeomorphism `(s \ {a})⁺ ≃ₜ insert a s` is the inclusion on the points
other than `a`. -/
@[simp]
theorem _root_.Filter.Tendsto.onePointHomeomorphInsert_symm_apply_of_ne
    (h : Tendsto ((↑) : s → X) cofinite (𝓝 a)) (y : ↥(insert a s)) (hy : (y : X) ≠ a) :
    h.onePointHomeomorphInsert.symm y =
      ((⟨y, y.2.resolve_left hy, hy⟩ : ↥(s \ {a})) : OnePoint ↥(s \ {a})) := by
  rw [Homeomorph.symm_apply_eq, h.onePointHomeomorphInsert_apply_coe]

end TauCeti
