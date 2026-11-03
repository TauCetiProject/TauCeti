/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smoothness at a point of a map out of a disjoint union

A map `Sum.elim f g` out of the disjoint union `M ⊕ M'` of two manifolds is `C^n` at a point
`Sum.inl x` exactly when `f` is `C^n` at `x`, and at `Sum.inr y` exactly when `g` is `C^n` at `y`:
each summand is an open submanifold. Mathlib states the global form, `ContMDiff.sumElim`; these are
the pointwise forms, which let smoothness of a map out of a disjoint union be checked one summand
at a time where `f` or `g` is only known to be `C^n` near some points.

## Main results

* `TauCeti.contMDiffAt_sumElim_inl`, `TauCeti.contMDiffAt_sumElim_inr`: `Sum.elim f g` is `C^n` at
  a point of a summand exactly when its restriction to that summand is.
-/

public section

open Set Filter Topology
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
  {f : M → N} {g : M' → N}

/-- A map out of a disjoint union is `C^n` at a point of the first summand exactly when its
restriction to the first summand is. -/
@[simp]
theorem contMDiffAt_sumElim_inl {x : M} :
    ContMDiffAt I J n (Sum.elim f g) (.inl x) ↔ ContMDiffAt I J n f x := by
  refine ⟨fun h ↦ h.comp x ContMDiff.inl.contMDiffAt, fun h ↦ ?_⟩
  -- On the open set `range Sum.inl`, the map is `f` after the smooth retraction onto `M`.
  have hr : ContMDiffAt I I n (Sum.elim id fun _ ↦ x : M ⊕ M' → M) (.inl x) :=
    (contMDiff_id.sumElim contMDiff_const).contMDiffAt
  refine (h.comp (Sum.inl x) hr).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_range_inl.mem_nhds (mem_range_self x)] with _ hz
  obtain ⟨_, rfl⟩ := hz
  rfl

/-- A map out of a disjoint union is `C^n` at a point of the second summand exactly when its
restriction to the second summand is. -/
@[simp]
theorem contMDiffAt_sumElim_inr {y : M'} :
    ContMDiffAt I J n (Sum.elim f g) (.inr y) ↔ ContMDiffAt I J n g y := by
  refine ⟨fun h ↦ h.comp y ContMDiff.inr.contMDiffAt, fun h ↦ ?_⟩
  -- On the open set `range Sum.inr`, the map is `g` after the smooth retraction onto `M'`.
  have hr : ContMDiffAt I I n (Sum.elim (fun _ ↦ y) id : M ⊕ M' → M') (.inr y) :=
    (contMDiff_const.sumElim contMDiff_id).contMDiffAt
  refine (h.comp (Sum.inr y) hr).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_range_inr.mem_nhds (mem_range_self y)] with _ hz
  obtain ⟨_, rfl⟩ := hz
  rfl

end TauCeti
