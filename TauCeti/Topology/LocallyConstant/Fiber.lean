/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sets.Opens

/-!
# Fibers of a locally constant function as open sets

The fibers `f⁻¹{a}` of a locally constant function `f : X → α` are open
(`IsLocallyConstant.isOpen_fiber`). This file packages them as elements of `Opens X`
(`LocallyConstant.fiberOpens`), so that they can index restrictions of sheaves, and records that
they cover `X`.
-/

public section

open TopologicalSpace

namespace LocallyConstant

variable {X α : Type*} [TopologicalSpace X]

/-- The fiber `f⁻¹{a}` of a locally constant function `f`, as an open subset of `X`. -/
@[expose] def fiberOpens (f : LocallyConstant X α) (a : α) : Opens X :=
  ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩

@[simp]
theorem mem_fiberOpens {f : LocallyConstant X α} {a : α} {x : X} :
    x ∈ f.fiberOpens a ↔ f x = a :=
  Iff.rfl

@[simp]
theorem coe_fiberOpens (f : LocallyConstant X α) (a : α) :
    (f.fiberOpens a : Set X) = f ⁻¹' {a} :=
  rfl

/-- The fibers of a locally constant function cover its domain. -/
theorem iSup_fiberOpens (f : LocallyConstant X α) : ⨆ a, f.fiberOpens a = ⊤ :=
  top_unique fun x _ ↦ Opens.mem_iSup.2 ⟨f x, rfl⟩

end LocallyConstant
