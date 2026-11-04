/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sets.Closeds

/-!
# Fibers of a locally constant function as clopen sets

The fibers `f⁻¹{a}` of a locally constant function `f : X → α` are clopen
(`IsLocallyConstant.isClopen_fiber`). This file packages them as elements of `Clopens X`
(`LocallyConstant.fiberClopens`). Their underlying open sets `(f.fiberClopens a).toOpens` can
index restrictions of sheaves, and they cover `X`. Their preimages under a continuous map `g` are
the fibers of `f ∘ g` (`LocallyConstant.comap_toOpens_fiberClopens`).
-/

public section

open TopologicalSpace

namespace LocallyConstant

variable {X α : Type*} [TopologicalSpace X]

/-- The fiber `f⁻¹{a}` of a locally constant function `f`, as a clopen subset of `X`. -/
def fiberClopens (f : LocallyConstant X α) (a : α) : Clopens X :=
  ⟨f ⁻¹' {a}, f.isLocallyConstant.isClopen_fiber a⟩

@[simp]
theorem mem_fiberClopens {f : LocallyConstant X α} {a : α} {x : X} :
    x ∈ f.fiberClopens a ↔ f x = a :=
  (Iff.rfl)

@[simp]
theorem coe_fiberClopens (f : LocallyConstant X α) (a : α) :
    (f.fiberClopens a : Set X) = f ⁻¹' {a} :=
  (rfl)

/-- The fibers of a locally constant function, as open sets, cover its domain. -/
theorem iSup_toOpens_fiberClopens (f : LocallyConstant X α) :
    ⨆ a, (f.fiberClopens a).toOpens = ⊤ :=
  top_unique fun x _ ↦ Opens.mem_iSup.2 ⟨f x, mem_fiberClopens.2 rfl⟩

/-- The preimage under a continuous map `g` of the fiber of `f` over `a` is the fiber of `f ∘ g`
over `a`. -/
theorem comap_toOpens_fiberClopens {Y : Type*} [TopologicalSpace Y] (g : C(Y, X))
    (f : LocallyConstant X α) (a : α) :
    Opens.comap g (f.fiberClopens a).toOpens = ((f.comap g).fiberClopens a).toOpens :=
  Opens.ext (by ext; simp)

end LocallyConstant
