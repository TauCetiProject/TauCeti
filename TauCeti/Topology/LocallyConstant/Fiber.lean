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
(`IsLocallyConstant.isClopen_fiber`). Because these open fibers cover `X`, a map out of `X` is
continuous if and only if its restriction to each fiber is continuous
(`IsLocallyConstant.continuous_iff`), and likewise for joint fibers of two locally constant
functions (`IsLocallyConstant.continuous_iff₂`).

This file also packages the fibers of `f : LocallyConstant X α` as elements of `Clopens X`
(`LocallyConstant.fiberClopens`). Their underlying open sets `(f.fiberClopens a).toOpens` can
index restrictions of sheaves, and they cover `X`. Their preimages under a continuous map `g` are
the fibers of `f ∘ g` (`LocallyConstant.comap_toOpens_fiberClopens`).
-/

public section

open TopologicalSpace

namespace IsLocallyConstant

/-- A map out of `X` is continuous if and only if its restriction to each fiber of a locally
constant function `f : X → α` is continuous. -/
theorem continuous_iff {X α T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {f : X → α} (hf : IsLocallyConstant f) {g : X → T} :
    Continuous g ↔ ∀ a : α, Continuous (fun x : {x : X // f x = a} => g x.1) := by
  refine ⟨fun hg _ => hg.comp continuous_subtype_val, fun hg => ?_⟩
  exact continuous_of_cover_nhds (s := fun a => {x : X | f x = a})
    (fun x => ⟨f x, (hf.isOpen_fiber (f x)).mem_nhds rfl⟩)
    (fun a => continuousOn_iff_continuous_domRestrict.2 (hg a))

/-- A map out of `X` is continuous if and only if its restriction to each joint fiber of two
locally constant functions `f₁ : X → α` and `f₂ : X → β` is continuous. -/
theorem continuous_iff₂ {X α β T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {f₁ : X → α} {f₂ : X → β} (hf₁ : IsLocallyConstant f₁) (hf₂ : IsLocallyConstant f₂)
    {g : X → T} :
    Continuous g ↔
      ∀ (a : α) (b : β), Continuous (fun x : {x : X // f₁ x = a ∧ f₂ x = b} => g x.1) := by
  rw [(hf₁.prodMk hf₂).continuous_iff, Prod.forall]
  exact forall₂_congr fun a b =>
    ⟨fun h => h.comp ((continuous_subtype_val (p := fun x => f₁ x = a ∧ f₂ x = b)).subtype_mk
        fun x => Prod.ext x.2.1 x.2.2),
     fun h => h.comp ((continuous_subtype_val
        (p := fun x => (fun y => (f₁ y, f₂ y)) x = (a, b))).subtype_mk
        fun x => ⟨congrArg Prod.fst x.2, congrArg Prod.snd x.2⟩)⟩

end IsLocallyConstant

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
