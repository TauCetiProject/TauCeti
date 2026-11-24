/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.Compacts

/-!
# Fibers of a locally constant function as clopen sets

The fibers `f⁻¹{a}` of a locally constant function `f : X → α` are clopen
(`IsLocallyConstant.isClopen_fiber`). Because these open fibers cover `X`, a map out of `X` is
continuous if and only if its restriction to each fiber is continuous
(`IsLocallyConstant.continuous_iff`), and likewise for joint fibers of two locally constant
functions (`IsLocallyConstant.continuous_iff₂`) and for maps into a sigma space landing in each
corresponding summand (`IsLocallyConstant.continuous_iff_of_eq_sigmaMk`).

This file also packages the fibers of `f : LocallyConstant X α` as elements of `Clopens X`
(`LocallyConstant.fiberClopens`). Their underlying open sets `(f.fiberClopens a).toOpens` can
index restrictions of sheaves, and they cover `X`. Their preimages under a continuous map `g` are
the fibers of `f ∘ g` (`LocallyConstant.comap_toOpens_fiberClopens`).

When `f` takes a constant value `b₀` off a compact set, its fibers over the other values are compact
open, and `IsLocallyConstant.fiberCompactOpens` packages them as pairwise disjoint elements of
`CompactOpens X`. A compact open set `K ⊆ X × Y` whose slice at `x` is `π (f x)`, with `π b₀ = ⊥`,
is then the union of the rectangles over these fibers
(`IsLocallyConstant.mem_iff_exists_fiberCompactOpens`).
-/

public section

open TopologicalSpace

namespace IsLocallyConstant

/-- A map out of `X` is continuous if and only if its restriction to each fiber of a locally
constant function `f : X → α` is continuous. -/
theorem continuous_iff {X α T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {f : X → α} (hf : IsLocallyConstant f) {g : X → T} :
    Continuous g ↔ ∀ a : α, Continuous (fun x : {x : X // f x = a} => g x.val) := by
  refine ⟨fun hg _ => hg.comp continuous_subtypeVal, fun hg => ?_⟩
  exact continuous_of_cover_nhds (s := fun a => {x : X | f x = a})
    (fun x => ⟨f x, (hf.isOpen_fiber (f x)).mem_nhds rfl⟩)
    (fun a => continuousOn_iff_continuous_domRestrict.2 (hg a))

/-- A map `g : X → Σ a, Z a` into a disjoint union that lands in summand `Z a` via `h a` on each
fiber `{x // f x = a}` of a locally constant function `f` is continuous if and only if each `h a`
is continuous. -/
theorem continuous_iff_of_eq_sigmaMk {X α : Type*} {Z : α → Type*}
    [TopologicalSpace X] [∀ a, TopologicalSpace (Z a)]
    {f : X → α} (hf : IsLocallyConstant f) {g : X → Σ a, Z a}
    (h : ∀ a, {x : X // f x = a} → Z a)
    (hg : ∀ a (x : {x : X // f x = a}), g x.val = ⟨a, h a x⟩) :
    Continuous g ↔ ∀ a : α, Continuous (h a) := by
  rw [hf.continuous_iff]
  refine forall_congr' fun a ↦ ?_
  rw [(Topology.IsEmbedding.sigmaMk (σ := Z) (i := a)).continuous_iff]
  exact ⟨fun h' ↦ h'.congr (hg a), fun h' ↦ h'.congr fun x ↦ (hg a x).symm⟩

/-- A map out of `X` is continuous if and only if its restriction to each joint fiber of two
locally constant functions `f₁ : X → α` and `f₂ : X → β` is continuous. -/
theorem continuous_iff₂ {X α β T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {f₁ : X → α} {f₂ : X → β} (hf₁ : IsLocallyConstant f₁) (hf₂ : IsLocallyConstant f₂)
    {g : X → T} :
    Continuous g ↔
      ∀ (a : α) (b : β), Continuous (fun x : {x : X // f₁ x = a ∧ f₂ x = b} => g x.val) := by
  rw [(hf₁.prodMk hf₂).continuous_iff, Prod.forall]
  exact forall₂_congr fun a b =>
    ⟨fun h => h.comp ((continuous_subtypeVal (p := fun x => f₁ x = a ∧ f₂ x = b)).subtype_mk
        fun x => Prod.ext x.property.1 x.property.2),
     fun h => h.comp ((continuous_subtypeVal
        (p := fun x => (fun y => (f₁ y, f₂ y)) x = (a, b))).subtype_mk
        fun x => ⟨congrArg Prod.fst x.property, congrArg Prod.snd x.property⟩)⟩

section CompactOpens

variable {X β : Type*} [TopologicalSpace X] {f : X → β} (hf : IsLocallyConstant f) {c : Set X}
  (hc : IsCompact c) {b₀ : β} (hfc : ∀ x ∉ c, f x = b₀)

/-- The fiber of a locally constant function `f` over a value `b` other than the value `b₀` that
`f` takes off a compact set `c`, as a compact open set; it is empty for `b = b₀`. -/
def fiberCompactOpens (b : β) : CompactOpens X where
  carrier := {x | f x = b ∧ b ≠ b₀}
  isCompact' := hc.of_isClosed_subset ((hf.isClosed_fiber b).inter isClosed_const)
    fun x hx ↦ by_contra fun hxc ↦ hx.2 (hx.1 ▸ hfc x hxc)
  isOpen' := (hf.isOpen_fiber b).inter isOpen_const

@[simp]
theorem mem_fiberCompactOpens {b : β} {x : X} :
    x ∈ hf.fiberCompactOpens hc hfc b ↔ f x = b ∧ b ≠ b₀ :=
  Iff.rfl

theorem pairwiseDisjoint_fiberCompactOpens (s : Set β) :
    s.PairwiseDisjoint fun b ↦ (hf.fiberCompactOpens hc hfc b : Set X) :=
  fun _ _ _ _ hbb' ↦ Set.disjoint_left.2 fun _ hx hx' ↦
    hbb' (((hf.mem_fiberCompactOpens hc hfc).1 hx).1.symm.trans
      ((hf.mem_fiberCompactOpens hc hfc).1 hx').1)

/-- If a compact open set `K ⊆ X × Y` has slice `π (f x)` at each `x`, with `π b₀ = ⊥`, then `K` is
the union of the rectangles `hf.fiberCompactOpens hc hfc p ×ˢ π p` over any finite set `P` of
values containing `f '' c`. -/
theorem mem_iff_exists_fiberCompactOpens {Y : Type*} [TopologicalSpace Y]
    (π : β → CompactOpens Y) (hπ : π b₀ = ⊥) {K : CompactOpens (X × Y)}
    (hK : ∀ x y, (x, y) ∈ K ↔ y ∈ π (f x)) {P : Finset β} (hP : ∀ x ∈ c, f x ∈ P) (x : X) (y : Y) :
    (x, y) ∈ K ↔ ∃ p ∈ P, x ∈ hf.fiberCompactOpens hc hfc p ∧ y ∈ π p := by
  rw [hK]
  refine ⟨fun hy ↦ ?_, fun ⟨p, _, hxp, hy⟩ ↦ (hf.mem_fiberCompactOpens hc hfc).1 hxp |>.1 ▸ hy⟩
  have hb : f x ≠ b₀ := fun hb ↦ by
    rw [hb, hπ, ← SetLike.mem_coe, CompactOpens.coe_bot] at hy
    exact Set.notMem_empty y hy
  exact ⟨f x, hP x (by_contra fun hx ↦ hb (hfc x hx)),
    (hf.mem_fiberCompactOpens hc hfc).2 ⟨rfl, hb⟩, hy⟩

end CompactOpens

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
