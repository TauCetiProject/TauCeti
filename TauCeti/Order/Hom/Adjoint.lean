/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max

/-!
# Adjoints of endpoint-preserving monotone maps on finite linear orders

Every top-preserving monotone map `f : α →o β` from a finite linear order `α` with top into a
preorder `β` with top and decidable `≤` admits a left adjoint `f.leftAdjoint hf : β →o α`, given at
`y` by the least `x` with `y ≤ f x`. When both orders have a bottom element, `f.leftAdjoint hf`
automatically preserves `⊥`. Dually, every bottom-preserving monotone map `g : β →o α` from a
finite linear order `β` with bottom into a preorder `α` with bottom and decidable `≤` admits a
right adjoint `g.rightAdjoint hg : α →o β`, given at `x` by the greatest `y` with `g y ≤ x`. When
both orders have a top element, `g.rightAdjoint hg` automatically preserves `⊤`.

On finite bounded linear orders these two constructions are mutually inverse and contravariantly
functorial (`OrderHom.leftAdjoint_comp`, `OrderHom.rightAdjoint_comp`), yielding the duality
between top-preserving and bottom-preserving monotone maps. Moreover, if `f` also preserves `⊥`
(resp. `g` also preserves `⊤`), then `f.leftAdjoint` reflects `⊥`
(`OrderHom.leftAdjoint_eq_bot_iff`, `OrderHom.leftAdjoint_ne_bot`) and `g.rightAdjoint` reflects
`⊤` (`OrderHom.rightAdjoint_eq_top_iff`, `OrderHom.rightAdjoint_ne_top`).

## Main declarations

* `OrderHom.leftAdjoint`: the left adjoint of a top-preserving monotone map from a finite linear
  order.
* `OrderHom.rightAdjoint`: the right adjoint of a bottom-preserving monotone map from a finite
  linear order.
* `OrderHom.galoisConnection_leftAdjoint`, `OrderHom.galoisConnection_rightAdjoint`: the
  defining Galois connections.
* `OrderHom.rightAdjoint_leftAdjoint`, `OrderHom.leftAdjoint_rightAdjoint`: the mutual inverse
  laws on finite bounded linear orders.
-/

public section

namespace OrderHom

section LeftAdjoint

variable {α β : Type*} [LinearOrder α] [Fintype α] [OrderTop α] [Preorder β] [OrderTop β]
  [DecidableLE β]

private def leftAdjointFun (f : α →o β) (hf : f ⊤ = ⊤) (y : β) : α :=
  (Finset.univ.filter (fun x : α ↦ y ≤ f x)).min'
    ⟨⊤, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf ▸ le_top⟩⟩

private theorem leftAdjointFun_gc (f : α →o β) (hf : f ⊤ = ⊤) :
    GaloisConnection (leftAdjointFun f hf) f := by
  intro y x
  constructor
  · intro h
    have hmem := Finset.min'_mem (Finset.univ.filter (fun z : α ↦ y ≤ f z))
      ⟨⊤, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf ▸ le_top⟩⟩
    exact (Finset.mem_filter.mp hmem).2.trans (f.monotone h)
  · intro h
    exact Finset.min'_le (Finset.univ.filter fun z : α ↦ y ≤ f z) x
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- The left adjoint `β →o α` of a top-preserving monotone map `f : α →o β` from a finite linear
order with top. -/
def leftAdjoint (f : α →o β) (hf : f ⊤ = ⊤) : β →o α where
  toFun := leftAdjointFun f hf
  monotone' := (leftAdjointFun_gc f hf).monotone_l

/-- The Galois connection `f.leftAdjoint hf ⊣ f`. -/
theorem galoisConnection_leftAdjoint (f : α →o β) (hf : f ⊤ = ⊤) :
    GaloisConnection (f.leftAdjoint hf) f :=
  leftAdjointFun_gc f hf

/-- Inequality characterization of the left adjoint: `f.leftAdjoint hf y ≤ x ↔ y ≤ f x`. -/
@[simp]
theorem leftAdjoint_le_iff (f : α →o β) (hf : f ⊤ = ⊤) {y : β} {x : α} :
    f.leftAdjoint hf y ≤ x ↔ y ≤ f x :=
  f.galoisConnection_leftAdjoint hf y x

/-- The left adjoint of a top-preserving map automatically preserves `⊥` when both orders have
bottom elements. -/
@[simp]
theorem leftAdjoint_bot [OrderBot α] [OrderBot β] (f : α →o β) (hf : f ⊤ = ⊤) :
    f.leftAdjoint hf ⊥ = ⊥ :=
  (f.galoisConnection_leftAdjoint hf).l_bot

/-- Uniqueness of `OrderHom.leftAdjoint` from a Galois connection. -/
theorem leftAdjoint_eq_of_galoisConnection {f : α →o β} (hf : f ⊤ = ⊤) {l : β →o α}
    (hl : GaloisConnection l f) : f.leftAdjoint hf = l :=
  OrderHom.ext _ _ <| funext fun _ ↦
    (f.galoisConnection_leftAdjoint hf).l_unique hl fun _ ↦ rfl

end LeftAdjoint

/-- The left adjoint of the identity monotone map is the identity. -/
@[simp]
theorem leftAdjoint_id {α : Type*} [LinearOrder α] [Fintype α] [OrderTop α] :
    (OrderHom.id : α →o α).leftAdjoint rfl = OrderHom.id :=
  leftAdjoint_eq_of_galoisConnection rfl GaloisConnection.id

/-- Contravariant functoriality of `OrderHom.leftAdjoint`: for top-preserving maps `f` and `g`,
`(g.comp f).leftAdjoint` equals `(f.leftAdjoint hf).comp (g.leftAdjoint hg)`. -/
@[simp]
theorem leftAdjoint_comp {α β γ : Type*} [LinearOrder α] [Fintype α] [OrderTop α]
    [LinearOrder β] [Fintype β] [OrderTop β] [Preorder γ] [OrderTop γ] [DecidableLE γ]
    {f : α →o β} (hf : f ⊤ = ⊤) {g : β →o γ} (hg : g ⊤ = ⊤)
    (hgf : (g.comp f) ⊤ = ⊤ := (congrArg g hf).trans hg) :
    (g.comp f).leftAdjoint hgf = (f.leftAdjoint hf).comp (g.leftAdjoint hg) :=
  leftAdjoint_eq_of_galoisConnection hgf <|
    (g.galoisConnection_leftAdjoint hg).compose (f.galoisConnection_leftAdjoint hf)

section RightAdjoint

variable {α β : Type*} [Preorder α] [OrderBot α] [DecidableLE α]
  [LinearOrder β] [Fintype β] [OrderBot β]

/-- The right adjoint `α →o β` of a bottom-preserving monotone map `g : β →o α` from a finite
linear order `β` with bottom into a preorder `α` with bottom and decidable `≤`. -/
def rightAdjoint (g : β →o α) (hg : g ⊥ = ⊥) : α →o β :=
  OrderHom.dual.symm ((OrderHom.dual g).leftAdjoint hg)

/-- The Galois connection `g ⊣ g.rightAdjoint hg`. -/
theorem galoisConnection_rightAdjoint (g : β →o α) (hg : g ⊥ = ⊥) :
    GaloisConnection g (g.rightAdjoint hg) :=
  ((OrderHom.dual g).galoisConnection_leftAdjoint hg).dual

/-- Inequality characterization of the right adjoint: `y ≤ g.rightAdjoint hg x ↔ g y ≤ x`. -/
@[simp]
theorem le_rightAdjoint_iff (g : β →o α) (hg : g ⊥ = ⊥) {y : β} {x : α} :
    y ≤ g.rightAdjoint hg x ↔ g y ≤ x :=
  (g.galoisConnection_rightAdjoint hg y x).symm

/-- The right adjoint of a bottom-preserving map automatically preserves `⊤` when both orders have
top elements. -/
@[simp]
theorem rightAdjoint_top [OrderTop α] [OrderTop β] (g : β →o α) (hg : g ⊥ = ⊥) :
    g.rightAdjoint hg ⊤ = ⊤ :=
  (OrderHom.dual g).leftAdjoint_bot hg

/-- Uniqueness of `OrderHom.rightAdjoint` from a Galois connection. -/
theorem rightAdjoint_eq_of_galoisConnection {g : β →o α} (hg : g ⊥ = ⊥) {r : α →o β}
    (hr : GaloisConnection g r) : g.rightAdjoint hg = r :=
  OrderHom.dual.symm_apply_eq.mpr <|
    leftAdjoint_eq_of_galoisConnection hg hr.dual

end RightAdjoint

/-- The right adjoint of the identity monotone map is the identity. -/
@[simp]
theorem rightAdjoint_id {β : Type*} [LinearOrder β] [Fintype β] [OrderBot β] :
    (OrderHom.id : β →o β).rightAdjoint rfl = OrderHom.id :=
  OrderHom.dual.symm_apply_eq.mpr leftAdjoint_id

/-- Contravariant functoriality of `OrderHom.rightAdjoint`: for bottom-preserving maps `g` and `h`,
`(h.comp g).rightAdjoint` equals `(g.rightAdjoint hg).comp (h.rightAdjoint hh)`. -/
@[simp]
theorem rightAdjoint_comp {α β γ : Type*} [LinearOrder α] [Fintype α] [OrderBot α]
    [LinearOrder β] [Fintype β] [OrderBot β] [Preorder γ] [OrderBot γ] [DecidableLE γ]
    {g : β →o α} (hg : g ⊥ = ⊥) {h : α →o γ} (hh : h ⊥ = ⊥)
    (hhg : (h.comp g) ⊥ = ⊥ := (congrArg h hg).trans hh) :
    (h.comp g).rightAdjoint hhg = (g.rightAdjoint hg).comp (h.rightAdjoint hh) :=
  (OrderHom.dual.symm_apply_eq.mpr
    (leftAdjoint_comp (f := OrderHom.dual g) hg (g := OrderHom.dual h) hh hhg)).trans
    (OrderHom.symm_dual_comp _ _)

/-- When a top-preserving monotone map `f : α →o β` also preserves `⊥`, its left adjoint takes
the value `⊥` only at `⊥`. -/
@[simp]
theorem leftAdjoint_eq_bot_iff {α β : Type*} [LinearOrder α] [Fintype α] [OrderTop α] [OrderBot α]
    [PartialOrder β] [OrderTop β] [OrderBot β] [DecidableLE β]
    (f : α →o β) (hf : f ⊤ = ⊤) (hbot : f ⊥ = ⊥) {y : β} :
    f.leftAdjoint hf y = ⊥ ↔ y = ⊥ := by
  rw [(f.galoisConnection_leftAdjoint hf).l_eq_bot, hbot, le_bot_iff]

/-- When a top-preserving monotone map `f : α →o β` also preserves `⊥`, its left adjoint maps
non-bottom elements to non-bottom elements. -/
theorem leftAdjoint_ne_bot {α β : Type*} [LinearOrder α] [Fintype α] [OrderTop α] [OrderBot α]
    [PartialOrder β] [OrderTop β] [OrderBot β] [DecidableLE β]
    (f : α →o β) (hf : f ⊤ = ⊤) (hbot : f ⊥ = ⊥) {y : β} (hy : y ≠ ⊥) :
    f.leftAdjoint hf y ≠ ⊥ :=
  (f.leftAdjoint_eq_bot_iff hf hbot).not.mpr hy

/-- When a bottom-preserving monotone map `g : β →o α` also preserves `⊤`, its right adjoint
takes the value `⊤` only at `⊤`. -/
@[simp]
theorem rightAdjoint_eq_top_iff {α β : Type*} [PartialOrder α] [OrderTop α] [OrderBot α]
    [DecidableLE α] [LinearOrder β] [Fintype β] [OrderTop β] [OrderBot β]
    (g : β →o α) (hg : g ⊥ = ⊥) (htop : g ⊤ = ⊤) {x : α} :
    g.rightAdjoint hg x = ⊤ ↔ x = ⊤ :=
  leftAdjoint_eq_bot_iff (OrderHom.dual g) hg htop

/-- When a bottom-preserving monotone map `g : β →o α` also preserves `⊤`, its right adjoint
maps non-top elements to non-top elements. -/
theorem rightAdjoint_ne_top {α β : Type*} [PartialOrder α] [OrderTop α] [OrderBot α]
    [DecidableLE α] [LinearOrder β] [Fintype β] [OrderTop β] [OrderBot β]
    (g : β →o α) (hg : g ⊥ = ⊥) (htop : g ⊤ = ⊤) {x : α} (hx : x ≠ ⊤) :
    g.rightAdjoint hg x ≠ ⊤ :=
  leftAdjoint_ne_bot (OrderHom.dual g) hg htop hx

section Inverse

variable {α β : Type*} [LinearOrder α] [Fintype α] [BoundedOrder α]
  [LinearOrder β] [Fintype β] [BoundedOrder β]

/-- On finite bounded linear orders, taking the right adjoint of `f.leftAdjoint hf` (which preserves
`⊥` by `OrderHom.leftAdjoint_bot`) recovers `f`. -/
@[simp]
theorem rightAdjoint_leftAdjoint (f : α →o β) (hf : f ⊤ = ⊤)
    (hbot : f.leftAdjoint hf ⊥ = ⊥ := f.leftAdjoint_bot hf) :
    (f.leftAdjoint hf).rightAdjoint hbot = f :=
  rightAdjoint_eq_of_galoisConnection hbot (f.galoisConnection_leftAdjoint hf)

/-- On finite bounded linear orders, taking the left adjoint of `g.rightAdjoint hg` (which preserves
`⊤` by `OrderHom.rightAdjoint_top`) recovers `g`. -/
@[simp]
theorem leftAdjoint_rightAdjoint (g : β →o α) (hg : g ⊥ = ⊥)
    (htop : g.rightAdjoint hg ⊤ = ⊤ := g.rightAdjoint_top hg) :
    (g.rightAdjoint hg).leftAdjoint htop = g :=
  leftAdjoint_eq_of_galoisConnection htop (g.galoisConnection_rightAdjoint hg)

end Inverse

end OrderHom
