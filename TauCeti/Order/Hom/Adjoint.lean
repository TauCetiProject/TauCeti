/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Adjoints of endpoint-preserving monotone maps on finite linear orders

Every monotone map `f : α →o β` from a finite linear order with top preserving `⊤` admits a
left adjoint `f.leftAdjoint hf : β →o α`, given at `y` by the least `x` with `y ≤ f x`. When both
orders have a bottom element, `f.leftAdjoint hf` automatically preserves `⊥`. Dually, every monotone
map `g : β →o α` into a finite linear order with bottom preserving `⊥` admits a right adjoint
`g.rightAdjoint hg : α →o β`, given at `x` by the greatest `y` with `g y ≤ x`, which automatically
preserves `⊤`.

On finite bounded linear orders these two constructions are mutually inverse and contravariantly
functorial (`OrderHom.leftAdjoint_comp`, `OrderHom.rightAdjoint_comp`), yielding the duality
between top-preserving and bottom-preserving monotone maps.

## Main declarations

* `OrderHom.leftAdjoint`: the left adjoint of a top-preserving monotone map out of a finite linear
  order.
* `OrderHom.rightAdjoint`: the right adjoint of a bottom-preserving monotone map into a finite
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

@[simp]
theorem leftAdjoint_le_iff (f : α →o β) (hf : f ⊤ = ⊤) {y : β} {x : α} :
    f.leftAdjoint hf y ≤ x ↔ y ≤ f x :=
  f.galoisConnection_leftAdjoint hf y x

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

@[simp]
theorem leftAdjoint_id {α : Type*} [LinearOrder α] [Fintype α] [OrderTop α] [DecidableLE α] :
    (OrderHom.id : α →o α).leftAdjoint rfl = OrderHom.id :=
  leftAdjoint_eq_of_galoisConnection rfl GaloisConnection.id

theorem leftAdjoint_comp {α β γ : Type*} [LinearOrder α] [Fintype α] [OrderTop α]
    [LinearOrder β] [Fintype β] [OrderTop β] [DecidableLE β]
    [Preorder γ] [OrderTop γ] [DecidableLE γ]
    {f : α →o β} (hf : f ⊤ = ⊤) {g : β →o γ} (hg : g ⊤ = ⊤)
    (hgf : (g.comp f) ⊤ = ⊤ := (congrArg g hf).trans hg) :
    (g.comp f).leftAdjoint hgf = (f.leftAdjoint hf).comp (g.leftAdjoint hg) :=
  leftAdjoint_eq_of_galoisConnection hgf <|
    (g.galoisConnection_leftAdjoint hg).compose (f.galoisConnection_leftAdjoint hf)

section RightAdjoint

variable {α β : Type*} [Preorder α] [OrderBot α] [DecidableLE α]
  [LinearOrder β] [Fintype β] [OrderBot β]

private def rightAdjointFun (g : β →o α) (hg : g ⊥ = ⊥) (x : α) : β :=
  (Finset.univ.filter (fun y : β ↦ g y ≤ x)).max'
    ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg ▸ bot_le⟩⟩

private theorem rightAdjointFun_gc (g : β →o α) (hg : g ⊥ = ⊥) :
    GaloisConnection g (rightAdjointFun g hg) := by
  intro y x
  constructor
  · intro h
    exact Finset.le_max' (Finset.univ.filter fun z : β ↦ g z ≤ x) y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro h
    have hmem := Finset.max'_mem (Finset.univ.filter (fun z : β ↦ g z ≤ x))
      ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg ▸ bot_le⟩⟩
    exact (g.monotone h).trans (Finset.mem_filter.mp hmem).2

/-- The right adjoint `α →o β` of a bottom-preserving monotone map `g : β →o α` into a finite
linear order with bottom. -/
def rightAdjoint (g : β →o α) (hg : g ⊥ = ⊥) : α →o β where
  toFun := rightAdjointFun g hg
  monotone' := (rightAdjointFun_gc g hg).monotone_u

/-- The Galois connection `g ⊣ g.rightAdjoint hg`. -/
theorem galoisConnection_rightAdjoint (g : β →o α) (hg : g ⊥ = ⊥) :
    GaloisConnection g (g.rightAdjoint hg) :=
  rightAdjointFun_gc g hg

@[simp]
theorem le_rightAdjoint_iff (g : β →o α) (hg : g ⊥ = ⊥) {y : β} {x : α} :
    y ≤ g.rightAdjoint hg x ↔ g y ≤ x :=
  (g.galoisConnection_rightAdjoint hg y x).symm

@[simp]
theorem rightAdjoint_top [OrderTop α] [OrderTop β] (g : β →o α) (hg : g ⊥ = ⊥) :
    g.rightAdjoint hg ⊤ = ⊤ :=
  (g.galoisConnection_rightAdjoint hg).u_top

/-- Uniqueness of `OrderHom.rightAdjoint` from a Galois connection. -/
theorem rightAdjoint_eq_of_galoisConnection {g : β →o α} (hg : g ⊥ = ⊥) {r : α →o β}
    (hr : GaloisConnection g r) : g.rightAdjoint hg = r :=
  OrderHom.ext _ _ <| funext fun _ ↦
    (g.galoisConnection_rightAdjoint hg).u_unique hr fun _ ↦ rfl

end RightAdjoint

@[simp]
theorem rightAdjoint_id {β : Type*} [LinearOrder β] [Fintype β] [OrderBot β] [DecidableLE β] :
    (OrderHom.id : β →o β).rightAdjoint rfl = OrderHom.id :=
  rightAdjoint_eq_of_galoisConnection rfl GaloisConnection.id

theorem rightAdjoint_comp {α β γ : Type*} [LinearOrder α] [Fintype α] [OrderBot α] [DecidableLE α]
    [LinearOrder β] [Fintype β] [OrderBot β] [Preorder γ] [OrderBot γ] [DecidableLE γ]
    {g : β →o α} (hg : g ⊥ = ⊥) {h : α →o γ} (hh : h ⊥ = ⊥)
    (hhg : (h.comp g) ⊥ = ⊥ := (congrArg h hg).trans hh) :
    (h.comp g).rightAdjoint hhg = (g.rightAdjoint hg).comp (h.rightAdjoint hh) :=
  rightAdjoint_eq_of_galoisConnection hhg <|
    (g.galoisConnection_rightAdjoint hg).compose (h.galoisConnection_rightAdjoint hh)

section Inverse

variable {α β : Type*} [LinearOrder α] [Fintype α] [BoundedOrder α] [DecidableLE α]
  [LinearOrder β] [Fintype β] [BoundedOrder β] [DecidableLE β]

@[simp]
theorem rightAdjoint_leftAdjoint (f : α →o β) (hf : f ⊤ = ⊤)
    (hbot : f.leftAdjoint hf ⊥ = ⊥ := f.leftAdjoint_bot hf) :
    (f.leftAdjoint hf).rightAdjoint hbot = f :=
  rightAdjoint_eq_of_galoisConnection hbot (f.galoisConnection_leftAdjoint hf)

@[simp]
theorem leftAdjoint_rightAdjoint (g : β →o α) (hg : g ⊥ = ⊥)
    (htop : g.rightAdjoint hg ⊤ = ⊤ := g.rightAdjoint_top hg) :
    (g.rightAdjoint hg).leftAdjoint htop = g :=
  leftAdjoint_eq_of_galoisConnection htop (g.galoisConnection_rightAdjoint hg)

end Inverse

end OrderHom
