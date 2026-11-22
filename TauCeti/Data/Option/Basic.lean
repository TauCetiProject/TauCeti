/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Option.Basic
public import Mathlib.Logic.Relation

/-!
# Basic lemmas on `Option`

* `Option.unattach_bind`: forgetting subtype membership commutes with `Option.bind`.
* `Option.unattach_inj`, `Option.unattach_map`, `Option.map_unattach_eq_map_val`: injectivity of
  `Option.unattach` and compatibility with `Option.map`.
* `TauCeti.reflTransGen_of_foldlM_eq_some`: a successful `List.foldlM` over `Option` gives a
  `Relation.ReflTransGen` walk whenever each step satisfies the relation.
-/

public section

namespace Option

/-- Forgetting subtype membership commutes with `Option.bind`. -/
@[simp]
theorem unattach_bind {α β : Type*} {q : β → Prop} (o : Option α)
    (f : α → Option {y // q y}) :
    (o.bind f).unattach = o.bind fun x ↦ (f x).unattach := by
  cases o <;> simp

/-- `Option.unattach` is injective. -/
@[simp]
theorem unattach_inj {α : Type*} {p : α → Prop} {o₁ o₂ : Option {x // p x}} :
    o₁.unattach = o₂.unattach ↔ o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> simp [Subtype.ext_iff]

/-- Forgetting subtype membership after mapping into a subtype drops the proof component. -/
@[simp]
theorem unattach_map {α β : Type*} {q : β → Prop} (o : Option α)
    (g : α → β) (hg : ∀ x, q (g x)) :
    (o.map fun x ↦ (⟨g x, hg x⟩ : {y // q y})).unattach = o.map g := by
  cases o <;> rfl

/-- Mapping after `Option.unattach` composes with `Subtype.val`. -/
theorem map_unattach_eq_map_val {α β : Type*} {p : α → Prop} (o : Option {x // p x}) (g : α → β) :
    o.unattach.map g = o.map fun x ↦ g x.val := by
  cases o <;> rfl

end Option

namespace TauCeti

/-- If every defined `Option`-valued step `f z a = some z'` implies `r z z'`, then a defined
`List.foldlM` along `l` from `x` to `y` yields `Relation.ReflTransGen r x y`. -/
theorem reflTransGen_of_foldlM_eq_some {α β : Type*} {r : α → α → Prop}
    {f : α → β → Option α} (hf : ∀ {x y : α} {a : β}, f x a = some y → r x y)
    {l : List β} {x y : α} (h : l.foldlM f x = some y) : Relation.ReflTransGen r x y := by
  induction l generalizing x with
  | nil => obtain rfl := Option.some.inj (by simpa using h); exact .refl
  | cons a l ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨z, hxz, hzy⟩ := Option.bind_eq_some_iff.mp h
    exact .head (hf hxz) (ih hzy)

/-- Variant of `TauCeti.reflTransGen_of_foldlM_eq_some` for an action `g : List β → α → Option α`
characterized by its `[]` and `b :: l` equations (for instance an unexposed wrapper around
`List.foldlM`). -/
theorem reflTransGen_of_nil_of_cons_eq_some {α β : Type*} {r : α → α → Prop}
    {f : α → β → Option α} {g : List β → α → Option α}
    (hnil : ∀ x, g [] x = some x) (hcons : ∀ b l x, g (b :: l) x = (f x b).bind (g l))
    (hf : ∀ {x y : α} {b : β}, f x b = some y → r x y)
    {l : List β} {x y : α} (h : g l x = some y) : Relation.ReflTransGen r x y := by
  have heq : ∀ l x, g l x = l.foldlM f x := by
    intro l
    induction l with
    | nil => intro x; simp [hnil]
    | cons b l ih => intro x; simp [hcons, ih]
  exact reflTransGen_of_foldlM_eq_some (f := f) hf (heq l x ▸ h)

end TauCeti
