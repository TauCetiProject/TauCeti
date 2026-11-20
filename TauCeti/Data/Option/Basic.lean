/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Option.Basic

/-!
# Basic lemmas on `Option`

* `Option.unattach_bind`: forgetting subtype membership commutes with `Option.bind`.
* `Option.unattach_inj`, `Option.unattach_map`, `Option.map_unattach_eq_map_val`: injectivity of
  `Option.unattach` and compatibility with `Option.map`.
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
