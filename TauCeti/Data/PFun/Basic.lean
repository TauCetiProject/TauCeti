/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PFun

/-!
# Binding a defined value into a partial function

A partial function `f : α →. β` is a function `α → Part β`, but `α →. β` is a definition that
`simp` does not unfold, so `Part.bind_some` does not rewrite `Part.some a >>= f`. This file states
that rewrite for partial functions. It computes compositions of partial functions with defined
inputs, such as evaluations of programs relative to an oracle, and provides range lemmas for
domain-restricted identity maps.

## Main results

* `PFun.some_bind`: `Part.some a >>= f = f a` for a partial function `f`.
* `PFun.ran_res`: the range of `PFun.res h S` is `h '' S`.
* `PFun.ran_comp`: the range of `g.comp f` is `g.image f.ran`.
* `PFun.ran_map_const`: the range of `fun x => (f x).map fun _ => x` is `f.Dom`.
-/

public section

universe u v w

namespace PFun

/-- Binding a defined value `a` into a partial function `f` applies `f` to `a`. -/
@[simp]
theorem some_bind {α β : Type u} (f : α →. β) (a : α) : Part.some a >>= f = f a :=
  Part.bind_some a f

/-- The range of a total function restricted to a set `S` is `h '' S`. -/
@[simp]
theorem ran_res {α : Type u} {β : Type v} (h : α → β) (S : Set α) :
    (PFun.res h S).ran = h '' S := by
  ext y
  simp [ran, mem_res]

/-- The range of a partial-function composition `g.comp f` is the image of `f.ran` under `g`. -/
@[simp]
theorem ran_comp {α : Type u} {β : Type v} {γ : Type w} (g : β →. γ) (f : α →. β) :
    (g.comp f).ran = g.image f.ran := by
  ext z
  simp only [ran, Set.mem_ofPred_eq, comp_apply, mem_image]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hz⟩ := Part.mem_bind_iff.1 hx
    exact ⟨y, ⟨x, hy⟩, hz⟩
  · rintro ⟨y, ⟨x, hy⟩, hz⟩
    exact ⟨x, Part.mem_bind_iff.2 ⟨y, hy, hz⟩⟩

/-- Restricting the identity to the domain of `f` has range equal to `f.Dom`. -/
@[simp]
theorem ran_map_const {α : Type u} {β : Type v} (f : α →. β) :
    PFun.ran (fun x => (f x).map fun _ => x) = f.Dom := by
  have hres : (fun x => (f x).map fun _ => x) = PFun.res id f.Dom := by
    ext x y
    simp [mem_res, Part.mem_map_iff, mem_dom]
  rw [hres, ran_res, Set.image_id]

end PFun
