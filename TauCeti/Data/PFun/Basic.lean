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
* `PFun.ran_map_const`: the range of `fun x => (f x).map fun _ => x` is `f.Dom`.
* `PFun.ran_comp_map_const`: the range of `g.comp fun x => (f x).map fun _ => x` is
  `g.image f.Dom`.
-/

public section

universe u v w

namespace PFun

/-- Binding a defined value `a` into a partial function `f` applies `f` to `a`. -/
@[simp]
theorem some_bind {α β : Type u} (f : α →. β) (a : α) : Part.some a >>= f = f a :=
  Part.bind_some a f

/-- Restricting the identity to the domain of `f` has range equal to `f.Dom`. -/
theorem ran_map_const {α : Type u} {β : Type v} (f : α →. β) :
    PFun.ran (fun x => (f x).map fun _ => x) = f.Dom := by
  ext y
  simp only [ran, Set.mem_ofPred_eq, Part.mem_map_iff, mem_dom]
  exact ⟨fun ⟨_, b, hb, rfl⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨y, b, hb, rfl⟩⟩

/-- Composing `g` with the identity restricted to the domain of `f` has range `g.image f.Dom`. -/
theorem ran_comp_map_const {α : Type u} {β : Type v} {γ : Type w} (g : α →. γ) (f : α →. β) :
    PFun.ran (PFun.comp g fun x => (f x).map fun _ => x) = g.image f.Dom := by
  ext y
  have hcomp (x : α) :
      PFun.comp g (fun x => (f x).map fun _ => x) x = ((f x).map fun _ => x).bind g :=
    PFun.comp_apply g (fun x => (f x).map fun _ => x) x
  simp only [ran, Set.mem_ofPred_eq, mem_image, mem_dom]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    rw [hcomp] at hx
    obtain ⟨x', hx', hy⟩ := Part.mem_bind_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hx'
    exact ⟨x, ⟨b, hb⟩, hy⟩
  · rintro ⟨x, ⟨b, hb⟩, hy⟩
    refine ⟨x, ?_⟩
    rw [hcomp]
    exact Part.mem_bind_iff.2 ⟨x, (Part.mem_map_iff _).2 ⟨b, hb, rfl⟩, hy⟩

end PFun
