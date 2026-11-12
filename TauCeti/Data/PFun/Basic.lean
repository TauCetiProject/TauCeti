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
inputs, such as evaluations of programs relative to an oracle.

## Main results

* `PFun.some_bind`: `Part.some a >>= f = f a` for a partial function `f`.
-/

public section

universe u

namespace PFun

/-- Binding a defined value `a` into a partial function `f` applies `f` to `a`. -/
@[simp]
theorem some_bind {α β : Type u} (f : α →. β) (a : α) : Part.some a >>= f = f a :=
  Part.bind_some a f

end PFun
