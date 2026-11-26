/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases

/-!
# Postcomposing a pair with a function, and updating a four-tuple

Postcomposing the pair `![a₀, a₁]` with a function `f` applies `f` to both entries
(`Matrix.comp_vec2`), in the style of `Matrix.smul_vec2` and `Matrix.vec2_add`. This is the form in
which a pair of vectors meets a pullback, for instance `Prod.fst ∘ ![u, u'] = ![u.1, u'.1]` when
a form on a factor is pulled back to a product.

Replacing the entry in slot `i` of a four-tuple `![a₀, a₁, a₂, a₃]` by `p` gives the four-tuple
with `p` in slot `i` (`Matrix.update_vec4_zero` to `Matrix.update_vec4_three`). This is the form
in which a multilinear map in four arguments is used as a linear map in a single slot.

## Main results

* `Matrix.comp_vec2`: `f ∘ ![a₀, a₁] = ![f a₀, f a₁]`.
* `Matrix.update_vec4_zero`, `Matrix.update_vec4_one`, `Matrix.update_vec4_two`,
  `Matrix.update_vec4_three`: `Function.update ![a₀, a₁, a₂, a₃] i p` for each slot `i`.
-/

public section

namespace Matrix

/-- Postcomposing a pair with a function applies the function to both entries. -/
theorem comp_vec2 {α β : Type*} (f : α → β) (a₀ a₁ : α) : f ∘ ![a₀, a₁] = ![f a₀, f a₁] :=
  (FinVec.map_eq f ![a₀, a₁]).symm

section Update

variable {α : Type*} (a₀ a₁ a₂ a₃ p : α)

/-- Replacing the first entry of a four-tuple. -/
@[simp]
theorem update_vec4_zero : Function.update ![a₀, a₁, a₂, a₃] 0 p = ![p, a₁, a₂, a₃] := by
  ext i; fin_cases i <;> simp

/-- Replacing the second entry of a four-tuple. -/
@[simp]
theorem update_vec4_one : Function.update ![a₀, a₁, a₂, a₃] 1 p = ![a₀, p, a₂, a₃] := by
  ext i; fin_cases i <;> simp

/-- Replacing the third entry of a four-tuple. -/
@[simp]
theorem update_vec4_two : Function.update ![a₀, a₁, a₂, a₃] 2 p = ![a₀, a₁, p, a₃] := by
  ext i; fin_cases i <;> simp

/-- Replacing the fourth entry of a four-tuple. -/
@[simp]
theorem update_vec4_three : Function.update ![a₀, a₁, a₂, a₃] 3 p = ![a₀, a₁, a₂, p] := by
  ext i; fin_cases i <;> simp

end Update

end Matrix
