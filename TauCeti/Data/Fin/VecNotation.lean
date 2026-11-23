/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Postcomposing a pair with a function

Postcomposing the pair `![a₀, a₁]` with a function `f` applies `f` to both entries
(`Matrix.comp_vec2`), in the style of `Matrix.smul_vec2` and `Matrix.vec2_add`. This is the form in
which a pair of vectors meets a pullback, for instance `Prod.fst ∘ ![u, u'] = ![u.1, u'.1]` when
a form on a factor is pulled back to a product.

## Main results

* `Matrix.comp_vec2`: `f ∘ ![a₀, a₁] = ![f a₀, f a₁]`.
-/

public section

namespace Matrix

/-- Postcomposing a pair with a function applies the function to both entries. -/
theorem comp_vec2 {α β : Type*} (f : α → β) (a₀ a₁ : α) : f ∘ ![a₀, a₁] = ![f a₀, f a₁] :=
  (FinVec.map_eq f ![a₀, a₁]).symm

end Matrix
