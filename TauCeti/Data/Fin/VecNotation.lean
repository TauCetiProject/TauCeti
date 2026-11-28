/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Operations on vector pairs

Postcomposing the pair `![a₀, a₁]` with a function `f` applies `f` to both entries
(`Matrix.comp_vec2`), in the style of `Matrix.smul_vec2` and `Matrix.vec2_add`. This is the form in
which a pair of vectors meets a pullback, for instance `Prod.fst ∘ ![u, u'] = ![u.1, u'.1]` when
a form on a factor is pulled back to a product.

## Main results

* `Matrix.comp_vec2`: `f ∘ ![a₀, a₁] = ![f a₀, f a₁]`.
* `TauCeti.eq_of_smul_vecCons_one_eq`: rows of the form `![x, 1]` have unique first coordinates
  up to scalar rescaling.
-/

public section

namespace Matrix

/-- Postcomposing a pair with a function applies the function to both entries. -/
theorem comp_vec2 {α β : Type*} (f : α → β) (a₀ a₁ : α) : f ∘ ![a₀, a₁] = ![f a₀, f a₁] :=
  (FinVec.map_eq f ![a₀, a₁]).symm

end Matrix

/-- Two rows of the form `![x, 1]` have the same first coordinate if one is a scalar multiple
of the other. -/
theorem TauCeti.eq_of_smul_vecCons_one_eq {R : Type*} [Monoid R] {x y : R} {a : R}
    (h : a • (![x, 1] : Fin 2 → R) = ![y, 1]) : x = y := by
  have ha : a = 1 := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun h 1
  simpa [ha] using congrFun h 0
