/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Opposites
public import Mathlib.Logic.Small.Basic

/-!
# Smallness of the opposite type

The multiplicative opposite `αᵐᵒᵖ` is in bijection with `α` through `MulOpposite.unop`, so it is
`w`-small whenever `α` is.

## Main results

* `TauCeti.small_mulOpposite`: the instance `Small.{w} αᵐᵒᵖ` for a `w`-small type `α`.
-/

public section

universe w u

namespace TauCeti

/-- If `α` is `w`-small, so is its multiplicative opposite `αᵐᵒᵖ`. -/
instance small_mulOpposite (α : Type u) [Small.{w} α] : Small.{w} αᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

end TauCeti
