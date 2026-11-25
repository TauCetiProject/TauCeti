/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Synonym

/-!
# Coordinates of finite sums in `C⋆ᵐᵒᵈ(A, Π i, E i)`

Mathlib computes the coordinates of `0`, `x + y`, `x - y`, `-x` and `c • x` in the type synonym
`C⋆ᵐᵒᵈ(A, Π i, E i)` (`WithCStarModule.add_apply` and its siblings). This file adds the same
statement for finite sums, `WithCStarModule.sum_apply`.
-/

public section

open scoped WithCStarModule

namespace WithCStarModule

variable {A ι κ : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]

/-- A coordinate of a finite sum in `C⋆ᵐᵒᵈ(A, Π i, E i)` is the sum of the coordinates. -/
@[simp]
theorem sum_apply (s : Finset κ) (x : κ → C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) :
    (∑ k ∈ s, x k) i = ∑ k ∈ s, x k i :=
  Finset.sum_apply i s fun k ↦ equiv A (Π i, E i) (x k)

end WithCStarModule
