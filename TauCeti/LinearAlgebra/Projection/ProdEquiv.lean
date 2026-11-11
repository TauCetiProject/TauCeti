/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# The splitting along a complement and the horizontal subspace

Mathlib's `Submodule.prodEquivOfIsCompl` identifies `p × q` with `E` when `q` is a complement of
`p`. This file records that it carries the horizontal subspace of `p × q`, the kernel of the second
projection, onto `p`.

## Main results

* `Submodule.map_ker_snd_prodEquivOfIsCompl`: the splitting carries the kernel of the second
  projection onto `p`.
-/

public section

namespace Submodule

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The splitting of `E` along a complement of `p` carries the kernel of the second projection of
`p × q` onto `p`. -/
theorem map_ker_snd_prodEquivOfIsCompl (p q : Submodule R E) (h : IsCompl p q) :
    (LinearMap.ker (LinearMap.snd R p q)).map (prodEquivOfIsCompl p q h).toLinearMap = p := by
  ext v
  simp

end Submodule
