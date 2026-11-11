/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# The dimension of a subcomodule

A bundled subcomodule and its carrier submodule `TauCeti.Subcomodule.toSubmodule` have the same
underlying type, so they have the same `Module.finrank`. Dimension counts over subcomodules pass
through this definitional equality to reach linear-algebra dimension lemmas stated for `Submodule`.

## Main results

* `TauCeti.Subcomodule.finrank_toSubmodule`: a subcomodule has the `Module.finrank` of its carrier
  submodule.
-/

public section

namespace TauCeti.Subcomodule

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The type underlying a bundled subcomodule is the type underlying its carrier submodule, so the
two have the same `Module.finrank`. -/
@[simp]
theorem finrank_toSubmodule (N : Subcomodule R C M) :
    Module.finrank R N.toSubmodule = Module.finrank R N :=
  rfl

end TauCeti.Subcomodule
