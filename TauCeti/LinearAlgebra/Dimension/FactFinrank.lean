/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The reflexive dimension condition as a `Fact`

Constructions whose dimension hypothesis `Module.finrank R M = Module.finrank R N` is supplied as
an instance `Fact (Module.finrank R M = Module.finrank R N)` (such as the orthonormal frame bundle
`TauCeti.OrthonormalFrameBundle.Fiber`) apply without further work when `M = N`, by the instance
`TauCeti.instFactFinrankEqSelf`.
-/

public section

namespace TauCeti

/-- A module has its own dimension, as an instance of `Fact`. -/
instance instFactFinrankEqSelf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Fact (Module.finrank R M = Module.finrank R M) :=
  ⟨rfl⟩

end TauCeti
