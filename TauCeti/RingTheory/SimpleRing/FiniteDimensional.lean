/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `IsSimpleRing` and `FiniteDimensional` occur in the exported statement.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
-- Non-public: the faithful action `Algebra.lsmul`, the injectivity of ring homomorphisms out of a
-- simple ring, and the finiteness of an endomorphism algebra are used only inside the proof.
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Finite-dimensionality of a simple algebra with a finite-dimensional module

A simple ring acts faithfully on every nonzero module: the action map into the endomorphism ring is
a ring homomorphism to a nontrivial ring, hence injective. So a simple `K`-algebra `R` with a
nonzero module `M` which is finite-dimensional over `K` embeds `K`-linearly into `End_K M`, and is
therefore finite-dimensional over `K`.

This lets statements about modules over a simple algebra which are finite-dimensional over `K`
drop the separate hypothesis that the algebra itself is finite-dimensional, as in
`TauCeti/RingTheory/Semisimple/SimpleArtinian.lean` and
`TauCeti/RingTheory/Semisimple/EndAlgebra.lean`.

## Main results

* `IsSimpleRing.finiteDimensional_of_nontrivial`: a simple `K`-algebra with a nonzero module
  finite-dimensional over `K` is finite-dimensional.
-/

public section

namespace IsSimpleRing

variable (K : Type*) [Field K] {R : Type*} [Ring R] [IsSimpleRing R] [Algebra K R]
  {M : Type*} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]

/-- A simple `K`-algebra with a nonzero module which is finite-dimensional over `K` is itself
finite-dimensional over `K`: it acts faithfully on the module, so it embeds in the endomorphism
algebra of the module. -/
theorem finiteDimensional_of_nontrivial [Nontrivial M] : FiniteDimensional K R :=
  Module.Finite.of_injective (Algebra.lsmul K K M : R →ₐ[K] Module.End K M).toLinearMap
    (RingHom.injective (Algebra.lsmul K K M : R →ₐ[K] Module.End K M).toRingHom)

end IsSimpleRing
