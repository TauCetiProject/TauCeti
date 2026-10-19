/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Endomorphisms commuting with a subalgebra

An endomorphism linear over a subalgebra of `Module.End K N` commutes with that subalgebra.
Restricting scalars therefore gives an element of its centralizer in `Module.End K N`.
This fact uses only semiring scalars and an additive commutative monoid, independently of
semisimplicity or finiteness assumptions used in double centralizer theorems.
-/

public section

namespace Subalgebra

variable {K N : Type*} [CommSemiring K] [AddCommMonoid N] [Module K N]

/-- An endomorphism linear over a subalgebra of `Module.End K N` lies in its centralizer after
restricting scalars to `K`. -/
theorem restrictScalars_mem_centralizer (A : Subalgebra K (Module.End K N))
    (g : Module.End A N) :
    g.restrictScalars K ∈ centralizer K (A : Set (Module.End K N)) := by
  refine (mem_centralizer_iff K).2 fun a ha => ?_
  ext m
  exact (g.map_smul ⟨a, ha⟩ m).symm

end Subalgebra
