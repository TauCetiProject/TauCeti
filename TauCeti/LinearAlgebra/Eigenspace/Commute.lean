/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Eigenspaces of commuting endomorphisms

An endomorphism `g` commuting with `f` commutes with every polynomial `p(f)`, so it preserves the
generalized eigenspaces of `p(f)`. Taking `g = f` shows that `f` preserves them too. This is the
commuting analogue of `Module.End.mapsTo_genEigenspace_neg_of_anticommute`.

## Main declarations

* `Module.End.mapsTo_genEigenspace_aeval_of_comm`: an endomorphism commuting with `f`
  preserves the generalized eigenspaces of `p(f)`.
-/

public section

open Polynomial

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An endomorphism `g` commuting with `f` preserves the generalized eigenspaces of `p(f)`, for
every polynomial `p`. -/
theorem mapsTo_genEigenspace_aeval_of_comm {f g : End R M} (h : Commute f g) (p : R[X])
    (μ : R) (k : ℕ∞) :
    Set.MapsTo g ((aeval f p).genEigenspace μ k) ((aeval f p).genEigenspace μ k) :=
  mapsTo_genEigenspace_of_comm
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton R f)
      h.symm).symm μ k

end Module.End
