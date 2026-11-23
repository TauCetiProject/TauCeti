/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Bases of root pairings

This file records basic properties of `RootPairing.Base` that depend only on the definition of a
base in Mathlib.

## Main results

* `RootPairing.Base.ext`: a base is determined by its support, the indices of its simple roots.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- **A base is determined by its simple roots.** The other fields of a base are propositions about
its support. -/
@[ext]
theorem ext {b b' : P.Base} (h : b.support = b'.support) : b = b' := by
  cases b
  cases b'
  subst h
  rfl

end RootPairing.Base
