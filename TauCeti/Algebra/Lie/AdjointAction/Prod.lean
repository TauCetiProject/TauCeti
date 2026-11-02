/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Prod

/-!
# The adjoint action of a product of Lie algebras

The bracket on `L × L'` is computed coordinatewise, so the adjoint endomorphism of a pair is the
product of the adjoint endomorphisms of its coordinates. This identity is what lets trace,
nilpotence and semisimplicity statements about `ad` on a product be reduced to the factors.

## Main statements

* `LieAlgebra.ad_prod`: `ad (x, x') = (ad x).prodMap (ad x')`.
-/

public section

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- The adjoint endomorphism in a binary product acts separately on the two factors. -/
theorem ad_prod (x : L × L') :
    ad R (L × L') x = (ad R L x.1).prodMap (ad R L' x.2) := by
  ext y <;> simp [Prod.bracket_apply]

end LieAlgebra
