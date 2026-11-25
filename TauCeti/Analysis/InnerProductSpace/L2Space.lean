/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The standard Hilbert basis of `ℓ²`

Mathlib's default Hilbert basis of `ℓ²(ι, 𝕜)` has the identity as its coordinate map, so the
coordinates `⟪default i, x⟫` of a vector `x` are its entries `x i`
(`HilbertBasis.inner_default_apply`).
-/

public section

open scoped InnerProductSpace lp

namespace HilbertBasis

variable {ι 𝕜 : Type*} [RCLike 𝕜]

/-- The coordinates of `x` in the standard Hilbert basis of `ℓ²(ι, 𝕜)` are its entries. -/
@[simp]
theorem inner_default_apply (x : ℓ²(ι, 𝕜)) (i : ι) :
    ⟪(default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) i, x⟫_𝕜 = x i :=
  ((default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).repr_apply_apply x i).symm

end HilbertBasis
