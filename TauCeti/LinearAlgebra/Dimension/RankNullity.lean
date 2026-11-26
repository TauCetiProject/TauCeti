/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank–nullity on a submodule in terms of `finrank`

Mathlib's `LinearMap.rank_map_add_rank_inf_ker` says that a linear map `f` restricted to a submodule
`p` has image `f(p)` and kernel `p ⊓ ker f` of ranks adding to the rank of `p`. This file records
its `finrank` form for a finitely generated submodule `p` over a ring with the rank-nullity
property, such as a division ring or a commutative domain.

## Main results

* `LinearMap.finrank_map_add_finrank_inf_ker`: `dim f(p) + dim (p ⊓ ker f) = dim p`.
-/

public section

namespace LinearMap

universe v

/-- The `finrank` form of `LinearMap.rank_map_add_rank_inf_ker`, **rank–nullity on a
submodule**: the image `f(p)` and the kernel `p ⊓ ker f` of a linear map on a finite submodule `p`
have dimensions adding to that of `p`. -/
theorem finrank_map_add_finrank_inf_ker {K : Type*} {M : Type v} {N : Type*} [Ring K]
    [HasRankNullity.{v} K] [StrongRankCondition K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (p : Submodule K M) [Module.Finite K p] :
    Module.finrank K (p.map f) + Module.finrank K ↥(p ⊓ ker f) = Module.finrank K p := by
  rw [← (f.domRestrict p).finrank_range_add_finrank_ker, range_domRestrict, ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq p, Submodule.map_comap_subtype]

end LinearMap
