/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dimension of a product of modules

Mathlib's `Module.finrank_prod` computes the dimension of `M × M'` for finite free modules. For
`M × M` no finiteness is needed: if `M` is not finite then neither is `M × M`, and both
dimensions are `0` by convention. So `finrank (M × M) = 2 * finrank M` for every free module `M`
over a semiring with the strong rank condition (`Module.finrank_prod_self`).

A free module of positive dimension is finite, so the dimensions of factors of dimensions
`m + 1` and `n + 1` add without a separate finiteness hypothesis
(`Module.finrank_prod_eq_succ`). The sum is written `d + 1` together with a proof of
`(m + 1) + (n + 1) = d + 1`, the form used for products of local orientations.

For a finite-dimensional vector space `V` over a field `K`, the space `V × V^* × K`, the linear
model of the one-jet space of `V`, has dimension `2 * finrank K V + 1`
(`Module.finrank_prod_dual_prod_self`).

Without freeness, rank is still additive on products over any ring with the rank-nullity
property, for instance any domain: the first projection `M × N → M` is onto with kernel `N`
(`Module.rank_prod_of_hasRankNullity`). For modules of finite rank this gives the same formula
for `finrank` (`Module.finrank_prod_of_hasRankNullity`).
-/

public section

namespace Module

variable (R M : Type*) [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  [Module.Free R M]

/-- The dimension of `M × M` is twice that of `M`, whether or not `M` is finite. -/
theorem finrank_prod_self : finrank R (M × M) = 2 * finrank R M := by
  by_cases hM : Module.Finite R M
  · rw [Module.finrank_prod, two_mul]
  · have : ¬ Module.Finite R (M × M) := fun h =>
      hM (Module.Finite.of_surjective (LinearMap.fst R M M) Prod.fst_surjective)
    rw [finrank_of_not_finite hM, finrank_of_not_finite this, mul_zero]

variable {R M} {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module.Free R M'] {m n d : ℕ}

/-- If `M` and `M'` have dimensions `m + 1` and `n + 1`, where `(m + 1) + (n + 1) = d + 1`, then
`M × M'` has dimension `d + 1`. Both factors are finite because their dimensions are positive. -/
theorem finrank_prod_eq_succ (hM : finrank R M = m + 1) (hM' : finrank R M' = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) : finrank R (M × M') = d + 1 := by
  have := finite_of_finrank_eq_succ hM
  have := finite_of_finrank_eq_succ hM'
  rw [Module.finrank_prod, hM, hM', hd]

/-- The dimension of `V × V^* × K` is `2 * finrank K V + 1` for a finite-dimensional vector space
`V` over a field `K`. -/
theorem finrank_prod_dual_prod_self (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] : finrank K (V × Dual K V × K) = 2 * finrank K V + 1 := by
  rw [Module.finrank_prod, Module.finrank_prod, Subspace.dual_finrank_eq, finrank_self]
  omega

section RankNullity

universe u

variable {R : Type*} [Ring R] (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [HasRankNullity.{u} R]

/-- Over a ring with the rank-nullity property, rank is additive on products: the first
projection `M × N → M` is onto with kernel `N`. No freeness or finiteness is needed. -/
theorem rank_prod_of_hasRankNullity :
    Module.rank R (M × N) = Module.rank R M + Module.rank R N := by
  rw [← (LinearMap.fst R M N).rank_range_add_rank_ker, LinearMap.range_eq_top.2 Prod.fst_surjective,
    rank_top, LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective]

variable {M N} in
/-- Over a ring with the rank-nullity property, `finrank` is additive on products of modules of
finite rank. -/
theorem finrank_prod_of_hasRankNullity (hM : Module.rank R M < Cardinal.aleph0)
    (hN : Module.rank R N < Cardinal.aleph0) :
    finrank R (M × N) = finrank R M + finrank R N := by
  simp only [finrank, rank_prod_of_hasRankNullity, Cardinal.toNat_add hM hN]

end RankNullity

end Module
