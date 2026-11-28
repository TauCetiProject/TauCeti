/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Star
public import Mathlib.Analysis.RCLike.Basic

/-!
# Proper involution on real and complex group algebras

The coefficient at the group identity of `star a * a` is the sum of the squared norms of
the coefficients of `a`. Consequently the involution is proper, also for infinite groups:
each group-algebra element has finite support. In particular a central idempotent is fixed
by the involution, so it acts as an orthogonal projector in unitary representations.
-/

public section

namespace MonoidAlgebra

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G]

/-- The real part of the identity coefficient of `star a * a` is the squared coefficient norm. -/
theorem re_coeff_star_mul_self_one (a : MonoidAlgebra 𝕜 G) :
    RCLike.re ((star a * a).coeff 1) = ∑ g ∈ a.coeff.support, ‖a.coeff g‖ ^ 2 := by
  rw [coeff_mul_apply_right]
  simp only [Finsupp.sum, one_mul, coeff_star, inv_inv, RCLike.star_def, map_sum,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The group algebra involution is proper: `star a * a = 0` forces `a = 0`. -/
instance : IsProperStar (MonoidAlgebra 𝕜 G) where
  eq_zero_of_star_mul_self_eq_zero {a} ha := by
    have h : (∑ g ∈ a.coeff.support, ‖a.coeff g‖ ^ 2) = 0 := by
      simpa [ha] using (re_coeff_star_mul_self_one a).symm
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦ sq_nonneg ‖a.coeff g‖).mp h
    ext g
    by_cases hg : g ∈ a.coeff.support
    · simpa using hz g hg
    · simpa using Finsupp.notMem_support_iff.mp hg

end MonoidAlgebra
