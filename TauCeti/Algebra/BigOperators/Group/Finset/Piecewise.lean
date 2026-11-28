/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weighted products of conditional factors

`TauCeti.prod_prod_ite_mul_pow` splits a weighted double product of two singleton-supported
factors into one product per selected index. The indices may coincide, so overlapping
contributions can be collected without a case split.
-/

public section

namespace TauCeti

/-- If each of two factors is `1` off its selected index, the double product of their
weighted powers splits into two products at the selected indices, even if they coincide. -/
theorem prod_prod_ite_mul_pow {M ι κ : Type*} [CommMonoid M] [Fintype ι]
    [DecidableEq ι] [Fintype κ] (u v : ι) (f g : κ → M) (a : ι → κ → ℕ) :
    (∏ i, ∏ j, ((if i = u then f j else 1) * (if i = v then g j else 1)) ^ a i j) =
      (∏ j, f j ^ a u j) * ∏ j, g j ^ a v j := by
  rw [Finset.prod_comm]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow, Fintype.prod_ite_eq']

end TauCeti
