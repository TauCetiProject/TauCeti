/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz

/-!
# Ideals of rational points

For a rational point `a : σ → k` of affine space over a field `k`, the vanishing ideal
`MvPolynomial.vanishingIdeal k {a}` is the kernel of evaluation at `a`.

## Main results

* `MvPolynomial.vanishingIdeal_singleton_eq_ker_eval`: the vanishing ideal of a rational point is
  the kernel of evaluation at that point.

## References

* L. Alpöge and L. Sernau, grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0,
  Copyright 2026 Anthropic, PBC), `src/Lib/General/Algebra/MultivariatePolynomials.lean`
  (`New.exists_le_weight_of_mem_vanishingIdeal_pow`).
-/

public section

namespace MvPolynomial

/-- The vanishing ideal of a rational point is the kernel of evaluation at that point. -/
theorem vanishingIdeal_singleton_eq_ker_eval {σ k : Type*} [Field k] (a : σ → k) :
    vanishingIdeal k {a} = RingHom.ker (eval a) := by
  ext f
  simp only [mem_vanishingIdeal_singleton_iff, RingHom.mem_ker, aeval_eq_eval]

end MvPolynomial
