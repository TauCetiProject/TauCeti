/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Entrywise division with remainder of exponents

Dividing every entry of an exponent `α : σ →₀ ℕ` by `p` with remainder writes `α` as
`p • μ + ν` with `ν i < p` for all `i`, where `μ` and `ν` are the entrywise quotients and
remainders.

## Main results

* `Finsupp.nsmul_mapRange_div_add_mapRange_mod`: `p • (α / p) + α % p = α` entrywise.
-/

public section

namespace Finsupp

variable {σ : Type*} (p : ℕ)

/-- Every exponent is `p • μ + ν` for its entrywise quotients `μ` and remainders `ν` by `p`. -/
theorem nsmul_mapRange_div_add_mapRange_mod (α : σ →₀ ℕ) :
    p • α.mapRange (· / p) (Nat.zero_div p) + α.mapRange (· % p) (Nat.zero_mod p) = α := by
  ext i
  simp [Nat.div_add_mod]

end Finsupp
