/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Norms of monomials

For a point `x : σ → R` of a normed commutative ring with `‖1‖ = 1` and an exponent
`t : σ →₀ ℕ`, the monomial `xᵗ = ∏ᵢ xᵢ ^ tᵢ` has norm at most `cᵗ = ∏ᵢ cᵢ ^ tᵢ` whenever
`‖xᵢ‖ ≤ cᵢ` for every `i`, that is, whenever `x` lies in the closed polydisc of polyradius `c`.

## Main results

* `Finsupp.norm_prod_pow_le`: the norm of a monomial on the closed polydisc of polyradius `c` is
  at most its weight `cᵗ`.
-/

public section

namespace Finsupp

/-- On the closed polydisc `‖xᵢ‖ ≤ cᵢ`, the monomial `xᵗ = ∏ᵢ xᵢ ^ tᵢ` has norm at most
`cᵗ = ∏ᵢ cᵢ ^ tᵢ`. -/
theorem norm_prod_pow_le {σ R : Type*} [NormedCommRing R] [NormOneClass R] {x : σ → R}
    {c : σ → ℝ} (hx : ∀ i, ‖x i‖ ≤ c i) (t : σ →₀ ℕ) :
    ‖t.prod (x · ^ ·)‖ ≤ t.prod (c · ^ ·) :=
  (Finset.norm_prod_le _ _).trans <| Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hx i) _)

end Finsupp

end
