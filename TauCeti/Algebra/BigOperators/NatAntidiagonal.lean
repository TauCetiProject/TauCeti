/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Iterated products over antidiagonals

A product over the triples `(a, b, c)` with `a + b + c = n` can be computed by first splitting `n`
as `(a + b) + c` and then `a + b`, or by first splitting `n` as `a + (b + c)` and then `b + c`.
This associativity of the antidiagonal convolution is what makes a comultiplication
`xₙ ↦ ∑_{i + j = n} xᵢ ⊗ xⱼ` coassociative.
-/

public section

namespace Finset.Nat

/-- **Associativity of the antidiagonal convolution**: the product over `a + b + c = n` taken as
`(a + b) + c` agrees with the product taken as `a + (b + c)`. -/
@[to_additive /-- **Associativity of the antidiagonal convolution**: the sum over `a + b + c = n`
taken as `(a + b) + c` agrees with the sum taken as `a + (b + c)`. -/]
theorem prod_antidiagonal_prod_antidiagonal_fst {M : Type*} [CommMonoid M] (n : ℕ)
    (f : ℕ → ℕ → ℕ → M) :
    ∏ p ∈ antidiagonal n, ∏ q ∈ antidiagonal p.1, f q.1 q.2 p.2 =
      ∏ p ∈ antidiagonal n, ∏ q ∈ antidiagonal p.2, f p.1 q.1 q.2 := by
  rw [prod_sigma', prod_sigma']
  -- reindex the triples: `((a + b, c), (a, b)) ↦ ((a, b + c), (b, c))`
  apply prod_nbij' (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩) <;> aesop (add simp [add_assoc])

end Finset.Nat
