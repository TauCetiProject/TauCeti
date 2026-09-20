/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# The normalisation of an invariant form against the coroots

Mathlib's `RootPairing.InvariantForm.two_mul_apply_root_root` computes an invariant form on two
roots through the Cartan integers: `2 ⟨αᵢ, αⱼ⟩ = ⟨αᵢ, αⱼ^∨⟩ ⟨αⱼ, αⱼ⟩`. Nothing in that argument
uses that the first argument is a root, and this file records the identity for an arbitrary
vector of the weight space:

`2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩`,

that is, the coroot `α^∨` is `2α / ⟨α, α⟩` under the identification of weights and coweights that
the form provides. It converts any expression in the pairings `⟨x, α⟩` of an invariant form into
one in the coroot values `⟨x, α^∨⟩`, which is how the Weyl dimension formula passes from the
form in which it is proved to its division-free integer statement.

## Main results

* `RootPairing.InvariantForm.two_mul_apply_root`: `2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩` for every `x`.
-/

public section

namespace RootPairing.InvariantForm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} (B : P.InvariantForm)

/-- **The normalisation of an invariant form against a coroot**: `2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩`
for every vector `x` of the weight space. This extends
`RootPairing.InvariantForm.two_mul_apply_root_root` from the roots to all of `M`. -/
theorem two_mul_apply_root (x : M) (j : ι) :
    2 * B.form x (P.root j) = P.coroot' j x * B.form (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j x (P.root j)]
  rw [reflection_apply, reflection_apply_self, LinearMap.map_sub₂, LinearMap.map_smul₂,
    smul_eq_mul, map_neg, map_neg, mul_neg, neg_sub_neg]

end RootPairing.InvariantForm
