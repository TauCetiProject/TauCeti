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

The identity also controls vectors of equal length that differ by a natural combination of
roots: expanding `⟨y - x, y - x⟩` for `⟨x, x⟩ = ⟨y, y⟩` shows that some root occurring in
`y - x` has negative coroot value on `x`. For minuscule weights this is the existence of a raising
step towards a higher weight.

## Main results

* `RootPairing.InvariantForm.two_mul_apply_root`: `2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩` for every `x`.
* `RootPairing.InvariantForm.exists_pos_and_coroot'_neg_of_apply_self_eq`: if `x` and `y` have
  equal length and `y - x`, of positive length, is a natural combination of roots of nonnegative
  length, some root with positive coefficient has negative coroot value on `x`.
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
  -- The reflection in `α := P.root j` preserves the form, and it sends `x` to `x - ⟨x, α^∨⟩ α`
  -- and `α` to `-α`.
  have h : B.form (x - P.coroot' j x • P.root j) (-P.root j) = B.form x (P.root j) := by
    rw [← reflection_apply_self, ← reflection_apply]
    exact B.apply_reflection_reflection j x (P.root j)
  -- Expanding the left-hand side by bilinearity turns that into the claim.
  rw [LinearMap.map_sub₂, LinearMap.map_smul₂, map_neg, map_neg, smul_eq_mul] at h
  linear_combination -h

/-- **A root lowering a vector of the same length.** Let `x` and `y` have the same length for an
invariant form whose roots have nonnegative length, and let `y - x`, of positive length, be a
natural combination `∑ j ∈ s, c j • α_{f j}` of roots. Then some root `α_{f j}` with `c j > 0` has
negative coroot value on `x`. -/
theorem exists_pos_and_coroot'_neg_of_apply_self_eq [LinearOrder R] [IsStrictOrderedRing R]
    (hroot : ∀ i, 0 ≤ B.form (P.root i) (P.root i)) {x y : M}
    (hxy : B.form x x = B.form y y) (hpos : 0 < B.form (y - x) (y - x))
    {κ : Type*} {s : Finset κ} {f : κ → ι} {c : κ → ℕ}
    (h : y - x = ∑ j ∈ s, c j • P.root (f j)) :
    ∃ j ∈ s, 0 < c j ∧ P.coroot' (f j) x < 0 := by
  -- Equal lengths give `⟨y - x, y - x⟩ = -2 ⟨x, y - x⟩`, so `2 ⟨x, y - x⟩` is negative.
  have hsymm : B.form y x = B.form x y := B.symm.eq y x
  have hneg : 2 * B.form x (y - x) < 0 := by
    simp only [map_sub, LinearMap.sub_apply] at hpos ⊢
    linarith
  -- Expanding `y - x` writes `2 ⟨x, y - x⟩` as a sum of `c j ⟨x, α_{f j}^∨⟩ ⟨α_{f j}, α_{f j}⟩`.
  have hsum : 2 * B.form x (y - x) =
      ∑ j ∈ s, (c j : R) * (P.coroot' (f j) x * B.form (P.root (f j)) (P.root (f j))) := by
    rw [h, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_nsmul, nsmul_eq_mul, mul_left_comm, B.two_mul_apply_root]
  rw [hsum] at hneg
  by_contra! hnonneg
  refine hneg.not_ge (Finset.sum_nonneg fun j hj ↦ ?_)
  rcases (c j).eq_zero_or_pos with hc | hc
  · simp [hc]
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hnonneg j hj hc) (hroot _))

end RootPairing.InvariantForm
