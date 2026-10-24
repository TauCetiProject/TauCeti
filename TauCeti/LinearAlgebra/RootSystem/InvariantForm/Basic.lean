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
* `RootPairing.InvariantForm.reflTransGen_of_sub_eq_sum`: iterating such raising steps joins two
  vectors of an injective family of equal length whose difference is a natural combination of
  roots.
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

/-- **Raising paths between vectors of equal length.** Let `μ` be an injective family of vectors of
equal length, indexed by a type with a well-founded order, for an invariant form that is positive
on the nonzero vectors of the root span and whose roots have nonnegative length. Suppose that
whenever a root `α_{f j}` has negative coroot value on `μ a`, an `r`-step leads from `a` to a
smaller index `a'` with `μ a' = μ a + α_{f j}`. Then `r`-paths lead from `a` to every `b` for
which `μ b - μ a` is a natural combination of the roots `α_{f j}`. -/
theorem reflTransGen_of_sub_eq_sum [LinearOrder R] [IsStrictOrderedRing R]
    (hroot : ∀ i, 0 ≤ B.form (P.root i) (P.root i))
    (hpos : ∀ v ∈ P.rootSpan R, v ≠ 0 → 0 < B.form v v)
    {X : Type*} [LT X] [WellFoundedLT X] {μ : X → M} (hμ : Function.Injective μ)
    (hlen : ∀ a b, B.form (μ a) (μ a) = B.form (μ b) (μ b))
    {κ : Type*} [Fintype κ] {f : κ → ι} {r : X → X → Prop}
    (hstep : ∀ a j, P.coroot' (f j) (μ a) < 0 → ∃ a' < a, r a a' ∧ μ a' = μ a + P.root (f j))
    {a b : X} {c : κ → ℕ} (h : μ b - μ a = ∑ j, c j • P.root (f j)) :
    Relation.ReflTransGen r a b := by
  classical
  induction a using WellFoundedLT.induction generalizing c with
  | ind a ih =>
  by_cases hab : a = b
  · subst hab
    exact .refl
  have hspan : μ b - μ a ∈ P.rootSpan R := h ▸ Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_of_tower_mem _ (c j) (Submodule.subset_span (Set.mem_range_self (f j)))
  obtain ⟨j, -, hcj, hj⟩ := B.exists_pos_and_coroot'_neg_of_apply_self_eq hroot (hlen a b)
    (hpos _ hspan (sub_ne_zero.mpr (hμ.ne (Ne.symm hab)))) h
  obtain ⟨a', ha', hr, hμa'⟩ := hstep a j hj
  refine .head hr (ih a' ha' (c := Function.update c j (c j - 1)) ?_)
  -- Lowering the coefficient of `α_{f j}` by one removes one copy of `α_{f j}` from the sum.
  have hsum : ∑ i, c i • P.root (f i) =
      (∑ i, Function.update c j (c j - 1) i • P.root (f i)) + P.root (f j) := by
    have herase : ∑ i ∈ Finset.univ.erase j, Function.update c j (c j - 1) i • P.root (f i) =
        ∑ i ∈ Finset.univ.erase j, c i • P.root (f i) :=
      Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self, herase]
    conv_lhs => rw [← Nat.sub_add_cancel hcj, add_nsmul, one_nsmul]
    abel
  rw [hμa', sub_add_eq_sub_sub, h, hsum, add_sub_cancel_right]

end RootPairing.InvariantForm
