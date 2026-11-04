/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero

/-!
# The `ℓ¹`-sum of norms of a finitely supported function

For a finitely supported function `f : α →₀ E` into a seminormed group, the sum
`f.sum fun _ a ↦ ‖a‖` of the norms of its values is its `ℓ¹`-norm. This file records the
estimates that make this sum a seminorm on `α →₀ E` and control it under the operations on finitely
supported functions: it is subadditive, invariant under negation, multiplied by at most `‖d‖`
under multiplication by an integer `d`, does not increase under `Finsupp.mapDomain`, and is
multiplied by at most `C` under `Finsupp.mapRange` along a map multiplying norms by at most `C`.

These are the estimates on the `ℓ¹`-norm of simplicial chains, which are finitely supported
functions on simplices.
-/

public section

namespace Finsupp

variable {α β E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- The `ℓ¹`-sum of norms of a finitely supported function is nonnegative. -/
theorem sum_norm_nonneg (f : α →₀ E) : 0 ≤ f.sum fun _ a ↦ ‖a‖ :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- The `ℓ¹`-sum of norms can be computed over any finite set containing the support. -/
theorem sum_norm_eq_sum_of_support_subset (f : α →₀ E) {s : Finset α} (hs : f.support ⊆ s) :
    (f.sum fun _ a ↦ ‖a‖) = ∑ a ∈ s, ‖f a‖ :=
  sum_of_support_subset f hs _ fun _ _ ↦ norm_zero

/-- **The triangle inequality** for the `ℓ¹`-sum of norms. -/
theorem sum_norm_add_le (f g : α →₀ E) :
    ((f + g).sum fun _ a ↦ ‖a‖) ≤ (f.sum fun _ a ↦ ‖a‖) + g.sum fun _ a ↦ ‖a‖ := by
  classical
  rw [sum_norm_eq_sum_of_support_subset (f + g) support_add,
    sum_norm_eq_sum_of_support_subset f Finset.subset_union_left,
    sum_norm_eq_sum_of_support_subset g Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ ↦ norm_add_le (f a) (g a)

/-- The `ℓ¹`-sum of norms is invariant under negation. -/
@[simp]
theorem sum_norm_neg (f : α →₀ E) : ((-f).sum fun _ a ↦ ‖a‖) = f.sum fun _ a ↦ ‖a‖ := by
  rw [sum_neg_index fun _ ↦ norm_zero]
  simp only [norm_neg]

/-- Multiplying a finitely supported function by an integer `d` multiplies its `ℓ¹`-sum of norms by
at most `‖d‖`. -/
theorem sum_norm_zsmul_le (d : ℤ) (f : α →₀ E) :
    ((d • f).sum fun _ a ↦ ‖a‖) ≤ ‖d‖ * f.sum fun _ a ↦ ‖a‖ := by
  rw [sum_norm_eq_sum_of_support_subset (d • f) support_smul, sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ ↦ by
    simpa only [coe_smul, Pi.smul_apply] using norm_zsmul_le d (f a)

/-- **Pushing a finitely supported function forward does not increase its `ℓ¹`-sum of norms.** -/
theorem sum_norm_mapDomain_le (φ : α → β) (f : α →₀ E) :
    ((mapDomain φ f).sum fun _ a ↦ ‖a‖) ≤ f.sum fun _ a ↦ ‖a‖ := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
    have hdisj : Disjoint (single a b).support f.support := by
      rw [support_single a hb, Finset.disjoint_singleton_left]
      exact ha
    rw [mapDomain_add, mapDomain_single, sum_add_index_of_disjoint hdisj,
      sum_single_index (h := fun _ x ↦ ‖x‖) norm_zero]
    refine (sum_norm_add_le _ _).trans ?_
    rw [sum_single_index (h := fun _ x ↦ ‖x‖) norm_zero]
    exact add_le_add_right ih _

/-- **Changing the values along a map multiplying norms by at most `C`** multiplies the `ℓ¹`-sum
of norms by at most `C`. -/
theorem sum_norm_mapRange_le {ψ : E → F} (hψ : ψ 0 = 0) {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C * ‖x‖)
    (f : α →₀ E) : ((mapRange ψ hψ f).sum fun _ a ↦ ‖a‖) ≤ C * f.sum fun _ a ↦ ‖a‖ := by
  rw [sum_mapRange_index fun _ ↦ norm_zero, sum, sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ ↦ hC (f a)

end Finsupp
