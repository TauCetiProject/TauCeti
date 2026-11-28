/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The `ℓ¹`-sum of norms of a finitely supported function

For a finitely supported function `f : α →₀ E` into a seminormed group, the sum
`f.sum fun _ a ↦ ‖a‖` of the norms of its values is its `ℓ¹`-norm. This file records the
estimates that make this sum a seminorm on `α →₀ E` and control it under the operations on finitely
supported functions: it dominates every coordinate norm, is subadditive on binary and finite sums,
is invariant under negation, is multiplied by at most `‖d‖` under multiplication by an integer `d`,
does not increase under `Finsupp.mapDomain`, and is multiplied by at most `C` under
`Finsupp.mapRange` along a map multiplying norms by at most `C`.

These are the estimates on the `ℓ¹`-norm of simplicial chains, which are finitely supported
functions on simplices.

The `ℓ¹`-norm of `h : G →₀ 𝕜` on a magma `G` also bounds the eigenvalues of right convolution
by `h` on bounded functions: if `f : G → E` is bounded and not identically zero, and
`Σ_{g'} h(g') • f(g g') = θ • f(g)` for every `g`, then `‖θ‖ ≤ Σ_g ‖h g‖`
(`Finsupp.norm_le_sum_norm_of_sum_smul_mul_eq_smul`).

Finally, if each member `f i` of a family of functions indexed by the support of `w : ι →₀ 𝕜` is
bounded by a constant multiple of a fixed function `g` on a set, so is the weighted sum
`w.sum fun i c ↦ c • f i x` (`Finsupp.exists_norm_sum_smul_le_of_forall_mem_support`).
-/

public section

namespace Finsupp

variable {α β E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- The `ℓ¹`-sum of norms of a finitely supported function is nonnegative. -/
theorem sum_norm_nonneg (f : α →₀ E) : 0 ≤ f.sum fun _ a ↦ ‖a‖ :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- The `ℓ¹`-sum of norms dominates the norm of every coordinate value. -/
theorem norm_apply_le_sum_norm (f : α →₀ E) (a : α) : ‖f a‖ ≤ f.sum fun _ x ↦ ‖x‖ := by
  by_cases ha : a ∈ f.support
  · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) ha
  · rw [notMem_support_iff.mp ha, norm_zero]; exact sum_norm_nonneg f

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

/-- **The finite-sum triangle inequality** for the `ℓ¹`-sum of norms. -/
theorem sum_norm_sum_le {ι : Type*} (f : ι → α →₀ E) (s : Finset ι) :
    ((∑ i ∈ s, f i).sum fun _ a ↦ ‖a‖) ≤ ∑ i ∈ s, (f i).sum fun _ a ↦ ‖a‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (sum_norm_add_le _ _).trans (add_le_add_right ih _)

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

/-- Let `f` be a bounded, not identically zero function on a magma `G` with values in a normed
group, and `h : G →₀ 𝕜` such that `Σ_{g'} h(g') f(g g') = θ f(g)` for every `g`. Then the
eigenvalue `θ` of right convolution by `h` has norm at most the `ℓ¹` norm `Σ_g ‖h g‖` of `h`. -/
theorem norm_le_sum_norm_of_sum_smul_mul_eq_smul {𝕜 G E : Type*} [SeminormedRing 𝕜] [Mul G]
    [NormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E] {f : G → E}
    (hf : BddAbove (Set.range fun g ↦ ‖f g‖)) (hf₀ : f ≠ 0) (h : G →₀ 𝕜) {θ : 𝕜}
    (hθ : ∀ g, (h.sum fun g' c ↦ c • f (g * g')) = θ • f g) :
    ‖θ‖ ≤ h.sum fun _ c ↦ ‖c‖ := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hf₀
  have hM : 0 < ⨆ g, ‖f g‖ := (norm_pos_iff.2 hg₀).trans_le (le_ciSup hf g₀)
  have key (g : G) : ‖θ‖ * ‖f g‖ ≤ (h.sum fun _ c ↦ ‖c‖) * ⨆ g, ‖f g‖ := by
    rw [← norm_smul, ← hθ g, Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g' _ ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (le_ciSup hf _) (norm_nonneg _)
  have : Nonempty G := ⟨g₀⟩
  refine le_of_mul_le_mul_right ?_ hM
  rw [Real.mul_iSup_of_nonneg (norm_nonneg θ)]
  exact ciSup_le key

/-- If, on a set `s`, each function `f i` with `i` in the support of the weights `w` is bounded in
norm by a constant multiple of `g`, then so is the weighted sum `w.sum fun i c ↦ c • f i x`.
The constants may depend on `i`, and `g` need not be nonnegative. -/
theorem exists_norm_sum_smul_le_of_forall_mem_support {ι X 𝕜 : Type*} [SeminormedRing 𝕜]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (w : ι →₀ 𝕜) (f : ι → X → E) (g : X → ℝ) (s : Set X)
    (h : ∀ i ∈ w.support, ∃ C : ℝ, ∀ x ∈ s, ‖f i x‖ ≤ C * g x) :
    ∃ C : ℝ, ∀ x ∈ s, ‖w.sum fun i c ↦ c • f i x‖ ≤ C * g x := by
  classical
  choose C hC using h
  let D (i : ι) := if hi : i ∈ w.support then C i hi else 0
  refine ⟨∑ i ∈ w.support, ‖w i‖ * D i, fun x hx ↦ ?_⟩
  rw [sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hD : D i = C i hi := dite_eq_left hi
  rw [mul_assoc, hD]
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hC i hi x hx) (norm_nonneg _))

end Finsupp
