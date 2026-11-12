/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Ring

/-!
# Replication of pairwise optimization problems

Replace each vertex of a loopless directed graph with a finite edge set by `q` copies and
each edge by the complete bipartite graph between its endpoint clusters. A nonnegative pair
cost, depending on the labels at its endpoints, has infimum multiplied by `q²`. Labels may vary
arbitrarily within each cluster, and the label type need not be finite. Nonnegative costs
inside clusters do not change the result if they vanish on cluster-constant assignments.

The lower bound averages over sections choosing one copy of every vertex. The upper bound
copies a label assignment constantly across each cluster. In particular, the argument applies
to gauge costs of group-valued cochains, without assuming that an optimal gauge exists.

## References

* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Lemma 6 (the section argument for replicated gauge costs).
-/

public section

open Finset

namespace Finset

variable {V A ι M : Type*}

/-- If every section has pair cost at least `d`, the total inter-cluster pair cost is at least
`Fintype.card ι ^ 2` copies of `d`. Only the edge set is required to be finite, and no sign
assumption on the pair costs is needed. -/
theorem card_sq_nsmul_le_sum_of_forall_sections [Fintype ι] [AddCommMonoid M]
    [LinearOrder M] [IsOrderedCancelAddMonoid M] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → ι → ι → M) {d : M}
    (hd : ∀ s : V → ι, d ≤ ∑ e ∈ E, w e (s e.1) (s e.2)) :
    (Fintype.card ι ^ 2) • d ≤ ∑ e ∈ E, ∑ a, ∑ b, w e a b := by
  classical
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  let S := E.biUnion fun e ↦ {e.1, e.2}
  have hmem (e : V × V) (he : e ∈ E) : e.1 ∈ S ∧ e.2 ∈ S := by
    constructor <;> exact mem_biUnion.mpr ⟨e, he, by simp⟩
  let extend (s : S → ι) (v : V) := if hv : v ∈ S then s ⟨v, hv⟩ else Classical.choice hι
  rcases E.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · have hd0 : d ≤ 0 := by simpa using hd (fun _ ↦ Classical.choice hι)
    simpa using nsmul_nonpos hd0 (Fintype.card ι ^ 2)
  have hcard : 2 ≤ Fintype.card S := by
    have hne : (⟨e.1, (hmem e he).1⟩ : S) ≠ ⟨e.2, (hmem e he).2⟩ :=
      fun h ↦ hE e he (congrArg Subtype.val h)
    have := card_le_card (subset_univ _ :
      {(⟨e.1, (hmem e he).1⟩ : S), (⟨e.2, (hmem e he).2⟩ : S)} ⊆ univ)
    simpa [hne] using this
  have hcount (e : V × V) (he : e ∈ E) :
      ∑ s : S → ι, w e (extend s e.1) (extend s e.2) =
        (Fintype.card ι ^ (Fintype.card S - 2)) • ∑ a, ∑ b, w e a b := by
    have hne : (⟨e.1, (hmem e he).1⟩ : S) ≠ ⟨e.2, (hmem e he).2⟩ :=
      fun h ↦ hE e he (congrArg Subtype.val h)
    have h := Fintype.sum_piFinset_apply_apply hne (fun _ : S ↦ (univ : Finset ι)) (w e)
    have hsize : #(univ \ {(⟨e.1, (hmem e he).1⟩ : S),
        (⟨e.2, (hmem e he).2⟩ : S)}) = Fintype.card S - 2 := by
      rw [card_sdiff_of_subset (subset_univ _)]
      simp [hne]
    simp only [prod_const, card_univ, hsize] at h
    simpa [extend, (hmem e he).1, (hmem e he).2] using h
  have hsum := sum_le_sum (s := (univ : Finset (S → ι))) (fun s _ ↦ hd (extend s))
  have htotal : ∑ s : S → ι, ∑ e ∈ E, w e (extend s e.1) (extend s e.2) =
      (Fintype.card ι ^ (Fintype.card S - 2)) • ∑ e ∈ E, ∑ a, ∑ b, w e a b := by
    rw [sum_comm, ← sum_nsmul]
    exact sum_congr rfl hcount
  rw [htotal] at hsum
  have hpow : Fintype.card ι ^ Fintype.card S =
      Fintype.card ι ^ (Fintype.card S - 2) * Fintype.card ι ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  apply (nsmul_le_nsmul_iff_right
    (pow_ne_zero (Fintype.card S - 2) (Fintype.card_ne_zero (α := ι)))).mp
  simpa only [sum_const, card_univ, Fintype.card_fun, hpow, mul_smul] using hsum

/-- Replication multiplies the infimum of nonnegative pair costs by the square of the number
of copies, even with a nonnegative penalty vanishing on cluster-constant assignments.
Neither the vertex type nor the label type must be finite, and no infimum need be attained.
The statement includes empty copy types, empty graphs and empty vertex types. -/
theorem ciInf_add_sum_eq_card_sq_mul_ciInf_sum [Fintype ι] [Nonempty A] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → ℝ)
    (hw : ∀ e ∈ E, ∀ a b, 0 ≤ w e a b)
    (c : (V → ι → A) → ℝ) (hc : ∀ β, 0 ≤ c β)
    (hc_const : ∀ β : V → A, c (fun v _ ↦ β v) = 0) :
    (⨅ β : V → ι → A, c β + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) =
      (Fintype.card ι : ℝ) ^ 2 * ⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2) := by
  classical
  let f (β : V → A) := ∑ e ∈ E, w e (β e.1) (β e.2)
  let F (β : V → ι → A) := c β + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)
  have hf : BddBelow (Set.range f) := ⟨0, by
    rintro _ ⟨β, rfl⟩
    exact sum_nonneg fun e he ↦ hw e he _ _⟩
  have hF : BddBelow (Set.range F) := ⟨0, by
    rintro _ ⟨β, rfl⟩
    exact add_nonneg (hc β) (sum_nonneg fun e he ↦
      sum_nonneg fun a _ ↦ sum_nonneg fun b _ ↦ hw e he _ _)⟩
  have hcopy (β : V → A) : F (fun v _ ↦ β v) = (Fintype.card ι : ℝ) ^ 2 * f β := by
    simp [F, f, hc_const, ← mul_sum]
    ring
  refine le_antisymm ?_ ?_
  · rw [Real.mul_iInf_of_nonneg (sq_nonneg (Fintype.card ι : ℝ))]
    exact le_ciInf fun β ↦ (ciInf_le hF (fun v _ ↦ β v)).trans_eq (hcopy β)
  · apply le_ciInf
    intro β
    have hsections := E.card_sq_nsmul_le_sum_of_forall_sections hE
      (fun e a b ↦ w e (β e.1 a) (β e.2 b))
      (fun s ↦ ciInf_le hf (fun v ↦ β v (s v)))
    have hbound : (Fintype.card ι : ℝ) ^ 2 * iInf f ≤
        ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b) := by
      simpa [nsmul_eq_mul, Nat.cast_pow] using hsections
    exact hbound.trans (le_add_of_nonneg_left (hc β))

/-- The infimum of nonnegative pair costs is multiplied by the square of the number of copies
when every edge is replaced by all pairs of copies of its endpoints. -/
theorem ciInf_sum_eq_card_sq_mul_ciInf_sum [Fintype ι] [Nonempty A] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → ℝ)
    (hw : ∀ e ∈ E, ∀ a b, 0 ≤ w e a b) :
    (⨅ β : V → ι → A, ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) =
      (Fintype.card ι : ℝ) ^ 2 * ⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2) := by
  simpa using E.ciInf_add_sum_eq_card_sq_mul_ciInf_sum hE w hw
    (fun _ : V → ι → A ↦ 0) (fun _ ↦ le_rfl) (fun _ ↦ rfl)

end Finset
