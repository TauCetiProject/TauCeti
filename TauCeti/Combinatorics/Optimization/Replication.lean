/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Replication of pairwise optimization problems

Replace each vertex of a finite loopless directed graph by `q` copies and each edge by the
complete bipartite graph between its endpoint clusters. A nonnegative pair cost, depending on
the labels at its endpoints, has infimum multiplied by `q²`. Labels on the copies may vary
arbitrarily within each cluster, and the label type need not be finite. Nonnegative costs
inside clusters do not change the result if equally labelled pairs have cost zero.

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

variable {V A : Type*}

/-- If every section has pair cost at least `d`, the total inter-cluster pair cost is at least
`q² * d`. No sign assumption on the pair costs is needed. -/
theorem sq_mul_le_sum_of_forall_sections [Finite V] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : (V × V) → A → A → ℝ)
    {q : ℕ} (hq : 0 < q) (β : V → Fin q → A) {d : ℝ}
    (hd : ∀ s : V → Fin q, d ≤ ∑ e ∈ E, w e (β e.1 (s e.1)) (β e.2 (s e.2))) :
    (q : ℝ) ^ 2 * d ≤ ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b) := by
  classical
  let := Fintype.ofFinite V
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  rcases E.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · have := hd (fun _ ↦ ⟨0, hq⟩)
    simpa using mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (q : ℝ)) (by simpa using this)
  have hcard : 2 ≤ Fintype.card V := by
    have := card_le_card (by simp : {e.1, e.2} ⊆ (univ : Finset V))
    simpa [hE e he] using this
  have hcount (e : V × V) (he : e ∈ E) :
      ∑ s : V → Fin q, w e (β e.1 (s e.1)) (β e.2 (s e.2)) =
        (q : ℝ) ^ (Fintype.card V - 2) * ∑ a, ∑ b, w e (β e.1 a) (β e.2 b) := by
    have h := Fintype.sum_piFinset_apply_apply (hE e he) (fun _ : V ↦ (univ : Finset (Fin q)))
      (fun a b ↦ w e (β e.1 a) (β e.2 b))
    simpa [prod_const, card_sdiff_of_subset (by simp : {e.1, e.2} ⊆ (univ : Finset V)),
      hE e he, nsmul_eq_mul] using h
  have hsum := sum_le_sum (s := (univ : Finset (V → Fin q))) (fun s _ ↦ hd s)
  have htotal : ∑ s : V → Fin q, ∑ e ∈ E, w e (β e.1 (s e.1)) (β e.2 (s e.2)) =
      (q : ℝ) ^ (Fintype.card V - 2) *
        ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b) := by
    calc
      _ = ∑ e ∈ E, ∑ s : V → Fin q, w e (β e.1 (s e.1)) (β e.2 (s e.2)) :=
        sum_comm
      _ = _ := by rw [mul_sum]; exact sum_congr rfl hcount
  rw [htotal] at hsum
  have hpow : (q : ℝ) ^ Fintype.card V = (q : ℝ) ^ (Fintype.card V - 2) * (q : ℝ) ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  have hpos : 0 < (q : ℝ) ^ (Fintype.card V - 2) := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa [sum_const, Fintype.card_fun, hpow, mul_assoc, mul_comm, mul_left_comm] using hsum

/-- Replication multiplies the infimum of nonnegative pair costs by `q²`, even with
nonnegative within-cluster penalties vanishing on equal labels. The infima range over all
assignments; neither finiteness of the label type nor attainment of the infimum is required.
The statement includes `q = 0`, empty graphs and empty vertex types. -/
theorem ciInf_add_sum_sum_sum_eq_sq_mul_ciInf_sum [Fintype V] [Nonempty A] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : (V × V) → A → A → ℝ)
    (hw : ∀ e ∈ E, ∀ a b, 0 ≤ w e a b)
    (z : V → A → A → ℝ) (hz : ∀ v a b, 0 ≤ z v a b) (hz_diag : ∀ v a, z v a a = 0)
    (q : ℕ) :
    (⨅ β : V → Fin q → A,
      (∑ v, ∑ a : Fin q, ∑ b : Fin q with a < b, z v (β v a) (β v b)) +
        ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) =
      (q : ℝ) ^ 2 * ⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2) := by
  classical
  let f (β : V → A) := ∑ e ∈ E, w e (β e.1) (β e.2)
  let F (β : V → Fin q → A) :=
    (∑ v, ∑ a : Fin q, ∑ b : Fin q with a < b, z v (β v a) (β v b)) +
      ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)
  have hf : BddBelow (Set.range f) := ⟨0, by
    rintro _ ⟨β, rfl⟩
    exact sum_nonneg fun e he ↦ hw e he _ _⟩
  have hF : BddBelow (Set.range F) := ⟨0, by
    rintro _ ⟨β, rfl⟩
    exact add_nonneg (sum_nonneg fun v _ ↦ sum_nonneg fun a _ ↦
      sum_nonneg fun b _ ↦ hz v _ _) (sum_nonneg fun e he ↦
      sum_nonneg fun a _ ↦ sum_nonneg fun b _ ↦ hw e he _ _)⟩
  have hcopy (β : V → A) : F (fun v _ ↦ β v) = (q : ℝ) ^ 2 * f β := by
    simp [F, f, hz_diag, ← mul_sum]
    ring
  refine le_antisymm ?_ ?_
  · rw [Real.mul_iInf_of_nonneg (sq_nonneg (q : ℝ))]
    exact le_ciInf fun β ↦ (ciInf_le hF (fun v _ ↦ β v)).trans_eq (hcopy β)
  · rcases q.eq_zero_or_pos with rfl | hq
    · simp
    · apply le_ciInf
      intro β
      have hsections := E.sq_mul_le_sum_of_forall_sections hE w hq β
        (fun s ↦ ciInf_le hf (fun v ↦ β v (s v)))
      exact hsections.trans (le_add_of_nonneg_left (sum_nonneg fun v _ ↦
        sum_nonneg fun a _ ↦ sum_nonneg fun b _ ↦ hz v _ _))

end Finset
