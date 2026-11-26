/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Algebra.Polynomial.Splits

/-!
# Commonly interlaced real polynomials

The real roots of a real polynomial `p`, counted with multiplicity and listed in nonincreasing
order, form the list `p.sortedRoots`; its entry of index `j` is the `(j + 1)`-st largest root.

A family `f : ι → ℝ[X]` is *commonly interlaced* (`TauCeti.CommonlyInterlaced`) when every member
splits over `ℝ` and, for all members `f i`, `f i'` and every `j` with `j + 1 < natDegree (f i)`,
the `(j + 2)`-nd largest root of `f i` is at most the `(j + 1)`-st largest root of `f i'`. For
real-rooted polynomials of one degree `n`, this says that the largest roots of all members lie in
one interval, the second largest roots in the next interval below it, and so on. Marcus, Spielman
and Srivastava define common interlacing as the existence of one polynomial of degree `n - 1`
interlacing every member, and remark that for real-rooted polynomials of degree `n` this is the
condition used here.

The main result is their lemma on a single level of an interlacing family: if the members of a
nonempty finite commonly interlaced family have positive leading coefficients, then some member
has all its roots at most some root of the sum of the family. The member whose largest root is
smallest works: at that root every member is nonpositive, at the largest of the largest roots
every member is nonnegative, and the sum has a root in between by the intermediate value theorem.
Only the comparison of second largest roots with largest roots enters the proof.

## Main definitions

* `Polynomial.sortedRoots`: the real roots of a real polynomial in nonincreasing order.
* `TauCeti.CommonlyInterlaced`: a family of real-rooted polynomials with a common interlacing.

## Main results

* `TauCeti.exists_isRoot_le_of_commonlyInterlaced`: in a nonempty finite commonly interlaced
  family with positive leading coefficients, some member has every root at most some root of the
  sum of the family.

## References

* A. W. Marcus, D. A. Spielman, N. Srivastava, *Interlacing families I: bipartite Ramanujan
  graphs of all degrees*, Ann. of Math. 182 (2015), 307–325; arXiv:1304.4132, Definition 4.1 and
  Lemma 4.2.
-/

public section

open Finset

namespace Polynomial

/-- The real roots of a real polynomial, counted with multiplicity, in nonincreasing order: the
entry of index `j` is the `(j + 1)`-st largest root. The zero polynomial has no roots in Mathlib's
convention, so its list is empty. -/
noncomputable def sortedRoots (p : ℝ[X]) : List ℝ :=
  p.roots.sort (· ≥ ·)

variable {p : ℝ[X]} {x : ℝ}

/-- The sorted roots of `p` are its roots, as a multiset. -/
@[simp]
theorem coe_sortedRoots (p : ℝ[X]) : (p.sortedRoots : Multiset ℝ) = p.roots :=
  Multiset.sort_eq _ _

/-- The sorted roots of `p` are its roots. -/
@[simp]
theorem mem_sortedRoots : x ∈ p.sortedRoots ↔ x ∈ p.roots :=
  Multiset.mem_sort _

/-- `p.sortedRoots` lists every root of `p` as often as its multiplicity. -/
@[simp]
theorem length_sortedRoots (p : ℝ[X]) : p.sortedRoots.length = p.roots.card :=
  Multiset.length_sort _

/-- The sorted roots of `p` are in nonincreasing order. -/
theorem pairwise_sortedRoots (p : ℝ[X]) : p.sortedRoots.Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

/-- The sorted roots of `p` are the only nonincreasing list with the roots of `p` as its
multiset. -/
theorem sortedRoots_eq_iff {l : List ℝ} :
    p.sortedRoots = l ↔ l.Pairwise (· ≥ ·) ∧ (l : Multiset ℝ) = p.roots := by
  refine ⟨fun h ↦ h ▸ ⟨pairwise_sortedRoots p, coe_sortedRoots p⟩, fun ⟨hl, hlp⟩ ↦ ?_⟩
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba ↦ le_antisymm hba hab)
    (pairwise_sortedRoots p) hl ?_
  rw [← Multiset.coe_eq_coe, hlp, coe_sortedRoots]

/-- Within range, each entry of `p.sortedRoots` is at most the one before it. -/
theorem sortedRoots_getD_succ_le_getD {j : ℕ} (hj : j + 1 < p.sortedRoots.length) :
    p.sortedRoots.getD (j + 1) 0 ≤ p.sortedRoots.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (Nat.lt_of_succ_lt hj), Option.getD_some]
  exact List.pairwise_iff_getElem.1 (pairwise_sortedRoots p) _ _ _ _ (Nat.lt_succ_self j)

/-- Every root of `p` is at most the head of `p.sortedRoots`, its largest root. -/
theorem le_sortedRoots_getD_zero (hx : x ∈ p.roots) : x ≤ p.sortedRoots.getD 0 0 := by
  rw [← mem_sortedRoots] at hx
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hx)
  have hp := pairwise_sortedRoots p
  rw [hal] at hx hp ⊢
  rcases List.mem_cons.1 hx with rfl | hx
  · exact le_rfl
  · exact List.rel_of_pairwise_cons hp hx

/-- A polynomial with a root has its largest root `p.sortedRoots.getD 0 0` among its roots. -/
theorem sortedRoots_getD_zero_mem_roots (hp : p.roots ≠ 0) : p.sortedRoots.getD 0 0 ∈ p.roots := by
  have hl : p.sortedRoots ≠ [] := fun h ↦ hp (by rw [← coe_sortedRoots, h, Multiset.coe_nil])
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hl
  rw [← mem_sortedRoots, hal]
  simp

/-- Once the largest root is removed, every remaining root of `p` is at most the second largest
root `p.sortedRoots.getD 1 0`. -/
theorem le_sortedRoots_getD_one_of_mem_erase (hx : x ∈ p.roots.erase (p.sortedRoots.getD 0 0)) :
    x ≤ p.sortedRoots.getD 1 0 := by
  rw [← coe_sortedRoots] at hx
  have hp := pairwise_sortedRoots p
  generalize p.sortedRoots = l at hx hp ⊢
  match l, hx, hp with
  | [], hx, _ => simp at hx
  | [a], hx, _ => simp at hx
  | a :: b :: l, hx, hp =>
    simp only [List.getD_cons_zero, List.getD_cons_succ, Multiset.coe_erase, List.erase_cons_head,
      Multiset.mem_coe, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact le_rfl
    · exact List.rel_of_pairwise_cons (List.Pairwise.of_cons hp) hx

end Polynomial

namespace TauCeti

open Polynomial

/-- A family of real polynomials is *commonly interlaced* when every member splits over `ℝ` and,
for all members `f i`, `f i'` and every `j` with `j + 1 < natDegree (f i)`, the `(j + 2)`-nd
largest root of `f i` is at most the `(j + 1)`-st largest root of `f i'`. For real-rooted
polynomials of one degree, this says that the `(j + 1)`-st largest roots of all members lie in
an interval that lies above the `(j + 2)`-nd largest roots of all members. -/
def CommonlyInterlaced {ι : Type*} (f : ι → ℝ[X]) : Prop :=
  (∀ i, (f i).Splits) ∧
    ∀ i i' (j : ℕ), j + 1 < (f i).natDegree →
      (f i).sortedRoots.getD (j + 1) 0 ≤ (f i').sortedRoots.getD j 0

variable {ι κ : Type*} {f : ι → ℝ[X]}

/-- The defining property of a commonly interlaced family. -/
theorem commonlyInterlaced_iff : CommonlyInterlaced f ↔ (∀ i, (f i).Splits) ∧
    ∀ i i' (j : ℕ), j + 1 < (f i).natDegree →
      (f i).sortedRoots.getD (j + 1) 0 ≤ (f i').sortedRoots.getD j 0 :=
  Iff.rfl

/-- Every member of a commonly interlaced family splits over `ℝ`. -/
theorem CommonlyInterlaced.splits (hf : CommonlyInterlaced f) (i : ι) : (f i).Splits :=
  hf.1 i

/-- In a commonly interlaced family, the `(j + 2)`-nd largest root of one member is at most the
`(j + 1)`-st largest root of every member. -/
theorem CommonlyInterlaced.sortedRoots_getD_succ_le (hf : CommonlyInterlaced f) {j : ℕ}
    (i i' : ι) (hj : j + 1 < (f i).natDegree) :
    (f i).sortedRoots.getD (j + 1) 0 ≤ (f i').sortedRoots.getD j 0 :=
  hf.2 i i' j hj

/-- Common interlacing is preserved by reindexing, in particular by passing to a subfamily. -/
theorem CommonlyInterlaced.comp (hf : CommonlyInterlaced f) (e : κ → ι) :
    CommonlyInterlaced (f ∘ e) :=
  ⟨fun i ↦ hf.splits (e i), fun i i' _ hj ↦ hf.sortedRoots_getD_succ_le (e i) (e i') hj⟩

/-- A family with at most one member is commonly interlaced as soon as its members split: the
roots of a single polynomial interlace themselves. -/
theorem commonlyInterlaced_of_subsingleton [Subsingleton ι] (hf : ∀ i, (f i).Splits) :
    CommonlyInterlaced f := by
  refine ⟨hf, fun i i' j hj ↦ ?_⟩
  obtain rfl := Subsingleton.elim i i'
  exact sortedRoots_getD_succ_le_getD <| by
    rwa [length_sortedRoots, splits_iff_card_roots.1 (hf i)]

/-- **One level of an interlacing family** (Marcus–Spielman–Srivastava, Lemma 4.2). If the
members of a nonempty finite commonly interlaced family of real polynomials have positive leading
coefficients, then some member has every root at most some root of the sum of the family. -/
theorem exists_isRoot_le_of_commonlyInterlaced [Fintype ι] [Nonempty ι]
    (hf : CommonlyInterlaced f) (hlc : ∀ i, 0 < (f i).leadingCoeff) :
    ∃ i, ∀ x, (f i).IsRoot x → ∃ y, (∑ i', f i').IsRoot y ∧ x ≤ y := by
  have hne (i : ι) : f i ≠ 0 := leadingCoeff_ne_zero.1 (hlc i).ne'
  -- A member without roots satisfies the conclusion vacuously.
  by_cases h0 : ∃ i, (f i).roots = 0
  · obtain ⟨i, hi⟩ := h0
    exact ⟨i, fun x hx ↦ by simpa [hi] using (mem_roots (hne i)).2 hx⟩
  push Not at h0
  -- Compare the largest roots `r i` of the members.
  let r (i : ι) : ℝ := (f i).sortedRoots.getD 0 0
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image univ r univ_nonempty
  obtain ⟨i₁, -, hi₁⟩ := exists_max_image univ r univ_nonempty
  -- At the smallest largest root every member is nonpositive.
  have hneg : (∑ i, f i).eval (r i₀) ≤ 0 := by
    rw [eval_finsetSum]
    refine sum_nonpos fun i _ ↦ (hf.splits i).eval_nonpos_of_forall_mem_erase_le (hlc i).le
      (sortedRoots_getD_zero_mem_roots (h0 i)) (hi₀ i (mem_univ _)) fun y hy ↦ ?_
    -- A root besides the largest one makes the degree at least two.
    have hcard : 0 + 1 < (f i).natDegree := by
      have := Multiset.card_pos_iff_exists_mem.2 ⟨y, hy⟩
      rw [Multiset.card_erase_of_mem (sortedRoots_getD_zero_mem_roots (h0 i)),
        splits_iff_card_roots.1 (hf.splits i), Nat.pred_eq_sub_one] at this
      omega
    exact (le_sortedRoots_getD_one_of_mem_erase hy).trans
      (hf.sortedRoots_getD_succ_le i i₀ hcard)
  -- At the largest largest root every member is nonnegative.
  have hpos : 0 ≤ (∑ i, f i).eval (r i₁) := by
    rw [eval_finsetSum]
    exact sum_nonneg fun i _ ↦ zero_le_eval_of_roots_le_of_leadingCoeff_nonneg
      (fun y hy ↦ (le_sortedRoots_getD_zero ((mem_roots (hne i)).2 hy)).trans (hi₁ i (mem_univ _)))
      (hlc i).le
  obtain ⟨y, ⟨hy₀, -⟩, hy⟩ := intermediate_value_Icc (hi₁ i₀ (mem_univ _))
    (∑ i, f i).continuous.continuousOn ⟨hneg, hpos⟩
  exact ⟨i₀, fun x hx ↦ ⟨y, hy, (le_sortedRoots_getD_zero ((mem_roots (hne i₀)).2 hx)).trans hy₀⟩⟩

end TauCeti
