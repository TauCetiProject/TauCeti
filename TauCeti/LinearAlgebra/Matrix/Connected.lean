/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Finset.Max
public import TauCeti.Logic.Relation
import Mathlib.Tactic.Ring

/-!
# Strong connectivity of the directed graph of a matrix

A square matrix `A` with entries in a partially ordered type determines a directed graph on its
index set, with an edge from `i` to a distinct `j` when `0 < A i j`. When the off-diagonal
entries are nonnegative, strong connectivity of this directed graph is the same as the absence of
a disconnecting cut: no nonempty proper set of indices has all of its outgoing entries zero.

For a symmetric `A` the directed graph is an ordinary graph and strong connectivity is ordinary
connectedness; the cut condition is then the form in which
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the connectedness condition
on the intersection matrix of a numerical type.

## Main results

* `Matrix.forall_reflTransGen_ne_and_pos_iff`: for a matrix with nonnegative off-diagonal
  entries, strong connectivity of its directed graph is the absence of a disconnecting cut.
* `Matrix.eq_smul_of_mulVec_eq_zero`: if a matrix over a linear ordered field has nonnegative
  off-diagonal entries and strongly connected positive-entry graph, then every vector in its
  kernel is proportional to any strictly positive vector in its kernel.
-/

public section

namespace Matrix

/-- For a matrix `A` whose off-diagonal entries are nonnegative, strong connectivity of the
directed graph with an edge from `i` to a distinct `j` when `0 < A i j` is equivalent to the
absence of a disconnecting cut: no nonempty proper set of indices `s` has all of its outgoing
entries `A i j`, for `i ∈ s` and `j ∉ s`, zero. No symmetry of `A` is assumed, so the left-hand
side is connectedness of an ordinary graph only when `A` is symmetric, as the intersection matrix
of a numerical type is. The right-hand side is then the form in which
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the connectedness condition
on a numerical type, so this is what supplies the `connected` field of `TauCeti.NumericalType`
when one is constructed.

The nonnegativity hypothesis is what turns a nonzero cross-entry into a positive one, and so
cannot be dropped. -/
lemma forall_reflTransGen_ne_and_pos_iff {C R : Type*} [PartialOrder R] [Zero R]
    (A : Matrix C C R) (hA : ∀ i j, i ≠ j → 0 ≤ A i j) :
    (∀ i j, Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < A i j) i j) ↔
      ∀ s : Set C, s.Nonempty → s ≠ Set.univ → ¬ ∀ i ∈ s, ∀ j ∉ s, A i j = 0 := by
  rw [Relation.forall_reflTransGen_iff]
  refine forall_congr' fun s ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨i, hi, j, hj, -, hpos⟩ hcut
    exact hpos.ne' (hcut i hi j hj)
  · intro hcut
    by_contra hcon
    refine hcut fun i hi j hj ↦ ?_
    have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
    by_contra hne
    exact hcon ⟨i, hi, j, hj, hij, lt_of_le_of_ne (hA i j hij) (Ne.symm hne)⟩

/-- Let `A` be a matrix over a linear ordered field, with nonnegative off-diagonal entries and
strongly connected positive-entry graph. If `m` is a strictly positive vector in the kernel of
`A`, then every vector in the kernel of `A` is a scalar multiple of `m`.

This is the weighted maximum principle. At an index where `x i / m i` is maximal, subtracting
that multiple of the equation `A *ᵥ m = 0` from `A *ᵥ x = 0` shows that the ratio is equal
at every adjacent index; connectedness propagates the equality to every index. -/
lemma eq_smul_of_mulVec_eq_zero {C K : Type*} [Fintype C] [Nonempty C]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix C C K)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < A i j) i j)
    (m x : C → K) (hm : ∀ i, 0 < m i) (hAm : A.mulVec m = 0) (hAx : A.mulVec x = 0) :
    ∃ c : K, x = c • m := by
  classical
  let r : C → K := fun i ↦ x i / m i
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hr_le (j : C) : r j ≤ r i := hi j (Finset.mem_univ j)
  have hx_eq (j : C) : r j * m j = x j := div_mul_cancel₀ _ (hm j).ne'
  have hadj {j k : C} (hj : r j = r i) (hjk : j ≠ k ∧ 0 < A j k) : r k = r i := by
    have hsum : ∑ l, A j l * m l * (r l - r j) = 0 := by
      calc
        ∑ l, A j l * m l * (r l - r j) =
            ∑ l, (A j l * x l - r j * (A j l * m l)) := by
              apply Finset.sum_congr rfl
              intro l _
              rw [← hx_eq l]
              ring
        _ = A.mulVec x j - r j * A.mulVec m j := by
              simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, Finset.mul_sum]
        _ = 0 := by rw [congrFun hAx j, congrFun hAm j, Pi.zero_apply]; simp
    have hterm_nonpos (l : C) : A j l * m l * (r l - r j) ≤ 0 := by
      by_cases hjl : j = l
      · subst l
        simp
      · exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (hnonneg j l hjl) (hm l).le)
          (sub_nonpos.mpr (hj ▸ hr_le l))
    have hterm : A j k * m k * (r k - r j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos fun l _ ↦ hterm_nonpos l).mp hsum k
        (Finset.mem_univ k)
    have hcoeff : A j k * m k ≠ 0 := mul_ne_zero hjk.2.ne' (hm k).ne'
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hcoeff)).trans hj
  have hr_eq (j : C) : r j = r i := by
    induction hconnected i j with
    | refl => rfl
    | tail hab hjk ih => exact hadj ih hjk
  refine ⟨r i, funext fun j ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, ← hr_eq j, hx_eq]

end Matrix
