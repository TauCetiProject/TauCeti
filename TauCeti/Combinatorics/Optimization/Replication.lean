/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.ProdLex
public import TauCeti.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Filter

/-!
# Replication of pairwise optimization problems

Replace each vertex of a loopless directed graph with a finite edge set by `q` copies and
each edge by the complete bipartite graph between its endpoint clusters. A pair cost,
depending on the labels at its endpoints, has infimum multiplied by `q²`. Labels may vary
arbitrarily within each cluster, and the label type need not be finite.

The lower bound averages over sections choosing one copy of every vertex: any nonnegative
within-cluster penalty preserves the lower bound `q² · d`, even when the penalty is positive on
cluster-constant assignments. When the penalty vanishes on cluster-constant assignments, copying a
base assignment constantly across each cluster gives the matching upper bound, so the replicated
infimum equals `q²` times the base infimum without assuming that an optimal assignment exists.

Combining these bounds with the cluster decomposition of strictly increasing pairs in a
lexicographic product `V ×ₗ ι` transfers both the lower bound and the exact quadratic scaling law to
assignments `(V ×ₗ ι) → A` summed over strictly increasing pairs. In particular, the exact scaling
applies to replicated gauge distances of group-valued cochains, while the lower bound without
diagonal vanishing applies to cross-degree gauge costs whose within-cluster error is positive.

## References

* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, doi:10.5281/zenodo.23245792, Lemma 6 (the section argument for replicated
  gauge costs) and Proposition 10 (cross-degree gauge lower bound under replication).
-/

public section

open Finset Prod.Lex

namespace Finset

variable {V A ι M : Type*}

/-- If every section has pair cost at least `d`, the total inter-cluster pair cost is at least
`Fintype.card ι ^ 2` copies of `d`. Only the edge set is required to be finite, and no sign
assumption on the pair costs is needed. -/
theorem card_sq_nsmul_le_sum_of_forall_le_sum [Fintype ι] [AddCommMonoid M]
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

/-- If every assignment `V → A` has pair cost at least `d` and the penalty `c` is nonnegative, any
replicated assignment `β : V → ι → A` has total cost at least `(Fintype.card ι : R) ^ 2 * d`. No
cluster-constancy condition on `c` and no nonemptiness assumption on `A` are required. -/
theorem card_sq_mul_le_add_sum_of_forall_le_sum {R : Type*} [Fintype ι] [Semiring R]
    [LinearOrder R] [IsOrderedCancelAddMonoid R] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → R) {c d : R} (hc : 0 ≤ c)
    (hd : ∀ β : V → A, d ≤ ∑ e ∈ E, w e (β e.1) (β e.2)) (β : V → ι → A) :
    (Fintype.card ι : R) ^ 2 * d ≤ c + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b) := by
  have hsections := E.card_sq_nsmul_le_sum_of_forall_le_sum hE
    (fun e a b ↦ w e (β e.1 a) (β e.2 b)) (fun s ↦ hd (fun v ↦ β v (s v)))
  have hbound : (Fintype.card ι : R) ^ 2 * d ≤ ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b) := by
    simpa [nsmul_eq_mul, Nat.cast_pow] using hsections
  exact hbound.trans (le_add_of_nonneg_left hc)

/-- If every assignment `V → A` has pair cost at least `d` and `c` is a nonnegative penalty, the
infimum of the replicated cost over `V → ι → A` is at least `(Fintype.card ι : ℝ) ^ 2 * d`, even
when `c` is positive on cluster-constant assignments. -/
theorem card_sq_mul_le_ciInf_add_sum [Fintype ι] [Nonempty A] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → ℝ)
    (c : (V → ι → A) → ℝ) (hc : ∀ β, 0 ≤ c β) {d : ℝ}
    (hd : ∀ β : V → A, d ≤ ∑ e ∈ E, w e (β e.1) (β e.2)) :
    (Fintype.card ι : ℝ) ^ 2 * d ≤
      ⨅ β : V → ι → A, (c β + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) :=
  le_ciInf fun β ↦ E.card_sq_mul_le_add_sum_of_forall_le_sum hE w (hc β) hd β

/-- Section-averaging lower bound for replicated pair costs with a nonnegative penalty `c`, without
assuming `c` vanishes on cluster-constant assignments or that `A` is nonempty. -/
theorem card_sq_mul_ciInf_sum_le_ciInf_add_sum [Fintype ι] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → ℝ)
    (c : (V → ι → A) → ℝ) (hc : ∀ β, 0 ≤ c β)
    (hf : BddBelow (Set.range fun β : V → A ↦ ∑ e ∈ E, w e (β e.1) (β e.2))) :
    (Fintype.card ι : ℝ) ^ 2 * (⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2)) ≤
      ⨅ β : V → ι → A, (c β + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) := by
  obtain hA | hA := isEmpty_or_nonempty A
  · have h0 : (⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2)) = 0 := by
      obtain hV | hV := isEmpty_or_nonempty V
      · simp [E.eq_empty_of_isEmpty]
      · simp
    rw [h0, mul_zero]
    refine Real.iInf_nonneg fun β ↦ add_nonneg (hc β) ?_
    obtain hV | hV := isEmpty_or_nonempty V
    · simp [E.eq_empty_of_isEmpty]
    · obtain hι | hι := isEmpty_or_nonempty ι
      · simp
      · exact (IsEmpty.false (β (Classical.arbitrary V) (Classical.arbitrary ι))).elim
  · exact E.card_sq_mul_le_ciInf_add_sum hE w c hc fun β ↦ ciInf_le hf β

/-- Replication multiplies the infimum of pair costs by the square of the number of copies,
even with a nonnegative penalty vanishing on cluster-constant assignments. The pair costs may
take either sign, neither the vertex type nor the label type must be finite, and no infimum need
be attained. The statement includes empty copy types, empty graphs and empty vertex types. -/
theorem ciInf_add_sum_eq_card_sq_mul_ciInf_sum [Fintype ι] [Nonempty A] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → ℝ)
    (c : (V → ι → A) → ℝ) (hc : ∀ β, 0 ≤ c β)
    (hc_const : ∀ β : V → A, c (fun v _ ↦ β v) = 0) :
    (⨅ β : V → ι → A, c β + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) =
      (Fintype.card ι : ℝ) ^ 2 * ⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2) := by
  classical
  let f (β : V → A) := ∑ e ∈ E, w e (β e.1) (β e.2)
  let F (β : V → ι → A) := c β + ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)
  have hcopy (β : V → A) : F (fun v _ ↦ β v) = (Fintype.card ι : ℝ) ^ 2 * f β := by
    simp [F, f, hc_const, ← mul_sum]
    ring
  obtain hι | hι := isEmpty_or_nonempty ι
  · have hF (β : V → ι → A) : F β = 0 := by
      rw [Subsingleton.elim β fun _ _ ↦ Classical.arbitrary A, hcopy]
      simp
    rw [Fintype.card_eq_zero, Nat.cast_zero, zero_pow two_ne_zero, zero_mul]
    exact (iInf_congr hF).trans ciInf_const
  by_cases hf : BddBelow (Set.range f)
  · have hF : BddBelow (Set.range F) := ⟨_, by
      rintro _ ⟨β, rfl⟩
      exact E.card_sq_mul_le_add_sum_of_forall_le_sum hE w (hc β) (fun β ↦ ciInf_le hf β) β⟩
    refine le_antisymm ?_ (E.card_sq_mul_ciInf_sum_le_ciInf_add_sum hE w c hc hf)
    rw [Real.mul_iInf_of_nonneg (sq_nonneg (Fintype.card ι : ℝ))]
    exact le_ciInf fun β ↦ (ciInf_le hF (fun v _ ↦ β v)).trans_eq (hcopy β)
  · have hpos : 0 < (Fintype.card ι : ℝ) ^ 2 :=
      pow_pos (Nat.cast_pos.mpr Fintype.card_pos) 2
    have hF : ¬BddBelow (Set.range F) := by
      rintro ⟨m, hm⟩
      refine hf ⟨m / (Fintype.card ι : ℝ) ^ 2, ?_⟩
      rintro _ ⟨β, rfl⟩
      rw [div_le_iff₀' hpos, ← hcopy]
      exact hm ⟨_, rfl⟩
    exact (Real.iInf_of_not_bddBelow hF).trans
      (by rw [Real.iInf_of_not_bddBelow hf, mul_zero])

/-- The infimum of pair costs is multiplied by the square of the number of copies when every
edge is replaced by all pairs of copies of its endpoints. -/
theorem ciInf_sum_eq_card_sq_mul_ciInf_sum [Fintype ι] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (w : V × V → A → A → ℝ) :
    (⨅ β : V → ι → A, ∑ e ∈ E, ∑ a, ∑ b, w e (β e.1 a) (β e.2 b)) =
      (Fintype.card ι : ℝ) ^ 2 * ⨅ β : V → A, ∑ e ∈ E, w e (β e.1) (β e.2) := by
  obtain hA | hA := isEmpty_or_nonempty A
  · obtain hV | hV := isEmpty_or_nonempty V
    · simp [E.eq_empty_of_isEmpty]
    rcases isEmpty_or_nonempty ι with hι | hι <;> simp
  simpa using E.ciInf_add_sum_eq_card_sq_mul_ciInf_sum hE w
    (fun _ : V → ι → A ↦ 0) (fun _ ↦ le_rfl) (fun _ ↦ rfl)

section ProdLex

private theorem withinCluster_sum_nonneg [LT ι] [DecidableLT ι] (s : Finset V) (t : Finset ι)
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ)
    (hz_nonneg : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ a b,
      0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (β : V → ↥t → A) :
    0 ≤ ∑ v ∈ s, ∑ i : ↥t, ∑ j : ↥t with i.val < j.val,
      W (toLex (v, i)) (toLex (v, j)) (β v i) (β v j) :=
  sum_nonneg fun v hv ↦ sum_nonneg fun i _ ↦ sum_nonneg fun j hj ↦
    hz_nonneg v hv i.val i.property j.val j.property (mem_filter.mp hj).2 _ _

variable [Preorder V] [Preorder ι] [DecidableLT V] [DecidableLT (V ×ₗ ι)]

private theorem sum_product_filter_lt_map_toLex_eq_add [AddCommMonoid M] [DecidableLT ι]
    (s : Finset V) (t : Finset ι)
    (f : (V ×ₗ ι) → (V ×ₗ ι) → M) (w : V → V → A → A → M) (φ : (V ×ₗ ι) → A)
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t,
      f (toLex (u, i)) (toLex (v, j)) = w u v (φ (toLex (u, i))) (φ (toLex (v, j)))) :
    (∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2, f p.1 p.2) =
      (∑ v ∈ s, ∑ i : ↥t, ∑ j : ↥t with i.val < j.val, f (toLex (v, i)) (toLex (v, j))) +
        ∑ e ∈ {e ∈ s ×ˢ s | e.1 < e.2}, ∑ i : ↥t, ∑ j : ↥t,
          w e.1 e.2 (φ (toLex (e.1, i))) (φ (toLex (e.2, j))) := by
  rw [sum_product_filter_lt_map_toLex s t f]
  congr 1
  · refine sum_congr rfl fun v _ ↦ ?_
    rw [sum_filter_product t t (· < ·) fun i j ↦ f (toLex (v, i)) (toLex (v, j)), ← sum_coe_sort t]
    refine sum_congr rfl fun i _ ↦ ?_
    simp_rw [sum_filter]
    exact (sum_coe_sort t _).symm
  · refine sum_congr rfl fun e he ↦ ?_
    simp only [mem_filter, mem_product] at he
    calc
      (∑ i ∈ t, ∑ j ∈ t, f (toLex (e.1, i)) (toLex (e.2, j))) =
          ∑ i ∈ t, ∑ j ∈ t, w e.1 e.2 (φ (toLex (e.1, i))) (φ (toLex (e.2, j))) :=
        sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦
          hw e.1 he.1.1 e.2 he.1.2 he.2 i hi j hj
      _ = ∑ i : ↥t, ∑ j : ↥t, w e.1 e.2 (φ (toLex (e.1, i))) (φ (toLex (e.2, j))) := by
        rw [← sum_coe_sort t]
        exact sum_congr rfl fun i _ ↦ (sum_coe_sort t _).symm

private theorem ciInf_sum_product_filter_lt_map_toLex_eq [DecidableLT ι]
    (s : Finset V) (t : Finset ι)
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t, ∀ a b,
      W (toLex (u, i)) (toLex (v, j)) a b = w u v a b) :
    (⨅ φ : (V ×ₗ ι) → A,
        ∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
          with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2)) =
      ⨅ β : V → ↥t → A,
        ((∑ v ∈ s, ∑ i : ↥t, ∑ j : ↥t with i.val < j.val,
            W (toLex (v, i)) (toLex (v, j)) (β v i) (β v j)) +
          ∑ e ∈ {e ∈ s ×ˢ s | e.1 < e.2}, ∑ i : ↥t, ∑ j : ↥t,
            w e.1 e.2 (β e.1 i) (β e.2 j)) := by
  obtain hA | hA := isEmpty_or_nonempty A
  · obtain hV | hV := isEmpty_or_nonempty V
    · rcases isEmpty_or_nonempty ((V ×ₗ ι) → A) with _ | _ <;>
        simp [s.eq_empty_of_isEmpty]
    · rcases t.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · rcases isEmpty_or_nonempty ((V ×ₗ ι) → A) with _ | _ <;> simp
      · have : Nonempty (V ×ₗ ι) := ⟨toLex (Classical.arbitrary V, i)⟩
        have : Nonempty ↥t := ⟨⟨i, hi⟩⟩
        simp
  · have hsurj :
        Function.Surjective (fun φ : (V ×ₗ ι) → A ↦ fun v (i : ↥t) ↦ φ (toLex (v, i))) :=
      (Function.RightInverse.surjective Function.curry_uncurry).comp
        (toLex.injective.comp
          (Function.injective_id.prodMap Subtype.val_injective)).surjective_comp_right
    exact hsurj.iInf_congr _ fun φ ↦
      (sum_product_filter_lt_map_toLex_eq_add s t (fun x y ↦ W x y (φ x) (φ y)) w φ
        fun u hu v hv huv i hi j hj ↦ hw u hu v hv huv i hi j hj _ _).symm

/-- If within-cluster increasing pairs in `(s ×ˢ t).map toLex.toEmbedding` have nonnegative value
under `f`, inter-cluster pairs agree with `w` evaluated on `φ`, and every assignment `V → A` has
increasing-pair cost at least `d` on `s`, then the increasing-pair sum of `f` is at least
`(#t : R) ^ 2 * d`. -/
theorem card_sq_mul_le_sum_product_filter_lt_map_toLex_of_forall_le_sum
    {R : Type*} [Semiring R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (s : Finset V) (t : Finset ι)
    (f : (V ×ₗ ι) → (V ×ₗ ι) → R) (w : V → V → A → A → R) (φ : (V ×ₗ ι) → A)
    (hz_nonneg : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → 0 ≤ f (toLex (v, i)) (toLex (v, j)))
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t,
      f (toLex (u, i)) (toLex (v, j)) = w u v (φ (toLex (u, i))) (φ (toLex (v, j))))
    {d : R} (hd : ∀ β : V → A, d ≤ ∑ e ∈ s ×ˢ s with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) :
    (#t : R) ^ 2 * d ≤
      ∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
        with p.1 < p.2, f p.1 p.2 := by
  have : DecidableLT ι := Classical.decRel _
  rw [sum_product_filter_lt_map_toLex_eq_add s t f w φ hw, ← Fintype.card_coe t]
  refine card_sq_mul_le_add_sum_of_forall_le_sum {e ∈ s ×ˢ s | e.1 < e.2}
    (fun _ he ↦ (mem_filter.mp he).2.ne) (fun e ↦ w e.1 e.2) ?_ hd
    (fun v (i : ↥t) ↦ φ (toLex (v, i)))
  exact sum_nonneg fun v hv ↦ sum_nonneg fun i _ ↦ sum_nonneg fun j hj ↦
    hz_nonneg v hv i.val i.property j.val j.property (mem_filter.mp hj).2

/-- Infimum form of `Finset.card_sq_mul_le_sum_product_filter_lt_map_toLex_of_forall_le_sum`:
nonnegative within-cluster costs preserve a uniform lower bound multiplied by `(#t : ℝ) ^ 2`, even
when within-cluster costs are positive on constant assignments. -/
theorem card_sq_mul_le_ciInf_sum_product_filter_lt_map_toLex [Nonempty A]
    (s : Finset V) (t : Finset ι)
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ a b,
      0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t, ∀ a b,
      W (toLex (u, i)) (toLex (v, j)) a b = w u v a b)
    {d : ℝ} (hd : ∀ β : V → A, d ≤ ∑ e ∈ s ×ˢ s with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) :
    (#t : ℝ) ^ 2 * d ≤
      ⨅ φ : (V ×ₗ ι) → A,
        ∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
          with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2) :=
  le_ciInf fun φ ↦
    card_sq_mul_le_sum_product_filter_lt_map_toLex_of_forall_le_sum s t
      (fun x y ↦ W x y (φ x) (φ y)) w φ
      (fun v hv i hi j hj hij ↦ hz_nonneg v hv i hi j hj hij _ _)
      (fun u hu v hv huv i hi j hj ↦ hw u hu v hv huv i hi j hj _ _) hd

/-- Section-averaging lower bound for the infimum of increasing-pair costs on
`(s ×ˢ t).map toLex.toEmbedding`, without assuming within-cluster costs vanish on constant
assignments or that `A` is nonempty. -/
theorem card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_map_toLex
    (s : Finset V) (t : Finset ι)
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ a b,
      0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t, ∀ a b,
      W (toLex (u, i)) (toLex (v, j)) a b = w u v a b)
    (hf : BddBelow (Set.range fun β : V → A ↦
      ∑ e ∈ s ×ˢ s with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2))) :
    (#t : ℝ) ^ 2 * (⨅ β : V → A, ∑ e ∈ s ×ˢ s with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) ≤
      ⨅ φ : (V ×ₗ ι) → A,
        ∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
          with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2) := by
  have : DecidableLT ι := Classical.decRel _
  rw [ciInf_sum_product_filter_lt_map_toLex_eq s t W w hw, ← Fintype.card_coe t]
  exact card_sq_mul_ciInf_sum_le_ciInf_add_sum {e ∈ s ×ˢ s | e.1 < e.2}
    (fun _ he ↦ (mem_filter.mp he).2.ne) (fun e ↦ w e.1 e.2) _
    (withinCluster_sum_nonneg s t W hz_nonneg) hf

/-- Nonnegative-weight specialization of
`Finset.card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_map_toLex`, discharging `BddBelow`
automatically by `0`. -/
theorem card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_map_toLex_of_nonneg
    (s : Finset V) (t : Finset ι)
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ a b,
      0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hw_nonneg : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ a b, 0 ≤ w u v a b)
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t, ∀ a b,
      W (toLex (u, i)) (toLex (v, j)) a b = w u v a b) :
    (#t : ℝ) ^ 2 * (⨅ β : V → A, ∑ e ∈ s ×ˢ s with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) ≤
      ⨅ φ : (V ×ₗ ι) → A,
        ∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
          with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2) := by
  refine card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_map_toLex s t W w hz_nonneg hw
    ⟨0, ?_⟩
  rintro _ ⟨β, rfl⟩
  refine sum_nonneg fun (e : V × V) he ↦ ?_
  simp only [mem_filter, mem_product] at he
  exact hw_nonneg e.1 he.1.1 e.2 he.1.2 he.2 _ _

/-- When within-cluster increasing pairs in `(s ×ˢ t).map toLex.toEmbedding` have nonnegative cost
that vanishes on equal labels and inter-cluster pairs depend only on their `V` coordinates, the
infimum of the increasing-pair cost over `(V ×ₗ ι) → A` equals `(#t : ℝ) ^ 2` times the base infimum
over `V → A`. Neither `V`, `ι`, nor `A` need be finite or nonempty, and no infimum need be
attained. -/
theorem ciInf_sum_product_filter_lt_map_toLex_eq_card_sq_mul_ciInf_sum (s : Finset V) (t : Finset ι)
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ a b,
      0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hz_diag : ∀ v ∈ s, ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ a,
      W (toLex (v, i)) (toLex (v, j)) a a = 0)
    (hw : ∀ u ∈ s, ∀ v ∈ s, u < v → ∀ i ∈ t, ∀ j ∈ t, ∀ a b,
      W (toLex (u, i)) (toLex (v, j)) a b = w u v a b) :
    (⨅ φ : (V ×ₗ ι) → A,
        ∑ p ∈ ((s ×ˢ t).map toLex.toEmbedding) ×ˢ ((s ×ˢ t).map toLex.toEmbedding)
          with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2)) =
      (#t : ℝ) ^ 2 * ⨅ β : V → A, ∑ e ∈ s ×ˢ s with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2) := by
  have : DecidableLT ι := Classical.decRel _
  rw [ciInf_sum_product_filter_lt_map_toLex_eq s t W w hw, ← Fintype.card_coe t]
  obtain hA | hA := isEmpty_or_nonempty A
  · obtain hV | hV := isEmpty_or_nonempty V
    · simp [s.eq_empty_of_isEmpty]
    · rcases t.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · simp
      · have : Nonempty ↥t := ⟨⟨i, hi⟩⟩
        simp
  · refine ciInf_add_sum_eq_card_sq_mul_ciInf_sum {e ∈ s ×ˢ s | e.1 < e.2}
      (fun _ he ↦ (mem_filter.mp he).2.ne) (fun e ↦ w e.1 e.2) _
      (withinCluster_sum_nonneg s t W hz_nonneg) fun β ↦ ?_
    exact sum_eq_zero fun v hv ↦ sum_eq_zero fun i _ ↦ sum_eq_zero fun j hj ↦
      hz_diag v hv i.val i.property j.val j.property (mem_filter.mp hj).2 (β v)

end ProdLex

end Finset

namespace Fintype

open Finset

variable {V A ι : Type*} [Fintype V] [Fintype ι] [Preorder V] [Preorder ι]
  [DecidableLT V] [DecidableLT (V ×ₗ ι)]

/-- If within-cluster increasing pairs of `V ×ₗ ι` have nonnegative value under `f`, inter-cluster
pairs agree with `w` evaluated on `φ`, and every assignment `V → A` has increasing-pair cost at
least `d`, then the increasing-pair sum of `f` is at least `(Fintype.card ι : R) ^ 2 * d`. -/
theorem card_sq_mul_le_sum_product_filter_lt_prodLex_of_forall_le_sum
    {R : Type*} [Semiring R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (f : (V ×ₗ ι) → (V ×ₗ ι) → R) (w : V → V → A → A → R) (φ : (V ×ₗ ι) → A)
    (hz_nonneg : ∀ v i j, i < j → 0 ≤ f (toLex (v, i)) (toLex (v, j)))
    (hw : ∀ u v, u < v → ∀ i j,
      f (toLex (u, i)) (toLex (v, j)) = w u v (φ (toLex (u, i))) (φ (toLex (v, j))))
    {d : R} (hd : ∀ β : V → A, d ≤ ∑ e : V × V with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) :
    (Fintype.card ι : R) ^ 2 * d ≤
      ∑ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2, f p.1 p.2 := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.card_sq_mul_le_sum_product_filter_lt_map_toLex_of_forall_le_sum (univ : Finset V)
      (univ : Finset ι) f w φ (fun v _ i _ j _ ↦ hz_nonneg v i j)
      (fun u _ v _ huv i _ j _ ↦ hw u v huv i j) (by simpa [univ_product_univ] using hd)

/-- Infimum form of `Fintype.card_sq_mul_le_sum_product_filter_lt_prodLex_of_forall_le_sum`:
nonnegative within-cluster costs preserve a uniform lower bound multiplied by
`(Fintype.card ι : ℝ) ^ 2`, even when within-cluster costs are positive on constant assignments. -/
theorem card_sq_mul_le_ciInf_sum_product_filter_lt_prodLex [Nonempty A]
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v i j, i < j → ∀ a b, 0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hw : ∀ u v, u < v → ∀ i j a b, W (toLex (u, i)) (toLex (v, j)) a b = w u v a b)
    {d : ℝ} (hd : ∀ β : V → A, d ≤ ∑ e : V × V with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) :
    (Fintype.card ι : ℝ) ^ 2 * d ≤
      ⨅ φ : (V ×ₗ ι) → A,
        ∑ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2) :=
  le_ciInf fun φ ↦
    card_sq_mul_le_sum_product_filter_lt_prodLex_of_forall_le_sum
      (fun x y ↦ W x y (φ x) (φ y)) w φ
      (fun v i j hij ↦ hz_nonneg v i j hij _ _)
      (fun u v huv i j ↦ hw u v huv i j _ _) hd

/-- Section-averaging lower bound for the infimum of increasing-pair costs on `V ×ₗ ι`, without
assuming within-cluster costs vanish on constant assignments or that `A` is nonempty. -/
theorem card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_prodLex
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v i j, i < j → ∀ a b, 0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hw : ∀ u v, u < v → ∀ i j a b, W (toLex (u, i)) (toLex (v, j)) a b = w u v a b)
    (hf : BddBelow (Set.range fun β : V → A ↦
      ∑ e : V × V with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2))) :
    (Fintype.card ι : ℝ) ^ 2 *
        (⨅ β : V → A, ∑ e : V × V with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) ≤
      ⨅ φ : (V ×ₗ ι) → A,
        ∑ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_map_toLex (univ : Finset V)
      (univ : Finset ι) W w (fun v _ i _ j _ ↦ hz_nonneg v i j)
      (fun u _ v _ huv i _ j _ ↦ hw u v huv i j) (by simpa [univ_product_univ] using hf)

/-- Nonnegative-weight specialization of
`Fintype.card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_prodLex`, discharging `BddBelow`
automatically by `0`. -/
theorem card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_prodLex_of_nonneg
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v i j, i < j → ∀ a b, 0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hw_nonneg : ∀ u v, u < v → ∀ a b, 0 ≤ w u v a b)
    (hw : ∀ u v, u < v → ∀ i j a b, W (toLex (u, i)) (toLex (v, j)) a b = w u v a b) :
    (Fintype.card ι : ℝ) ^ 2 *
        (⨅ β : V → A, ∑ e : V × V with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2)) ≤
      ⨅ φ : (V ×ₗ ι) → A,
        ∑ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.card_sq_mul_ciInf_sum_le_ciInf_sum_product_filter_lt_map_toLex_of_nonneg
      (univ : Finset V) (univ : Finset ι) W w (fun v _ i _ j _ ↦ hz_nonneg v i j)
      (fun u _ v _ huv ↦ hw_nonneg u v huv) (fun u _ v _ huv i _ j _ ↦ hw u v huv i j)

/-- When within-cluster increasing pairs of `V ×ₗ ι` have nonnegative cost vanishing on equal labels
and inter-cluster pairs depend only on their `V` coordinates, the infimum of the increasing-pair
cost over `(V ×ₗ ι) → A` equals `(Fintype.card ι : ℝ) ^ 2` times the base infimum over `V → A`.
`V`, `ι`, and `A` need not be nonempty, `A` need not be finite, and no infimum need be attained. -/
theorem ciInf_sum_product_filter_lt_prodLex_eq_card_sq_mul_ciInf_sum
    (W : (V ×ₗ ι) → (V ×ₗ ι) → A → A → ℝ) (w : V → V → A → A → ℝ)
    (hz_nonneg : ∀ v i j, i < j → ∀ a b, 0 ≤ W (toLex (v, i)) (toLex (v, j)) a b)
    (hz_diag : ∀ v i j, i < j → ∀ a, W (toLex (v, i)) (toLex (v, j)) a a = 0)
    (hw : ∀ u v, u < v → ∀ i j a b, W (toLex (u, i)) (toLex (v, j)) a b = w u v a b) :
    (⨅ φ : (V ×ₗ ι) → A,
        ∑ p : (V ×ₗ ι) × (V ×ₗ ι) with p.1 < p.2, W p.1 p.2 (φ p.1) (φ p.2)) =
      (Fintype.card ι : ℝ) ^ 2 *
        ⨅ β : V → A, ∑ e : V × V with e.1 < e.2, w e.1 e.2 (β e.1) (β e.2) := by
  simpa [univ_product_univ, map_univ_equiv] using
    Finset.ciInf_sum_product_filter_lt_map_toLex_eq_card_sq_mul_ciInf_sum (univ : Finset V)
      (univ : Finset ι) W w (fun v _ i _ j _ ↦ hz_nonneg v i j)
      (fun v _ i _ j _ ↦ hz_diag v i j) (fun u _ v _ huv i _ j _ ↦ hw u v huv i j)

end Fintype
