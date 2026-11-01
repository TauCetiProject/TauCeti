/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Decreasing rearrangements of nonnegative null families

The decreasing rearrangement lists the values of a nonnegative null family in descending
order, with multiplicities. It is padded by zeros when only finitely many values are positive,
including for an empty index type. The characterization by finite superlevel sets avoids
choosing an enumeration of the original index type.

For a family tending to zero along the cofinite filter, its rearrangement tends to zero
and bounds every finite product by the product of the same number of initial terms.
This supplies ordered bounds for determinants with arbitrarily indexed rows.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {ι : Type*} {r : ι → ℝ}

private def rearrangementBounds (r : ι → ℝ) (n : ℕ) : Set ℝ :=
  insert 0 {a | ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a ≤ r i}

/-- The decreasing rearrangement of a bounded nonnegative family, padded by zeros.
The term at `n` is the supremum of the lower bounds on `n + 1` distinct entries, together
with zero. For a null family, a positive rearranged term is attained by an entry. -/
noncomputable def decreasingRearrangement (r : ι → ℝ) (n : ℕ) : ℝ :=
  sSup (rearrangementBounds r n)

theorem decreasingRearrangement_def (r : ι → ℝ) (n : ℕ) :
    decreasingRearrangement r n =
      sSup (insert 0 {a | ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a ≤ r i}) := (rfl)

private theorem nonempty_rearrangementBounds (r : ι → ℝ) (n : ℕ) :
    (rearrangementBounds r n).Nonempty :=
  ⟨0, Set.mem_insert _ _⟩

private theorem bddAbove_rearrangementBounds (hr : BddAbove (Set.range r)) (n : ℕ) :
    BddAbove (rearrangementBounds r n) := by
  obtain ⟨M, hM⟩ := hr
  refine ⟨max 0 M, ?_⟩
  rintro a (rfl | ⟨s, hs, ha⟩)
  · exact le_max_left _ _
  · obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < s.card)
    exact (ha i hi).trans ((hM (Set.mem_range_self i)).trans (le_max_right _ _))

/-- Rearranged bounds are nonnegative, even when there are no indices. -/
theorem decreasingRearrangement_nonneg (hr : BddAbove (Set.range r)) (n : ℕ) :
    0 ≤ decreasingRearrangement r n :=
  le_csSup (bddAbove_rearrangementBounds hr n) (Set.mem_insert _ _)

/-- A lower bound on `n + 1` distinct entries is bounded by the `n`-th rearranged entry. -/
theorem le_decreasingRearrangement (hr : BddAbove (Set.range r))
    {n : ℕ} {s : Finset ι} (hs : s.card = n + 1) {a : ℝ} (ha : ∀ i ∈ s, a ≤ r i) :
    a ≤ decreasingRearrangement r n :=
  le_csSup (bddAbove_rearrangementBounds hr n) (Set.mem_insert_of_mem _ ⟨s, hs, ha⟩)

/-- The rearrangement is antitone. -/
theorem antitone_decreasingRearrangement (hr : BddAbove (Set.range r)) :
    Antitone (decreasingRearrangement r) := by
  intro m n hmn
  apply csSup_le (nonempty_rearrangementBounds r n)
  rintro a (rfl | ⟨s, hs, ha⟩)
  · exact decreasingRearrangement_nonneg hr m
  · obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (by omega : m + 1 ≤ s.card)
    exact le_decreasingRearrangement hr ht (fun i hi ↦ ha i (hts hi))

/-- A finite set containing every entry larger than `a` bounds the rearrangement from its
cardinality onward. In particular finite support gives zero padding. -/
theorem decreasingRearrangement_le_of_card_le {a : ℝ} (ha : 0 ≤ a)
    {s : Finset ι} {n : ℕ} (hs : s.card ≤ n) (hr : ∀ i ∉ s, r i ≤ a) :
    decreasingRearrangement r n ≤ a := by
  apply csSup_le (nonempty_rearrangementBounds r n)
  rintro b (rfl | ⟨t, ht, hb⟩)
  · exact ha
  · obtain ⟨i, hit, his⟩ := exists_mem_notMem_of_card_lt_card (by omega : s.card < t.card)
    exact (hb i hit).trans (hr i his)

/-- The rearrangement of the zero family is zero. -/
@[simp]
theorem decreasingRearrangement_zero (n : ℕ) :
    decreasingRearrangement (0 : ι → ℝ) n = 0 := by
  apply le_antisymm
  · exact decreasingRearrangement_le_of_card_le le_rfl (s := ∅) (by simp) (by simp)
  · apply decreasingRearrangement_nonneg
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact le_rfl

/-- Strict superlevels characterize the rearrangement, retaining repeated values and their
multiplicities. The threshold may be zero. -/
theorem lt_decreasingRearrangement_iff (hr : BddAbove (Set.range r)) {a : ℝ}
    (ha : 0 ≤ a) (n : ℕ) :
    a < decreasingRearrangement r n ↔
      ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a < r i := by
  classical
  rw [decreasingRearrangement, lt_csSup_iff (bddAbove_rearrangementBounds hr n)
    (nonempty_rearrangementBounds r n)]
  constructor
  · rintro ⟨b, rfl | ⟨s, hs, hb⟩, hab⟩
    · exact (ha.not_gt hab).elim
    · exact ⟨s, hs, fun i hi ↦ hab.trans_le (hb i hi)⟩
  · rintro ⟨s, hs, hsa⟩
    have hne : s.Nonempty := card_pos.mp (by omega : 0 < s.card)
    refine ⟨s.inf' hne r, Set.mem_insert_of_mem _ ⟨s, hs, fun i hi ↦ inf'_le _ hi⟩, ?_⟩
    exact (lt_inf'_iff hne).mpr hsa

/-- A finite strict superlevel set becomes an initial segment of the same cardinality.
Thus the rearrangement preserves multiplicities, including ties. -/
theorem setOf_lt_decreasingRearrangement {a : ℝ}
    (ha : 0 ≤ a) (hfin : {i | a < r i}.Finite) :
    {n | a < decreasingRearrangement r n} = Set.Iio hfin.toFinset.card := by
  classical
  have hr : BddAbove (Set.range r) := by
    refine ((hfin.image r).bddAbove.union (bddAbove_Iic (a := a))).mono ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : a < r i
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (le_of_not_gt hi)
  ext n
  rw [Set.mem_ofPred_eq, Set.mem_Iio, lt_decreasingRearrangement_iff hr ha]
  constructor
  · rintro ⟨s, hs, hsa⟩
    have hsub : s ⊆ hfin.toFinset := fun i hi ↦ hfin.mem_toFinset.mpr (hsa i hi)
    have := card_le_card hsub
    omega
  · intro hn
    obtain ⟨s, hsub, hs⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hn)
    exact ⟨s, hs, fun i hi ↦ hfin.mem_toFinset.mp (hsub hi)⟩

/-- Every positive term of the rearrangement of a null family is an original entry. -/
theorem exists_eq_decreasingRearrangement (hr : Tendsto r cofinite (𝓝 0)) {n : ℕ}
    (hn : 0 < decreasingRearrangement r n) : ∃ i, r i = decreasingRearrangement r n := by
  classical
  set x := decreasingRearrangement r n
  have hfin : {i | x / 2 < r i}.Finite := by
    simpa only [Filter.eventually_cofinite, not_le] using
      hr.eventually_le_const (half_pos hn)
  let t := (hfin.toFinset.filter (fun i ↦ r i < x)).image r
  let s := insert (x / 2) t
  have hs : s.Nonempty := ⟨_, mem_insert_self _ _⟩
  let b := s.max' hs
  have hhalf : x / 2 ≤ b := le_max' s _ (mem_insert_self _ _)
  have hbx : b < x := by
    apply (max'_lt_iff s hs).mpr
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact half_lt_self hn
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
      exact (mem_filter.mp hi).2
  -- Only finitely many entries exceed x / 2. If x is not attained, the maximum b
  -- leaves a gap (b, x) with no entries. The superlevels at b and x then force x < x.
  by_contra! hne
  have hstep (i : ι) (hi : b < r i) : x < r i := by
    by_contra! hix
    have hlt : r i < x := hix.lt_of_ne (hne i)
    have hit : i ∈ hfin.toFinset := hfin.mem_toFinset.mpr (hhalf.trans_lt hi)
    have him : r i ∈ s := mem_insert_of_mem (mem_image.mpr ⟨i, mem_filter.mpr ⟨hit, hlt⟩, rfl⟩)
    exact hi.not_ge (le_max' s _ him)
  obtain ⟨u, hu, hur⟩ := (lt_decreasingRearrangement_iff hr.bddAbove_range_of_cofinite
    ((half_pos hn).le.trans hhalf) n).mp hbx
  exact (lt_irrefl x) ((lt_decreasingRearrangement_iff hr.bddAbove_range_of_cofinite hn.le n).mpr
    ⟨u, hu, fun i hi ↦ hstep i (hur i hi)⟩)

/-- A family tending to zero cofinitely has a null decreasing rearrangement. -/
theorem tendsto_decreasingRearrangement (hr : Tendsto r cofinite (𝓝 0)) :
    Tendsto (decreasingRearrangement r) atTop (𝓝 0) := by
  classical
  refine tendsto_order.mpr ⟨fun a ha ↦ Eventually.of_forall fun n ↦
    ha.trans_le (decreasingRearrangement_nonneg hr.bddAbove_range_of_cofinite n), fun ε hε ↦ ?_⟩
  have hfin : {i | ε / 2 ≤ r i}.Finite := by
    simpa only [Filter.eventually_cofinite, not_lt] using
      hr.eventually_lt_const (half_pos hε)
  filter_upwards [eventually_ge_atTop hfin.toFinset.card] with n hn
  exact (decreasingRearrangement_le_of_card_le (half_pos hε).le hn
    (fun i hi ↦ le_of_lt (lt_of_not_ge (by simpa using hi)))).trans_lt (half_lt_self hε)

/-- Every finite product of entries is bounded by the initial product of the rearrangement. -/
theorem prod_le_prod_decreasingRearrangement (hr₀ : ∀ i, 0 ≤ r i)
    (hr : BddAbove (Set.range r)) (s : Finset ι) :
    ∏ i ∈ s, r i ≤ ∏ k ∈ range s.card, decreasingRearrangement r k := by
  classical
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
  let f : Fin s.card → ℝ := fun k ↦ r (e k)
  let σ := Tuple.sortDesc f
  let g : Fin s.card ↪ ι := σ.toEmbedding.trans (e.toEmbedding.trans (Function.Embedding.subtype _))
  have hgk (k : Fin s.card) : g k = (e (σ k) : ι) := by simp [g]
  have hg : Antitone (r ∘ g) := Tuple.antitone_sortDesc f
  have hle (k : Fin s.card) : r (g k) ≤ decreasingRearrangement r k := by
    apply le_decreasingRearrangement hr (s := (Iic k).map g)
    · simp
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
      exact hg (mem_Iic.mp hj)
  calc
    ∏ i ∈ s, r i = ∏ k : Fin s.card, r (g k) := by
      rw [← prod_coe_sort s, ← e.prod_comp, ← Equiv.prod_comp σ]
      simp only [hgk]
    _ ≤ ∏ k : Fin s.card, decreasingRearrangement r k :=
      prod_le_prod₀ (fun k _ ↦ hr₀ _) (fun k _ ↦ hle k)
    _ = _ := Fin.prod_univ_eq_prod_range _ _

end TauCeti
