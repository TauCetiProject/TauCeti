/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Topology
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.IntersectionForm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

/-!
# Minimal numerical types of genus one

This file describes the minimal numerical types of genus one, the numerical shadows of the
special fibres of minimal regular models of genus-one curves.

A numerical type with a single component `i` has genus `1 + mᵢwᵢ(gᵢ - 1)`, so it has genus one
exactly when `gᵢ = 1`. With more than one component, the signed genus is `1 + ∑ᵢ Φᵢ` with every
contribution `Φᵢ` of a minimal type nonnegative and zero exactly at the `(-2)`-indices; hence a
numerical type with more than one component is minimal of genus one exactly when every component
is a `(-2)`-index.

For such a type the intersection graph is either a tree or a single cycle. More generally, suppose
only that every component satisfies `aᵢᵢ ≥ -2wᵢ` and that the intersection graph is not a tree,
that is, has positive topological genus. For every component `i` of a cycle `C` in the graph,
the two neighbours of `i` along `C` each meet `i` with `aᵢⱼ ≥ wᵢ`, so the row sums
`∑_{j ∈ C} aᵢⱼ` of the all-ones vector on `C` are nonnegative. Since the intersection form is
negative definite on proper subsets of the components and vanishes only on the multiples of the
multiplicity vector, the cycle passes through every component, all multiplicities are equal,
every component satisfies `aᵢᵢ = -2wᵢ` and meets exactly two others, each with `aᵢⱼ = wᵢ`, and
consequently all weights are equal; the topological genus is then one. The intersection matrix is
`-w` times the Cartan matrix of the affine Dynkin diagram `Ã_{n-1}`, and for a minimal type of
genus one, where moreover every `gᵢ` vanishes, this is the numerical type `I_n` of a cycle of
rational curves.

## Main results

* `TauCeti.NumericalType.arithmeticGenus_eq_one_iff_of_card_eq_one`: a numerical type with one
  component `i` has genus one exactly when `gᵢ = 1`.
* `TauCeti.NumericalType.isMinimal_and_arithmeticGenus_eq_one_iff`: with more than one
  component, a numerical type is minimal of genus one exactly when every component is a
  `(-2)`-index.
* `TauCeti.NumericalType.multiplicity_eq_of_topologicalGenus_pos`,
  `TauCeti.NumericalType.weight_eq_of_topologicalGenus_pos`,
  `TauCeti.NumericalType.intersection_self_eq_of_topologicalGenus_pos`,
  `TauCeti.NumericalType.intersection_eq_weight_of_topologicalGenus_pos` and
  `TauCeti.NumericalType.ncard_neighborSet_eq_two_of_topologicalGenus_pos`: if `aᵢᵢ ≥ -2wᵢ` for
  every component and the intersection graph is not a tree, then the intersection graph is a
  single cycle through all components, with constant multiplicities and weights, as described
  above.
* `TauCeti.NumericalType.topologicalGenus_le_one`: if `aᵢᵢ ≥ -2wᵢ` for every component, the
  topological genus is at most one.

## References

The numerical types are those of the Stacks Project chapter
[*Semistable Reduction*](https://stacks.math.columbia.edu/tag/0C2P), Section
[*Numerical types*](https://stacks.math.columbia.edu/tag/0C6Y); the semidefiniteness of the
intersection form used here is [Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X).
-/

public section

namespace TauCeti

namespace NumericalType

open Finset Matrix

universe u

variable {T : NumericalType.{u}}

/-! ### Genus one -/

/-- A numerical type with a single component `i` has genus one exactly when `gᵢ = 1`. -/
theorem arithmeticGenus_eq_one_iff_of_card_eq_one (h : Fintype.card T.Component = 1)
    (i : T.Component) : T.arithmeticGenus = 1 ↔ T.genus i = 1 := by
  rw [T.arithmeticGenus_of_card_eq_one h i]
  have hmw : (0 : ℤ) < (T.multiplicity i : ℤ) * (T.weight i : ℤ) :=
    mul_pos (Int.natCast_pos.mpr (T.multiplicity i).pos) (Int.natCast_pos.mpr (T.weight i).pos)
  constructor
  · intro heq
    have hzero : (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1) = 0 := by
      linarith
    have := (mul_eq_zero.mp hzero).resolve_left hmw.ne'
    omega
  · intro hg
    simp [hg]

/-- With more than one component, a numerical type is minimal of genus one exactly when every
component is a `(-2)`-index. -/
theorem isMinimal_and_arithmeticGenus_eq_one_iff (h : 1 < Fintype.card T.Component) :
    T.IsMinimal ∧ T.arithmeticGenus = 1 ↔ ∀ i, T.IsMinusTwoIndex i := by
  have hg := T.arithmeticGenus_eq_one_add_sum_genusContribution
  constructor
  · rintro ⟨hT, hg₁⟩ i
    have hsum : ∑ i, T.genusContribution i = 0 := by
      rw [hg₁] at hg
      push_cast at hg
      linarith
    rw [← T.genusContribution_eq_zero_iff h]
    exact (sum_eq_zero_iff_of_nonneg fun j _ ↦ hT.genusContribution_nonneg h j).mp hsum i
      (mem_univ i)
  · intro h₂
    refine ⟨T.isMinimal_iff.mpr fun i ↦ IsMinusTwoIndex.not_isMinusOneIndex T (h₂ i), ?_⟩
    have hsum : ∑ i, T.genusContribution i = 0 :=
      sum_eq_zero fun i _ ↦ (T.genusContribution_eq_zero_iff h i).mpr (h₂ i)
    rw [hsum, add_zero] at hg
    exact_mod_cast hg

/-! ### Numerical types whose intersection graph has a cycle -/

/-- Two adjacent components satisfy `wᵢ ≤ aᵢⱼ`. -/
private lemma weight_le_intersection_of_adj {i j : T.Component} (h : T.Adj i j) :
    (T.weight i : ℤ) ≤ T.intersection i j :=
  Int.le_of_dvd (T.adj_iff.mp h).2 (T.weight_dvd i j)

/-- Enlarging a set of components containing `i` does not decrease the sum of the intersection
numbers of `i` with its members. -/
private lemma sum_intersection_le_of_subset {i : T.Component} {u s : Finset T.Component}
    (hus : u ⊆ s) (hi : i ∈ u) : ∑ l ∈ u, T.intersection i l ≤ ∑ l ∈ s, T.intersection i l :=
  sum_le_sum_of_subset_of_nonneg hus fun l _ hl ↦
    T.offDiagonal_nonneg i l fun hil ↦ hl (hil ▸ hi)

/-- The row sum of `i` over a set containing `i` and two distinct neighbours `j` and `k` of `i`
is at least `aᵢᵢ + aᵢⱼ + aᵢₖ`. -/
private lemma intersection_add_add_le {i j k : T.Component} {s : Finset T.Component}
    (hij : T.Adj i j) (hik : T.Adj i k) (hjk : j ≠ k) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    T.intersection i i + T.intersection i j + T.intersection i k ≤
      ∑ l ∈ s, T.intersection i l := by
  have h := sum_intersection_le_of_subset (T := T) (u := {i, j, k}) (s := s)
    (by simp [insert_subset_iff, hi, hj, hk]) (mem_insert_self i _)
  rwa [sum_insert (by simp [(T.adj_iff.mp hij).1, (T.adj_iff.mp hik).1]), sum_pair hjk,
    ← add_assoc] at h

/-- If the intersection graph is not a tree, there is a nonempty set of components, namely the
vertices of a cycle, each of which has two distinct neighbours in the set. -/
private lemma exists_finset_forall_adj_adj (htop : 0 < T.topologicalGenus) :
    ∃ s : Finset T.Component, s.Nonempty ∧
      ∀ i ∈ s, ∃ j ∈ s, ∃ k ∈ s, j ≠ k ∧ T.Adj i j ∧ T.Adj i k := by
  classical
  have hacyc : ¬ T.intersectionGraph.IsAcyclic := fun h ↦ by
    have := T.topologicalGenus_eq_zero_iff.mpr ⟨T.intersectionGraph_connected, h⟩
    omega
  obtain ⟨v, p, hp⟩ : ∃ v, ∃ p : T.intersectionGraph.Walk v v, p.IsCycle := by
    simpa [SimpleGraph.IsAcyclic] using hacyc
  refine ⟨p.support.toFinset, ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩, fun i hi ↦ ?_⟩
  obtain ⟨j, k, hjk, hN⟩ :=
    Set.ncard_eq_two.mp (hp.ncard_neighborSet_toSubgraph_eq_two (List.mem_toFinset.mp hi))
  have hj : p.toSubgraph.Adj i j :=
    (p.toSubgraph.mem_neighborSet i j).mp (hN ▸ Set.mem_insert j {k})
  have hk : p.toSubgraph.Adj i k :=
    (p.toSubgraph.mem_neighborSet i k).mp (hN ▸ Set.mem_insert_of_mem j rfl)
  exact ⟨j, List.mem_toFinset.mpr (p.mem_support_of_adj_toSubgraph hj.symm),
    k, List.mem_toFinset.mpr (p.mem_support_of_adj_toSubgraph hk.symm), hjk,
    T.intersectionGraph_adj_iff.mp (p.toSubgraph.adj_sub hj),
    T.intersectionGraph_adj_iff.mp (p.toSubgraph.adj_sub hk)⟩

/-- If `aᵢᵢ ≥ -2wᵢ` for every component and the intersection graph is not a tree, then every row
sum `∑ₗ aᵢₗ` of the intersection matrix vanishes, every component has two distinct neighbours,
and all multiplicities agree. -/
private lemma forall_sum_intersection_eq_zero (hself : ∀ i, -(2 * (T.weight i : ℤ)) ≤
    T.intersection i i) (htop : 0 < T.topologicalGenus) :
    (∀ i, (∑ l, T.intersection i l = 0) ∧ ∃ j k, j ≠ k ∧ T.Adj i j ∧ T.Adj i k) ∧
      ∀ i j, T.multiplicity i = T.multiplicity j := by
  obtain ⟨s, hne, hs⟩ := exists_finset_forall_adj_adj htop
  -- On the vertex set `s` of a cycle, every row sum of the all-ones vector is nonnegative.
  have hrow : ∀ i ∈ s, 0 ≤ ∑ l ∈ s, T.intersection i l := fun i hi ↦ by
    obtain ⟨j, hj, k, hk, hjk, hij, hik⟩ := hs i hi
    linarith [intersection_add_add_le hij hik hjk hi hj hk, hself i,
      weight_le_intersection_of_adj hij, weight_le_intersection_of_adj hik]
  -- Negative definiteness on proper subsets forces the cycle to pass through every component.
  obtain rfl : s = univ := by
    by_contra hsu
    obtain ⟨i₀, hi₀⟩ := hne
    refine T.not_forall_fintype_sum_intersection_mul_nonneg_of_pos (I := s) (e := Subtype.val)
      Subtype.val_injective ?_ (y := fun _ ↦ 1) (fun _ ↦ zero_le_one) ⟨⟨i₀, hi₀⟩, one_pos⟩
      fun i ↦ ?_
    · rw [Fintype.card_coe]
      exact (card_lt_iff_ne_univ s).mpr hsu
    · have h := hrow i i.2
      rw [← sum_attach] at h
      simpa using h
  -- The intersection form vanishes at the all-ones vector, so every row sum vanishes and the
  -- multiplicity vector is constant.
  have hform : (fun _ ↦ (1 : ℤ)) ⬝ᵥ T.intersection *ᵥ (fun _ ↦ 1) =
      ∑ i, ∑ l, T.intersection i l := by
    rw [T.dotProduct_intersection_mulVec_of_support_subset (s := univ)
      fun i hi ↦ absurd (mem_univ i) hi]
    simp
  have hsum : ∑ i, ∑ l, T.intersection i l = 0 :=
    le_antisymm (hform ▸ T.dotProduct_intersection_mulVec_nonpos _)
      (sum_nonneg fun i _ ↦ hrow i (mem_univ i))
  refine ⟨fun i ↦ ⟨(sum_eq_zero_iff_of_nonneg fun i _ ↦ hrow i (mem_univ i)).mp hsum i
    (mem_univ i), ?_⟩, fun i j ↦ ?_⟩
  · obtain ⟨j, -, k, -, hjk, hij, hik⟩ := hs i (mem_univ i)
    exact ⟨j, k, hjk, hij, hik⟩
  · have h := (T.dotProduct_intersection_mulVec_eq_zero_iff _).mp (hform.trans hsum) j i
    simp only [mul_one, Nat.cast_inj, PNat.coe_inj] at h
    exact h

/-- A vanishing row sum `aᵢᵢ + aᵢⱼ + aᵢₖ + ⋯ = 0` with `aᵢᵢ ≥ -2wᵢ` at a component `i` with two
distinct neighbours `j` and `k` is tight: `aᵢᵢ = -2wᵢ`, `aᵢⱼ = aᵢₖ = wᵢ`, and `i` has no
further neighbour. -/
private lemma intersection_eq_of_sum_intersection_eq_zero {i j k : T.Component}
    (hself : -(2 * (T.weight i : ℤ)) ≤ T.intersection i i) (hrow : ∑ l, T.intersection i l = 0)
    (hjk : j ≠ k) (hij : T.Adj i j) (hik : T.Adj i k) :
    T.intersection i i = -(2 * (T.weight i : ℤ)) ∧ (∀ l, T.Adj i l ↔ l = j ∨ l = k) ∧
      T.intersection i j = T.weight i ∧ T.intersection i k = T.weight i := by
  have h₃ := intersection_add_add_le hij hik hjk (mem_univ i) (mem_univ j) (mem_univ k)
  have hwj := weight_le_intersection_of_adj hij
  have hwk := weight_le_intersection_of_adj hik
  rw [hrow] at h₃
  refine ⟨by linarith, fun l ↦ ⟨fun hil ↦ ?_, ?_⟩, by linarith, by linarith⟩
  · by_contra hl
    rw [not_or] at hl
    -- A third neighbour `l` would make the row sum of `i` positive.
    have h₄ := sum_intersection_le_of_subset (T := T) (u := {i, j, k, l}) (subset_univ _)
      (mem_insert_self i _)
    rw [sum_insert (by simp [(T.adj_iff.mp hij).1, (T.adj_iff.mp hik).1, (T.adj_iff.mp hil).1]),
      sum_insert (by simp [hjk, Ne.symm hl.1]), sum_pair (Ne.symm hl.2), hrow] at h₄
    linarith [weight_le_intersection_of_adj hil, (T.weight i).pos]
  · rintro (rfl | rfl)
    exacts [hij, hik]

/-- The structure of a numerical type with `aᵢᵢ ≥ -2wᵢ` for every component whose intersection
graph is not a tree: all multiplicities agree, and every component `i` satisfies `aᵢᵢ = -2wᵢ`
and meets exactly two other components `j` and `k`, with `aᵢⱼ = aᵢₖ = wᵢ`. -/
private theorem cycle_structure (hself : ∀ i, -(2 * (T.weight i : ℤ)) ≤ T.intersection i i)
    (htop : 0 < T.topologicalGenus) :
    (∀ i j, T.multiplicity i = T.multiplicity j) ∧
      ∀ i, T.intersection i i = -(2 * (T.weight i : ℤ)) ∧
        ∃ j k, j ≠ k ∧ (∀ l, T.Adj i l ↔ l = j ∨ l = k) ∧
          T.intersection i j = T.weight i ∧ T.intersection i k = T.weight i := by
  obtain ⟨hrow, hm⟩ := forall_sum_intersection_eq_zero hself htop
  refine ⟨hm, fun i ↦ ?_⟩
  obtain ⟨hrow₀, j, k, hjk, hij, hik⟩ := hrow i
  obtain ⟨hii, hadj, hj, hk⟩ :=
    intersection_eq_of_sum_intersection_eq_zero (hself i) hrow₀ hjk hij hik
  exact ⟨hii, j, k, hjk, hadj, hj, hk⟩

variable (hself : ∀ i, -(2 * (T.weight i : ℤ)) ≤ T.intersection i i)
  (htop : 0 < T.topologicalGenus)
include hself htop

/-- If `aᵢᵢ ≥ -2wᵢ` for every component and the intersection graph is not a tree, then all
multiplicities are equal. -/
theorem multiplicity_eq_of_topologicalGenus_pos (i j : T.Component) :
    T.multiplicity i = T.multiplicity j :=
  (cycle_structure hself htop).1 i j

/-- If `aᵢᵢ ≥ -2wᵢ` for every component and the intersection graph is not a tree, then
`aᵢᵢ = -2wᵢ` for every component. -/
theorem intersection_self_eq_of_topologicalGenus_pos (i : T.Component) :
    T.intersection i i = -(2 * (T.weight i : ℤ)) :=
  ((cycle_structure hself htop).2 i).1

/-- If `aᵢᵢ ≥ -2wᵢ` for every component and the intersection graph is not a tree, then any two
components that meet do so with intersection number `aᵢⱼ = wᵢ`. -/
theorem intersection_eq_weight_of_topologicalGenus_pos {i j : T.Component} (h : T.Adj i j) :
    T.intersection i j = T.weight i := by
  obtain ⟨-, j', k', -, hadj, hj', hk'⟩ := (cycle_structure hself htop).2 i
  rcases (hadj j).mp h with rfl | rfl
  exacts [hj', hk']

/-- If `aᵢᵢ ≥ -2wᵢ` for every component and the intersection graph is not a tree, then every
component meets exactly two others. -/
theorem ncard_neighborSet_eq_two_of_topologicalGenus_pos (i : T.Component) :
    (T.intersectionGraph.neighborSet i).ncard = 2 := by
  obtain ⟨-, j, k, hjk, hadj, -⟩ := (cycle_structure hself htop).2 i
  have hN : T.intersectionGraph.neighborSet i = {j, k} := by
    ext l
    simp only [SimpleGraph.mem_neighborSet, intersectionGraph_adj_iff, hadj l,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hN, Set.ncard_pair hjk]

/-- If `aᵢᵢ ≥ -2wᵢ` for every component and the intersection graph is not a tree, then all
weights are equal. -/
theorem weight_eq_of_topologicalGenus_pos (i j : T.Component) : T.weight i = T.weight j := by
  induction T.reflTransGen_adj i j with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih]
    have h₁ := intersection_eq_weight_of_topologicalGenus_pos hself htop hbc
    have h₂ := intersection_eq_weight_of_topologicalGenus_pos hself htop hbc.symm
    rw [T.intersection_comm, h₂] at h₁
    exact_mod_cast h₁.symm

omit htop in
/-- If `aᵢᵢ ≥ -2wᵢ` for every component, then the intersection graph has topological genus at
most one: it is either a tree or a single cycle. -/
theorem topologicalGenus_le_one : T.topologicalGenus ≤ 1 := by
  classical
  by_contra! htop
  have hdeg (i : T.Component) : T.intersectionGraph.degree i = 2 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard,
      ncard_neighborSet_eq_two_of_topologicalGenus_pos hself (by omega) i]
  have hsum := T.intersectionGraph.sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, smul_eq_mul] at hsum
  have hedge : #T.intersectionGraph.edgeFinset = T.intersectionGraph.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcard : T.intersectionGraph.edgeSet.ncard = Nat.card T.Component := by
    rw [Nat.card_eq_fintype_card]
    omega
  rw [topologicalGenus_def, hcard] at htop
  omega

end NumericalType

end TauCeti
