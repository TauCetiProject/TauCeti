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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

With two or three components the minimal types of genus one are listed explicitly, as the types
(2) to (9) of [Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T). Write
`aᵢⱼ = wᵢα = wⱼβ` for two components that meet. Dividing the fibre relation `∑ⱼ aᵢⱼmⱼ = 0` at a
`(-2)`-index `i` by `wᵢ` turns it into a linear relation between the multiplicities with these
quotients as coefficients. With two components `i` and `j` the two relations force `αβ = 4`. With
three components forming a chain `i - j - k` they force `αβ + γδ = 4`, where `aⱼₖ = wⱼγ = wₖδ`.
The few positive integer solutions of these equations are the listed types. Three components that
pairwise meet form a cycle, to which the description above applies.

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
* `TauCeti.NumericalType.isMinimal_and_arithmeticGenus_eq_one_iff_of_card_eq_two` and
  `TauCeti.NumericalType.isMinimal_and_arithmeticGenus_eq_one_iff_of_card_eq_three`: the minimal
  numerical types of genus one with two and with three components.
* `TauCeti.NumericalType.IsGenusOnePairShape` and `TauCeti.NumericalType.IsGenusOneChainShape`:
  the shapes of the minimal numerical types of genus one with two components, and with three
  components forming a chain.
* `TauCeti.NumericalType.exists_weight_multiplicity_intersection_eq_of_card_eq_two` and
  `TauCeti.NumericalType.exists_weight_multiplicity_intersection_eq_of_card_eq_three`: the shapes
  of a numerical type with two components, or with three components forming a chain, all of
  self-intersection `-2w`.

## References

The numerical types are those of the Stacks Project chapter
[*Semistable Reduction*](https://stacks.math.columbia.edu/tag/0C2P), Section
[*Numerical types*](https://stacks.math.columbia.edu/tag/0C6Y); the semidefiniteness of the
intersection form used here is [Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X). The
classification of minimal numerical types of genus one is
[Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T).
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

section Cycle

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

end Cycle

/-- Two components that meet have intersection number `aᵢⱼ = wᵢα = wⱼβ` for positive integers `α`
and `β`. -/
private lemma exists_intersection_eq_weight_mul {i j : T.Component}
    (h : 0 < T.intersection i j) : ∃ α β : ℤ, 0 < α ∧ 0 < β ∧
      T.intersection i j = T.weight i * α ∧ T.intersection i j = T.weight j * β := by
  obtain ⟨α, hα⟩ := T.weight_dvd i j
  obtain ⟨β, hβ⟩ := T.weight_dvd j i
  rw [T.intersection_comm j i] at hβ
  exact ⟨α, β, pos_of_mul_pos_right (hα ▸ h) (by positivity),
    pos_of_mul_pos_right (hβ ▸ h) (by positivity), hα, hβ⟩

/-! ### Two components -/

variable (T) in
/-- Two components `x` and `y` of a numerical type have one of the two shapes of the minimal types
of genus one with two components, the types (2) and (3) of
[Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T): either `w_y = w_x`,
`m_y = m_x` and `a_{xy} = 2w_x`, or `w_y = 4w_x`, `m_x = 2m_y` and `a_{xy} = 4w_x`. -/
def IsGenusOnePairShape (x y : T.Component) : Prop :=
  ((T.weight y : ℤ) = T.weight x ∧ (T.multiplicity y : ℤ) = T.multiplicity x ∧
      T.intersection x y = 2 * T.weight x) ∨
    ((T.weight y : ℤ) = 4 * T.weight x ∧ (T.multiplicity x : ℤ) = 2 * T.multiplicity y ∧
      T.intersection x y = 4 * T.weight x)

/-- The two explicit alternatives defining a genus-one pair shape. -/
lemma isGenusOnePairShape_iff {x y : T.Component} :
    T.IsGenusOnePairShape x y ↔
      ((T.weight y : ℤ) = T.weight x ∧ (T.multiplicity y : ℤ) = T.multiplicity x ∧
        T.intersection x y = 2 * T.weight x) ∨
      ((T.weight y : ℤ) = 4 * T.weight x ∧ (T.multiplicity x : ℤ) = 2 * T.multiplicity y ∧
        T.intersection x y = 4 * T.weight x) :=
  Iff.rfl

/-- The fibre relation at a component `l` of a numerical type whose components are `i` and
`j`. -/
private lemma fiber_relation_of_univ_eq_pair {i j : T.Component} (hij : i ≠ j)
    (hu : (univ : Finset T.Component) = {i, j}) (l : T.Component) :
    (T.multiplicity i : ℤ) * T.intersection l i + T.multiplicity j * T.intersection l j = 0 := by
  have h := T.fiber_relation l
  rwa [hu, sum_pair hij] at h

/-- If a numerical type has exactly two components `i` and `j`, each of self-intersection `-2w`,
then, writing `x` and `y` for `i` and `j` in a suitable order, they have one of the two shapes of
`TauCeti.NumericalType.IsGenusOnePairShape`. -/
theorem exists_weight_multiplicity_intersection_eq_of_card_eq_two
    (hcard : Fintype.card T.Component = 2) {i j : T.Component} (hij : i ≠ j)
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ))) :
    ∃ x y, (x = i ∧ y = j ∨ x = j ∧ y = i) ∧ T.IsGenusOnePairShape x y := by
  have hu : (univ : Finset T.Component) = {i, j} :=
    (eq_univ_of_card _ (by rw [card_pair hij, hcard])).symm
  have ri := fiber_relation_of_univ_eq_pair hij hu i
  have rj := fiber_relation_of_univ_eq_pair hij hu j
  rw [hi] at ri
  rw [hj, T.intersection_comm j i] at rj
  have hwi : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
  have hwj : (0 : ℤ) < T.weight j := Int.natCast_pos.mpr (T.weight j).pos
  have hmi : (0 : ℤ) < T.multiplicity i := Int.natCast_pos.mpr (T.multiplicity i).pos
  have hmj : (0 : ℤ) < T.multiplicity j := Int.natCast_pos.mpr (T.multiplicity j).pos
  -- Write `aᵢⱼ = wᵢα = wⱼβ`; the fibre relations become `mⱼα = 2mᵢ` and `mᵢβ = 2mⱼ`.
  obtain ⟨α, β, hα₀, hβ₀, hα, hβ⟩ := exists_intersection_eq_weight_mul
    (pos_of_mul_pos_right (by linarith [mul_pos hmi hwi]) hmj.le)
  have e₁ : (T.multiplicity j : ℤ) * α = 2 * T.multiplicity i :=
    mul_left_cancel₀ hwi.ne' (by rw [hα] at ri; linear_combination ri)
  have e₂ : (T.multiplicity i : ℤ) * β = 2 * T.multiplicity j :=
    mul_left_cancel₀ hwj.ne' (by rw [hβ] at rj; linear_combination rj)
  have hαβ : α * β = 4 := by
    have h : (α * β - 4) * (T.multiplicity i * T.multiplicity j) = 0 := by
      linear_combination (α * T.multiplicity j) * e₂ + 2 * T.multiplicity j * e₁
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (mul_pos hmi hmj).ne')
  have hα₄ : α ≤ 4 := by nlinarith
  have hβ₄ : β ≤ 4 := by nlinarith
  simp only [isGenusOnePairShape_iff]
  interval_cases α <;> interval_cases β <;>
    first
    | omega
    | exact ⟨i, j, .inl ⟨rfl, rfl⟩, by omega⟩
    | exact ⟨j, i, .inr ⟨rfl, rfl⟩, by rw [T.intersection_comm j i]; omega⟩

/-- In a numerical type with exactly two components `x` and `y` of one of the two shapes of
`TauCeti.NumericalType.IsGenusOnePairShape`, the fibre relation forces both self-intersections to
be `-2w`. -/
private lemma intersection_self_eq_of_card_eq_two {x y : T.Component} (hxy : x ≠ y)
    (hu : (univ : Finset T.Component) = {x, y}) (hpat : T.IsGenusOnePairShape x y) :
    T.intersection x x = -(2 * (T.weight x : ℤ)) ∧
      T.intersection y y = -(2 * (T.weight y : ℤ)) := by
  have rx := fiber_relation_of_univ_eq_pair hxy hu x
  have ry := fiber_relation_of_univ_eq_pair hxy hu y
  rw [T.intersection_comm y x] at ry
  have hm (l : T.Component) : (T.multiplicity l : ℤ) ≠ 0 :=
    (Int.natCast_pos.mpr (T.multiplicity l).pos).ne'
  rw [isGenusOnePairShape_iff] at hpat
  -- Rewrite every datum in terms of `w_x` and one multiplicity, then cancel the multiplicity.
  constructor <;> [apply mul_left_cancel₀ (hm x); apply mul_left_cancel₀ (hm y)] <;>
    rcases hpat with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ <;> simp only [h₁, h₂, h₃] at rx ry ⊢
  exacts [by linear_combination rx, by linear_combination rx, by linear_combination ry,
    by linear_combination ry]

/-- A numerical type with exactly two components `i` and `j` is minimal of genus one exactly when
both components have genus zero and, writing `x` and `y` for `i` and `j` in a suitable order,
they have one of the two shapes of `TauCeti.NumericalType.IsGenusOnePairShape`. These are the
types (2) and (3) of [Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T); the
self-intersections are then `-2w_x` and `-2w_y`. -/
theorem isMinimal_and_arithmeticGenus_eq_one_iff_of_card_eq_two
    (hcard : Fintype.card T.Component = 2) {i j : T.Component} (hij : i ≠ j) :
    T.IsMinimal ∧ T.arithmeticGenus = 1 ↔ T.genus i = 0 ∧ T.genus j = 0 ∧
      ∃ x y, (x = i ∧ y = j ∨ x = j ∧ y = i) ∧ T.IsGenusOnePairShape x y := by
  have hu : (univ : Finset T.Component) = {i, j} :=
    (eq_univ_of_card _ (by rw [card_pair hij, hcard])).symm
  rw [isMinimal_and_arithmeticGenus_eq_one_iff (by omega)]
  simp only [isMinusTwoIndex_iff]
  constructor
  · intro h
    exact ⟨(h i).1, (h j).1,
      exists_weight_multiplicity_intersection_eq_of_card_eq_two hcard hij (h i).2 (h j).2⟩
  · rintro ⟨hgi, hgj, x, y, hxy, hpat⟩
    have hself : T.intersection i i = -(2 * (T.weight i : ℤ)) ∧
        T.intersection j j = -(2 * (T.weight j : ℤ)) := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact intersection_self_eq_of_card_eq_two hij hu hpat
      · exact (intersection_self_eq_of_card_eq_two hij.symm (hu.trans (pair_comm _ _)) hpat).symm
    intro l
    rcases (by simpa [hu] using mem_univ l : l = i ∨ l = j) with rfl | rfl
    exacts [⟨hgi, hself.1⟩, ⟨hgj, hself.2⟩]

/-! ### Three components -/

variable (T) in
/-- Three components `x`, `j` and `z` of a numerical type have, along the chain `x - j - z`, one of
the five shapes of the minimal types of genus one whose three components form a chain, the types
(5) to (9) of [Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T). Listing data in
the order `(x, j, z)` and writing `w` and `m` for a weight and a multiplicity, these are:

* weights `(w, w, 3w)`, multiplicities `(m, 2m, m)`, `a_{xj} = w` and `a_{jz} = 3w`;
* weights `(3w, 3w, w)`, multiplicities `(m, 2m, 3m)`, `a_{xj} = a_{jz} = 3w`;
* weights `(w, 2w, 4w)`, multiplicities `(2m, 2m, m)`, `a_{xj} = 2w` and `a_{jz} = 4w`;
* weights `(w, 2w, w)`, multiplicities `(m, m, m)`, `a_{xj} = a_{jz} = 2w`;
* weights `(2w, w, 2w)`, multiplicities `(m, 2m, m)`, `a_{xj} = a_{jz} = 2w`.

The predicate does not record `a_{xz}`. -/
def IsGenusOneChainShape (x j z : T.Component) : Prop :=
  ((T.weight j : ℤ) = T.weight x ∧ (T.weight z : ℤ) = 3 * T.weight x ∧
      (T.multiplicity j : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity x ∧
      T.intersection x j = T.weight x ∧ T.intersection j z = 3 * T.weight x) ∨
    ((T.weight x : ℤ) = 3 * T.weight z ∧ (T.weight j : ℤ) = 3 * T.weight z ∧
      (T.multiplicity j : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity z : ℤ) = 3 * T.multiplicity x ∧
      T.intersection x j = 3 * T.weight z ∧ T.intersection j z = 3 * T.weight z) ∨
    ((T.weight j : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = 4 * T.weight x ∧
      (T.multiplicity j : ℤ) = T.multiplicity x ∧
      (T.multiplicity x : ℤ) = 2 * T.multiplicity z ∧
      T.intersection x j = 2 * T.weight x ∧ T.intersection j z = 4 * T.weight x) ∨
    ((T.weight j : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = T.weight x ∧
      (T.multiplicity j : ℤ) = T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity x ∧
      T.intersection x j = 2 * T.weight x ∧ T.intersection j z = 2 * T.weight x) ∨
    ((T.weight x : ℤ) = 2 * T.weight j ∧ (T.weight z : ℤ) = 2 * T.weight j ∧
      (T.multiplicity j : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity x ∧
      T.intersection x j = 2 * T.weight j ∧ T.intersection j z = 2 * T.weight j)

/-- The five explicit alternatives defining a genus-one chain shape. -/
lemma isGenusOneChainShape_iff {x j z : T.Component} :
    T.IsGenusOneChainShape x j z ↔
      ((T.weight j : ℤ) = T.weight x ∧ (T.weight z : ℤ) = 3 * T.weight x ∧
        (T.multiplicity j : ℤ) = 2 * T.multiplicity x ∧
        (T.multiplicity z : ℤ) = T.multiplicity x ∧
        T.intersection x j = T.weight x ∧ T.intersection j z = 3 * T.weight x) ∨
      ((T.weight x : ℤ) = 3 * T.weight z ∧ (T.weight j : ℤ) = 3 * T.weight z ∧
        (T.multiplicity j : ℤ) = 2 * T.multiplicity x ∧
        (T.multiplicity z : ℤ) = 3 * T.multiplicity x ∧
        T.intersection x j = 3 * T.weight z ∧ T.intersection j z = 3 * T.weight z) ∨
      ((T.weight j : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = 4 * T.weight x ∧
        (T.multiplicity j : ℤ) = T.multiplicity x ∧
        (T.multiplicity x : ℤ) = 2 * T.multiplicity z ∧
        T.intersection x j = 2 * T.weight x ∧ T.intersection j z = 4 * T.weight x) ∨
      ((T.weight j : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = T.weight x ∧
        (T.multiplicity j : ℤ) = T.multiplicity x ∧
        (T.multiplicity z : ℤ) = T.multiplicity x ∧
        T.intersection x j = 2 * T.weight x ∧ T.intersection j z = 2 * T.weight x) ∨
      ((T.weight x : ℤ) = 2 * T.weight j ∧ (T.weight z : ℤ) = 2 * T.weight j ∧
        (T.multiplicity j : ℤ) = 2 * T.multiplicity x ∧
        (T.multiplicity z : ℤ) = T.multiplicity x ∧
        T.intersection x j = 2 * T.weight j ∧ T.intersection j z = 2 * T.weight j) :=
  Iff.rfl

/-- The fibre relation at a component `l` of a numerical type whose components are `i`, `j` and
`k`. -/
private lemma fiber_relation_of_univ_eq_triple {i j k : T.Component} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hu : (univ : Finset T.Component) = {i, j, k}) (l : T.Component) :
    (T.multiplicity i : ℤ) * T.intersection l i + T.multiplicity j * T.intersection l j +
      T.multiplicity k * T.intersection l k = 0 := by
  have h := T.fiber_relation l
  rwa [hu, sum_insert (by simp [hij, hik]), sum_pair hjk, ← add_assoc] at h

/-- The positive integer solutions of `αβ + γδ = 4`. -/
private lemma cases_of_mul_add_mul_eq_four {α β γ δ : ℤ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (hsum : α * β + γ * δ = 4) :
    α = 1 ∧ β = 1 ∧ (γ = 1 ∧ δ = 3 ∨ γ = 3 ∧ δ = 1) ∨
      (α = 1 ∧ β = 3 ∨ α = 3 ∧ β = 1) ∧ γ = 1 ∧ δ = 1 ∨
      (α = 1 ∧ β = 2 ∨ α = 2 ∧ β = 1) ∧ (γ = 1 ∧ δ = 2 ∨ γ = 2 ∧ δ = 1) := by
  have hα₃ : α ≤ 3 := by nlinarith
  have hβ₃ : β ≤ 3 := by nlinarith
  have hγ₃ : γ ≤ 3 := by nlinarith
  have hδ₃ : δ ≤ 3 := by nlinarith
  interval_cases α <;> interval_cases β <;> interval_cases γ <;> interval_cases δ <;> omega

/-- If a numerical type has exactly three components `i`, `j` and `k`, each of self-intersection
`-2w`, and `i` and `k` do not meet, then the components form a chain `x - j - z`, where `x` and
`z` are `i` and `k` in a suitable order, of one of the five shapes of
`TauCeti.NumericalType.IsGenusOneChainShape`. -/
theorem exists_weight_multiplicity_intersection_eq_of_card_eq_three
    (hcard : Fintype.card T.Component = 3) {i j k : T.Component} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ))) (hik₀ : T.intersection i k = 0) :
    ∃ x z, (x = i ∧ z = k ∨ x = k ∧ z = i) ∧ T.IsGenusOneChainShape x j z := by
  have hu : (univ : Finset T.Component) = {i, j, k} :=
    (eq_univ_of_card _ (by
      rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk, hcard])).symm
  have ri := fiber_relation_of_univ_eq_triple hij hik hjk hu i
  have rj := fiber_relation_of_univ_eq_triple hij hik hjk hu j
  have rk := fiber_relation_of_univ_eq_triple hij hik hjk hu k
  rw [hi, hik₀] at ri
  rw [hj, T.intersection_comm j i] at rj
  rw [hk, T.intersection_comm k i, hik₀, T.intersection_comm k j] at rk
  have hwi : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
  have hwj : (0 : ℤ) < T.weight j := Int.natCast_pos.mpr (T.weight j).pos
  have hwk : (0 : ℤ) < T.weight k := Int.natCast_pos.mpr (T.weight k).pos
  have hmi : (0 : ℤ) < T.multiplicity i := Int.natCast_pos.mpr (T.multiplicity i).pos
  have hmj : (0 : ℤ) < T.multiplicity j := Int.natCast_pos.mpr (T.multiplicity j).pos
  have hmk : (0 : ℤ) < T.multiplicity k := Int.natCast_pos.mpr (T.multiplicity k).pos
  -- Write `aᵢⱼ = wᵢα = wⱼβ` and `aⱼₖ = wⱼγ = wₖδ`. The fibre relations become `mⱼα = 2mᵢ`,
  -- `mᵢβ + mₖγ = 2mⱼ` and `mⱼδ = 2mₖ`, whence `αβ + γδ = 4`.
  obtain ⟨α, β, hα₀, hβ₀, hα, hβ⟩ := exists_intersection_eq_weight_mul (i := i) (j := j)
    (pos_of_mul_pos_right (by linarith [mul_pos hmi hwi]) hmj.le)
  obtain ⟨γ, δ, hγ₀, hδ₀, hγ, hδ⟩ := exists_intersection_eq_weight_mul (i := j) (j := k)
    (pos_of_mul_pos_right (by linarith [mul_pos hmk hwk]) hmj.le)
  have e₁ : (T.multiplicity j : ℤ) * α = 2 * T.multiplicity i :=
    mul_left_cancel₀ hwi.ne' (by rw [hα] at ri; linear_combination ri)
  have e₂ : (T.multiplicity i : ℤ) * β + T.multiplicity k * γ = 2 * T.multiplicity j :=
    mul_left_cancel₀ hwj.ne' (by rw [hβ, hγ] at rj; linear_combination rj)
  have e₃ : (T.multiplicity j : ℤ) * δ = 2 * T.multiplicity k :=
    mul_left_cancel₀ hwk.ne' (by rw [hδ] at rk; linear_combination rk)
  have hsum : α * β + γ * δ = 4 := by
    have h : (α * β + γ * δ - 4) * T.multiplicity j = 0 := by
      linear_combination β * e₁ + γ * e₃ + 2 * e₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hmj.ne')
  clear ri rj rk hu
  simp only [isGenusOneChainShape_iff]
  -- In each case, read off the shape; for the last four the chain runs from `k` to `i`.
  rcases cases_of_mul_add_mul_eq_four hα₀ hβ₀ hγ₀ hδ₀ hsum with
    ⟨rfl, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl, rfl⟩ |
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨i, k, .inl ⟨rfl, rfl⟩, .inr <| .inl <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, k, .inl ⟨rfl, rfl⟩, .inl <| by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨k, i, .inr ⟨rfl, rfl⟩, .inl <| by
      rw [T.intersection_comm k j, T.intersection_comm j i]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨k, i, .inr ⟨rfl, rfl⟩, .inr <| .inl <| by
      rw [T.intersection_comm k j, T.intersection_comm j i]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨k, i, .inr ⟨rfl, rfl⟩, .inr <| .inr <| .inl <| by
      rw [T.intersection_comm k j, T.intersection_comm j i]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, k, .inl ⟨rfl, rfl⟩, .inr <| .inr <| .inr <| .inr <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, k, .inl ⟨rfl, rfl⟩, .inr <| .inr <| .inr <| .inl <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, k, .inl ⟨rfl, rfl⟩, .inr <| .inr <| .inl <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩

/-- In a numerical type whose components form a chain `x - j - z` of one of the five shapes of
`TauCeti.NumericalType.IsGenusOneChainShape`, the fibre relation forces all three
self-intersections to be `-2w`. -/
private lemma intersection_self_eq_of_card_eq_three {x j z : T.Component} (hxj : x ≠ j)
    (hxz : x ≠ z) (hjz : j ≠ z) (hu : (univ : Finset T.Component) = {x, j, z})
    (hxz₀ : T.intersection x z = 0) (hpat : T.IsGenusOneChainShape x j z) :
    ∀ l, T.intersection l l = -(2 * (T.weight l : ℤ)) := by
  have rx := fiber_relation_of_univ_eq_triple hxj hxz hjz hu x
  have rj := fiber_relation_of_univ_eq_triple hxj hxz hjz hu j
  have rz := fiber_relation_of_univ_eq_triple hxj hxz hjz hu z
  rw [hxz₀] at rx
  rw [T.intersection_comm j x] at rj
  rw [T.intersection_comm z x, hxz₀, T.intersection_comm z j] at rz
  have hm (l : T.Component) : (T.multiplicity l : ℤ) ≠ 0 :=
    (Int.natCast_pos.mpr (T.multiplicity l).pos).ne'
  rw [isGenusOneChainShape_iff] at hpat
  intro l
  rcases (by simpa [hu] using mem_univ l : l = x ∨ l = j ∨ l = z) with rfl | rfl | rfl <;>
    apply mul_left_cancel₀ (hm l) <;>
    -- Rewrite every datum in terms of one weight and one multiplicity, then cancel the
    -- multiplicity.
    rcases hpat with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ | ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ |
      ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ | ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ | ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ <;>
    simp only [h₁, h₂, h₃, h₄, h₅, h₆] at rx rj rz ⊢
  all_goals first
    | linear_combination rx
    | linear_combination rj
    | linear_combination rz

/-- A numerical type with exactly three components is minimal of genus one exactly when every
component has genus zero and either

* all weights `w` and all multiplicities agree and any two components meet with intersection
  number `w`: the cycle of type (4) of
  [Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T); or
* the components form a chain `x - j - z` of one of the five shapes of
  `TauCeti.NumericalType.IsGenusOneChainShape`, the types (5) to (9) of
  [Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T).

In both cases every self-intersection is then `-2w`. -/
theorem isMinimal_and_arithmeticGenus_eq_one_iff_of_card_eq_three
    (hcard : Fintype.card T.Component = 3) :
    T.IsMinimal ∧ T.arithmeticGenus = 1 ↔ (∀ l, T.genus l = 0) ∧
      ((∀ l l', (T.weight l' : ℤ) = T.weight l ∧ (T.multiplicity l' : ℤ) = T.multiplicity l ∧
          (l ≠ l' → T.intersection l l' = T.weight l)) ∨
        ∃ x j z, x ≠ j ∧ x ≠ z ∧ j ≠ z ∧ T.intersection x z = 0 ∧
          T.IsGenusOneChainShape x j z) := by
  rw [isMinimal_and_arithmeticGenus_eq_one_iff (by omega)]
  simp only [isMinusTwoIndex_iff]
  constructor
  · intro h
    refine ⟨fun l ↦ (h l).1, ?_⟩
    by_cases hadj : ∀ l l', l ≠ l' → 0 < T.intersection l l'
    · -- Any two components meet, so the intersection graph is a triangle.
      left
      obtain ⟨a, b, c, hab, hac, hbc, -⟩ :=
        card_eq_three.mp (show #(univ : Finset T.Component) = 3 by rw [card_univ, hcard])
      have htop := T.topologicalGenus_pos_of_adj_of_adj_of_adj (T.adj_iff.mpr ⟨hab, hadj a b hab⟩)
        (T.adj_iff.mpr ⟨hac, hadj a c hac⟩) (T.adj_iff.mpr ⟨hbc, hadj b c hbc⟩)
      have hself (l : T.Component) : -(2 * (T.weight l : ℤ)) ≤ T.intersection l l :=
        (h l).2.ge
      intro l l'
      exact ⟨by rw [weight_eq_of_topologicalGenus_pos hself htop l' l],
        by rw [multiplicity_eq_of_topologicalGenus_pos hself htop l' l],
        fun hll' ↦ intersection_eq_weight_of_topologicalGenus_pos hself htop
          (T.adj_iff.mpr ⟨hll', hadj l l' hll'⟩)⟩
    · -- Two components `p` and `q` do not meet; the third component `r` lies between them.
      right
      push Not at hadj
      obtain ⟨p, q, hpq, hpq₀⟩ := hadj
      replace hpq₀ : T.intersection p q = 0 := le_antisymm hpq₀ (T.offDiagonal_nonneg p q hpq)
      obtain ⟨r, hr⟩ : ((univ.erase p).erase q).Nonempty := by
        rw [← card_pos, card_erase_of_mem (by simp [hpq.symm]), card_erase_of_mem (mem_univ p),
          card_univ]
        omega
      obtain ⟨hrq, hrp⟩ : r ≠ q ∧ r ≠ p := by simpa using hr
      obtain ⟨x, z, hxz, hpat⟩ := exists_weight_multiplicity_intersection_eq_of_card_eq_three
        hcard hrp.symm hpq hrq (h p).2 (h r).2 (h q).2 hpq₀
      rcases hxz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨x, r, z, hrp.symm, hpq, hrq, hpq₀, hpat⟩
      · exact ⟨x, r, z, hrq.symm, hpq.symm, hrp, by rw [T.intersection_comm, hpq₀], hpat⟩
  · rintro ⟨hg, hcyc | ⟨x, j, z, hxj, hxz, hjz, hxz₀, hpat⟩⟩
    · intro l
      refine ⟨hg l, mul_left_cancel₀ (Int.natCast_pos.mpr (T.multiplicity l).pos).ne' ?_⟩
      rw [T.multiplicity_mul_intersection_self l,
        sum_congr rfl (g := fun _ ↦ (T.multiplicity l : ℤ) * T.weight l) fun l' hl' ↦ by
          rw [(hcyc l l').2.1, (hcyc l l').2.2 (ne_of_mem_erase hl').symm],
        sum_const, card_erase_of_mem (mem_univ l), card_univ, hcard]
      simp only [Nat.add_one_sub_one, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    · have hu : (univ : Finset T.Component) = {x, j, z} :=
        (eq_univ_of_card _ (by
          rw [card_insert_of_notMem (by simp [hxj, hxz]), card_pair hjz, hcard])).symm
      exact fun l ↦ ⟨hg l, intersection_self_eq_of_card_eq_three hxj hxz hjz hu hxz₀ hpat l⟩

end NumericalType

end TauCeti
