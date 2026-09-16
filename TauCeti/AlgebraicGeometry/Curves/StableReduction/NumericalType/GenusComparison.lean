/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Topology
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Comparing the arithmetic and topological genera of a numerical type

For a component `i` of a numerical type, put

`qᵢ = mᵢwᵢ` and `rᵢ = ∑_{j ≠ i} aᵢⱼ / wᵢ`.

The local genus defect

`qᵢ (-1 + gᵢ + rᵢ / 2) - (-1 + degree(i) / 2)`

compares the contribution of `i` to the arithmetic genus with its contribution to the first
Betti number of the intersection graph.  Summing these defects gives exactly
`arithmeticGenus - topologicalGenus`.

The divisibility axiom for a numerical type implies that `rᵢ` is at least the ordinary valence
of `i`.  Consequently the local defect is nonnegative whenever `gᵢ` is positive, `i` has at
least two neighbours, or `qᵢ = 1`.  This proves the arithmetic/topological genus comparison
whenever every component satisfies one of those conditions, in particular when the intersection
graph has minimum valence at least two.  In a connected graph with more than one vertex, the
components not covered by this local estimate are weighted genus-zero leaves.  Completing the
general minimal case requires the chain argument of
[Stacks, Lemma 55.3.14](https://stacks.math.columbia.edu/tag/0C7C).
-/

public section

namespace TauCeti

namespace NumericalType

open Finset

universe u

variable (T : NumericalType.{u})

/-- The sum `∑_{j ≠ i} aᵢⱼ / wᵢ` of the normalized intersections of a component with all other
components. Each summand is a nonnegative integer by the axioms of a numerical type. -/
noncomputable def normalizedValence (i : T.Component) : ℚ :=
  ∑ j ∈ Finset.univ.erase i, (T.intersection i j : ℚ) / (T.weight i : ℚ)

/-- The defining sum for the normalized valence. -/
lemma normalizedValence_def (i : T.Component) :
    T.normalizedValence i =
      ∑ j ∈ Finset.univ.erase i, (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
  rw [normalizedValence]

/-- The local difference between the arithmetic-genus and graph-genus contributions of a
component of a numerical type. -/
noncomputable def genusDefect (i : T.Component) : ℚ :=
  (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
      (-1 + T.genus i + T.normalizedValence i / 2) -
    (-1 + (T.intersectionGraph.neighborSet i).ncard / 2)

/-- The defining formula for the local genus defect. -/
lemma genusDefect_def (i : T.Component) :
    T.genusDefect i =
      (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
          (-1 + T.genus i + T.normalizedValence i / 2) -
        (-1 + (T.intersectionGraph.neighborSet i).ncard / 2) := by
  rw [genusDefect]

/-- The normalized valence is nonnegative. -/
lemma normalizedValence_nonneg (i : T.Component) :
    0 ≤ T.normalizedValence i := by
  apply Finset.sum_nonneg
  intro j hj
  have hij : i ≠ j := by
    exact (Finset.ne_of_mem_erase hj).symm
  exact div_nonneg (by exact_mod_cast T.offDiagonal_nonneg i j hij) (by positivity)

private lemma one_le_normalizedIntersection_of_adj {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) :
    (1 : ℚ) ≤ (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
  have hpos : (0 : ℤ) < T.intersection i j :=
    by
      rw [T.intersectionGraph_adj_iff, T.adj_iff] at hij
      exact hij.2
  have hle : (T.weight i : ℤ) ≤ T.intersection i j :=
    Int.le_of_dvd hpos (T.weight_dvd i j)
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < T.weight i)).2
  simpa using (by exact_mod_cast hle : (T.weight i : ℚ) ≤ T.intersection i j)

/-- The normalized intersection valence is at least the valence of the intersection graph. -/
lemma valence_le_normalizedValence (i : T.Component) :
    ((T.intersectionGraph.neighborSet i).ncard : ℚ) ≤ T.normalizedValence i := by
  classical
  have hcard : (T.intersectionGraph.neighborSet i).ncard =
      #({j | T.intersectionGraph.Adj i j} : Finset T.Component) := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext j
    simp
  calc
    ((T.intersectionGraph.neighborSet i).ncard : ℚ) =
        ∑ _j ∈ ({j | T.intersectionGraph.Adj i j} : Finset T.Component), (1 : ℚ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard
    _ ≤ ∑ j ∈ ({j | T.intersectionGraph.Adj i j} : Finset T.Component),
        (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
      exact Finset.sum_le_sum fun j hj ↦
        T.one_le_normalizedIntersection_of_adj (by simpa using hj)
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.mpr ⟨hj.ne.symm, Finset.mem_univ j⟩
      · intro j hj _
        have hij : i ≠ j := by exact (Finset.ne_of_mem_erase hj).symm
        exact div_nonneg (by exact_mod_cast T.offDiagonal_nonneg i j hij) (by positivity)
    _ = T.normalizedValence i := rfl

private lemma sum_fiber_offDiagonal :
    ∑ i, (T.multiplicity i : ℚ) * (T.intersection i i : ℚ) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        (T.multiplicity j : ℚ) * (T.intersection i j : ℚ) = 0 := by
  classical
  have hi (i : T.Component) :
      (T.multiplicity i : ℚ) * (T.intersection i i : ℚ) +
        ∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℚ) * (T.intersection i j : ℚ) = 0 := by
    have h := congrArg (Int.cast : ℤ → ℚ) (T.fiber_relation i)
    push_cast at h
    calc
      (T.multiplicity i : ℚ) * T.intersection i i +
          ∑ j ∈ Finset.univ.erase i,
            (T.multiplicity j : ℚ) * T.intersection i j =
          ∑ j, (T.multiplicity j : ℚ) * T.intersection i j :=
        Finset.add_sum_erase Finset.univ
          (fun j : T.Component ↦ (T.multiplicity j : ℚ) * T.intersection i j)
          (Finset.mem_univ i)
      _ = 0 := h
  calc
    _ = ∑ i, ((T.multiplicity i : ℚ) * T.intersection i i +
        ∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℚ) * T.intersection i j) := by rw [Finset.sum_add_distrib]
    _ = ∑ _i : T.Component, (0 : ℚ) := Finset.sum_congr rfl fun i _ ↦ hi i
    _ = 0 := Finset.sum_const_zero

private lemma sum_offDiagonal_swap :
    ∑ i, ∑ j ∈ Finset.univ.erase i,
        (T.multiplicity i : ℚ) * (T.intersection i j : ℚ) =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        (T.multiplicity j : ℚ) * (T.intersection i j : ℚ) := by
  classical
  calc
    _ = ∑ i, (∑ j, (T.multiplicity i : ℚ) * T.intersection i j) -
        ∑ i, (T.multiplicity i : ℚ) * T.intersection i i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      ring
    _ = ∑ i, (∑ j, (T.multiplicity j : ℚ) * T.intersection i j) -
        ∑ i, (T.multiplicity i : ℚ) * T.intersection i i := by
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
        rw [T.intersection_comm]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      ring

private lemma sum_multiplicity_mul_offDiagonal :
    ∑ i, ∑ j ∈ Finset.univ.erase i,
        (T.multiplicity i : ℚ) * (T.intersection i j : ℚ) =
      -∑ i, (T.multiplicity i : ℚ) * (T.intersection i i : ℚ) := by
  rw [T.sum_offDiagonal_swap]
  linarith [T.sum_fiber_offDiagonal]

private lemma sum_normalizedTerm_eq_sum_genusContribution :
    ∑ i, (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
        (-1 + T.genus i + T.normalizedValence i / 2) =
      ∑ i, T.genusContribution i := by
  classical
  rw [Finset.sum_congr rfl fun i _ ↦ T.genusContribution_def i]
  have hexpand (i : T.Component) :
      (T.multiplicity i : ℚ) * T.weight i *
          (-1 + T.genus i + T.normalizedValence i / 2) =
        (T.multiplicity i : ℚ) * T.weight i * ((T.genus i : ℚ) - 1) +
          (∑ j ∈ Finset.univ.erase i,
            (T.multiplicity i : ℚ) * T.intersection i j) / 2 := by
    rw [normalizedValence, ← Finset.sum_div, ← Finset.mul_sum]
    have hw : (T.weight i : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  calc
    ∑ i, (T.multiplicity i : ℚ) * T.weight i *
        (-1 + T.genus i + T.normalizedValence i / 2) =
        ∑ i, ((T.multiplicity i : ℚ) * T.weight i * ((T.genus i : ℚ) - 1) +
          (∑ j ∈ Finset.univ.erase i,
            (T.multiplicity i : ℚ) * T.intersection i j) / 2) :=
      Finset.sum_congr rfl fun i _ ↦ hexpand i
    _ = ∑ i, (T.multiplicity i : ℚ) * T.weight i * ((T.genus i : ℚ) - 1) +
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          (T.multiplicity i : ℚ) * T.intersection i j) / 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i, (T.multiplicity i : ℚ) * T.weight i * ((T.genus i : ℚ) - 1) -
        (∑ i, (T.multiplicity i : ℚ) * T.intersection i i) / 2 := by
      rw [T.sum_multiplicity_mul_offDiagonal]
      ring
    _ = ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.genus i : ℚ) - 1) - T.intersection i i / 2) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The sum of the local genus defects is the arithmetic genus minus the topological genus. -/
theorem sum_genusDefect :
    ∑ i, T.genusDefect i = (T.arithmeticGenus : ℚ) - T.topologicalGenus := by
  classical
  rw [Finset.sum_congr rfl fun i _ ↦ T.genusDefect_def i,
    Finset.sum_sub_distrib, T.sum_normalizedTerm_eq_sum_genusContribution,
    T.arithmeticGenus_eq_one_add_sum_genusContribution]
  have hdegree := T.intersectionGraph.sum_degrees_eq_twice_card_edges
  have hedge : #T.intersectionGraph.edgeFinset = T.intersectionGraph.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hvalence (v : T.Component) :
      (T.intersectionGraph.neighborSet v).ncard = T.intersectionGraph.degree v := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact T.intersectionGraph.card_neighborSet_eq_degree v
  have hdegree' : ∑ v, (T.intersectionGraph.neighborSet v).ncard =
      2 * T.intersectionGraph.edgeSet.ncard := by
    calc
      ∑ v, (T.intersectionGraph.neighborSet v).ncard =
          ∑ v, T.intersectionGraph.degree v := Finset.sum_congr rfl fun v _ ↦ hvalence v
      _ = 2 * #T.intersectionGraph.edgeFinset := hdegree
      _ = 2 * T.intersectionGraph.edgeSet.ncard := by rw [hedge]
  have hdegreeQ : (∑ v, (T.intersectionGraph.neighborSet v).ncard : ℚ) =
      2 * T.intersectionGraph.edgeSet.ncard := by exact_mod_cast hdegree'
  have hhalf : ∑ v, ((T.intersectionGraph.neighborSet v).ncard : ℚ) / 2 =
      (T.intersectionGraph.edgeSet.ncard : ℚ) := by
    rw [← Finset.sum_div]
    linarith
  have htop := congrArg (Int.cast : ℤ → ℚ) T.topologicalGenus_def
  push_cast at htop
  rw [htop]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  norm_num
  rw [hhalf]
  ring

/-- A component has nonnegative genus defect if it has positive genus, at least two neighbours,
or multiplicity times weight equal to one. -/
theorem genusDefect_nonneg_of (i : T.Component)
    (h : 0 < T.genus i ∨ 2 ≤ (T.intersectionGraph.neighborSet i).ncard ∨
      T.multiplicity i * T.weight i = 1) :
    0 ≤ T.genusDefect i := by
  rw [T.genusDefect_def]
  have hs := T.valence_le_normalizedValence i
  have hs0 := T.normalizedValence_nonneg i
  have hq : (1 : ℚ) ≤ (T.multiplicity i : ℚ) * (T.weight i : ℚ) := by
    have hm : (1 : ℚ) ≤ T.multiplicity i := by exact_mod_cast (T.multiplicity i).pos
    have hw : (1 : ℚ) ≤ T.weight i := by exact_mod_cast (T.weight i).pos
    nlinarith
  rcases h with hg | hd | hq1
  · have hgq : (1 : ℚ) ≤ T.genus i := by exact_mod_cast hg
    have hbase : 0 ≤ -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 := by
      linarith
    have hmul : -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 ≤
        (T.multiplicity i : ℚ) * T.weight i *
          (-1 + T.genus i + T.normalizedValence i / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) hbase]
    linarith
  · have hdq : (2 : ℚ) ≤ (T.intersectionGraph.neighborSet i).ncard := by exact_mod_cast hd
    have hbase : 0 ≤ -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 := by
      have hg0 : (0 : ℚ) ≤ T.genus i := by positivity
      linarith
    have hmul : -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 ≤
        (T.multiplicity i : ℚ) * T.weight i *
          (-1 + T.genus i + T.normalizedValence i / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) hbase]
    linarith
  · have hq1' : (T.multiplicity i : ℚ) * (T.weight i : ℚ) = 1 := by
      exact_mod_cast hq1
    rw [hq1']
    have hg0 : (0 : ℚ) ≤ T.genus i := by positivity
    linarith

/-- If every component has positive genus, at least two neighbours, or unit weighted
multiplicity, then the topological genus is at most the arithmetic genus. -/
theorem topologicalGenus_le_arithmeticGenus_of_forall (h : ∀ i : T.Component,
    0 < T.genus i ∨ 2 ≤ (T.intersectionGraph.neighborSet i).ncard ∨
      T.multiplicity i * T.weight i = 1) :
    T.topologicalGenus ≤ T.arithmeticGenus := by
  have hsum : (0 : ℚ) ≤ ∑ i, T.genusDefect i :=
    Finset.sum_nonneg fun i _ ↦ T.genusDefect_nonneg_of i (h i)
  rw [T.sum_genusDefect] at hsum
  have hq : (T.topologicalGenus : ℚ) ≤ T.arithmeticGenus := by linarith
  exact_mod_cast hq

/-- If the intersection graph has minimum degree at least two, then the topological genus is at
most the arithmetic genus. -/
theorem topologicalGenus_le_arithmeticGenus_of_two_le_valence
    (h : ∀ i : T.Component, 2 ≤ (T.intersectionGraph.neighborSet i).ncard) :
    T.topologicalGenus ≤ T.arithmeticGenus :=
  T.topologicalGenus_le_arithmeticGenus_of_forall fun i ↦ Or.inr (Or.inl (h i))

end NumericalType

end TauCeti
