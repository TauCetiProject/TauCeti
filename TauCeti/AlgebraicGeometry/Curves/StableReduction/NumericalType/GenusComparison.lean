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
graph has minimum valence at least two.

For a minimal numerical type with more than one component the comparison holds without further
hypotheses: `g_top ≤ g`
([Stacks, Lemma 55.3.14](https://stacks.math.columbia.edu/tag/0C7C)).  The proof here differs
from the chain argument of the Stacks Project.  For a set `S` of components, put

`E(S) = ∑_{i ∈ S} (Φᵢ + 1 - vᵢ(S) / 2)`,

where `Φᵢ` is the genus contribution of `i` and `vᵢ(S)` is the number of components of `S`
meeting `i`, so that `E` of the set of all components is `g - g_top`.  Deleting `i` from `S`
lowers `E(S)` by `Φᵢ + 1 - vᵢ(S)`, which is nonnegative when `vᵢ(S) ≤ 1` because minimality makes
`Φᵢ` nonnegative.  Once every remaining component meets at least two others, the fibre relation
bounds `E(S)` below by a sum of nonnegative terms.

## Main results

* `TauCeti.NumericalType.sum_genusDefect`: the local defects sum to `g - g_top`.
* `TauCeti.NumericalType.topologicalGenus_le_arithmeticGenus_of_two_le_valence`: `g_top ≤ g`
  when every component has at least two neighbours.
* `TauCeti.NumericalType.IsMinimal.topologicalGenus_le_arithmeticGenus`: `g_top ≤ g` for a
  minimal numerical type with more than one component.
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
  calc
    ((T.intersectionGraph.neighborSet i).ncard : ℚ) =
        T.intersectionGraph.degree i := by
      norm_cast
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    _ =
        ∑ _j ∈ T.intersectionGraph.neighborFinset i, (1 : ℚ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ∑ j ∈ T.intersectionGraph.neighborFinset i,
        (T.intersection i j : ℚ) / (T.weight i : ℚ) :=
      Finset.sum_le_sum fun j hj ↦ T.one_le_normalizedIntersection_of_adj
        ((T.intersectionGraph.mem_neighborFinset i j).1 hj)
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_erase.mpr
          ⟨((T.intersectionGraph.mem_neighborFinset i j).1 hj).ne.symm, Finset.mem_univ j⟩
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
  have hdegree' : ∑ v, (T.intersectionGraph.neighborSet v).ncard =
      2 * T.intersectionGraph.edgeSet.ncard := by
    calc
      ∑ v, (T.intersectionGraph.neighborSet v).ncard =
          ∑ v, T.intersectionGraph.degree v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
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
theorem genusDefect_nonneg_of_genus_pos_or_two_le_valence_or_mul_eq_one (i : T.Component)
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
theorem topologicalGenus_le_arithmeticGenus_of_genus_pos_or_two_le_valence_or_mul_eq_one
    (h : ∀ i : T.Component,
      0 < T.genus i ∨ 2 ≤ (T.intersectionGraph.neighborSet i).ncard ∨
        T.multiplicity i * T.weight i = 1) :
    T.topologicalGenus ≤ T.arithmeticGenus := by
  have hsum : (0 : ℚ) ≤ ∑ i, T.genusDefect i :=
    Finset.sum_nonneg fun i _ ↦
      T.genusDefect_nonneg_of_genus_pos_or_two_le_valence_or_mul_eq_one i (h i)
  rw [T.sum_genusDefect] at hsum
  have hq : (T.topologicalGenus : ℚ) ≤ T.arithmeticGenus := by linarith
  exact_mod_cast hq

/-- If the intersection graph has minimum degree at least two, then the topological genus is at
most the arithmetic genus. -/
theorem topologicalGenus_le_arithmeticGenus_of_two_le_valence
    (h : ∀ i : T.Component, 2 ≤ (T.intersectionGraph.neighborSet i).ncard) :
    T.topologicalGenus ≤ T.arithmeticGenus :=
  T.topologicalGenus_le_arithmeticGenus_of_genus_pos_or_two_le_valence_or_mul_eq_one fun i ↦
    Or.inr (Or.inl (h i))

/-! ### Minimal numerical types -/

/-- The number of components of `S`, other than `i`, that meet `i`. -/
private def valenceIn (S : Finset T.Component) (i : T.Component) : ℕ :=
  #{j ∈ S | j ≠ i ∧ 0 < T.intersection i j}

/-- The quantity `∑_{i ∈ S} (Φᵢ + 1 - vᵢ / 2)`, where `vᵢ` is the number of components of `S`
meeting `i`. For `S` the set of all components it is the difference between the arithmetic and
the topological genus. -/
private def excess (S : Finset T.Component) : ℚ :=
  ∑ i ∈ S, (T.genusContribution i + 1 - (T.valenceIn S i : ℚ) / 2)

/-- Removing a component `i` from `S` lowers the valence of `l ≠ i` by one exactly when `l`
meets `i`. -/
private lemma valenceIn_eq_valenceIn_erase_add {S : Finset T.Component} {i l : T.Component}
    (hi : i ∈ S) (hl : l ≠ i) :
    (T.valenceIn S l : ℚ) =
      T.valenceIn (S.erase i) l + if 0 < T.intersection l i then 1 else 0 := by
  rw [valenceIn, valenceIn, Finset.filter_erase]
  split_ifs with h
  · have hmem : i ∈ {j ∈ S | j ≠ l ∧ 0 < T.intersection l j} :=
      Finset.mem_filter.mpr ⟨hi, hl.symm, h⟩
    rw [← Finset.card_erase_add_one hmem]
    push_cast
    ring
  · have hmem : i ∉ {j ∈ S | j ≠ l ∧ 0 < T.intersection l j} := by
      simp [h]
    rw [Finset.erase_eq_of_notMem hmem, add_zero]

/-- Summing, over the other components of `S`, the indicator of meeting `i` gives the valence
of `i` in `S`. -/
private lemma sum_erase_ite_intersection_pos (S : Finset T.Component) (i : T.Component) :
    ∑ l ∈ S.erase i, (if 0 < T.intersection l i then 1 else 0 : ℚ) = T.valenceIn S i := by
  rw [Finset.sum_boole, valenceIn]
  congr 2
  ext l
  simp only [Finset.mem_filter, Finset.mem_erase, T.intersection_comm l i]
  tauto

/-- Removing a component `i` from `S` changes the excess by `Φᵢ + 1 - vᵢ`. -/
private lemma excess_eq_excess_erase_add {S : Finset T.Component} {i : T.Component}
    (hi : i ∈ S) :
    T.excess S =
      T.excess (S.erase i) + (T.genusContribution i + 1 - T.valenceIn S i) := by
  rw [excess, excess, ← Finset.add_sum_erase S _ hi]
  have hterm : ∀ l ∈ S.erase i,
      T.genusContribution l + 1 - (T.valenceIn S l : ℚ) / 2 =
        (T.genusContribution l + 1 - (T.valenceIn (S.erase i) l : ℚ) / 2) -
          (if 0 < T.intersection l i then 1 else 0 : ℚ) / 2 := fun l hl ↦ by
    rw [T.valenceIn_eq_valenceIn_erase_add hi (Finset.ne_of_mem_erase hl)]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div,
    T.sum_erase_ite_intersection_pos]
  ring

/-- The fibre relation, as a formula for the contribution of a component to the signed genus. -/
private lemma genusContribution_eq_add_sum (i : T.Component) :
    T.genusContribution i =
      (T.multiplicity i : ℚ) * (T.weight i : ℚ) * ((T.genus i : ℚ) - 1) +
        (∑ l ∈ univ.erase i, (T.multiplicity l : ℚ) * (T.intersection i l : ℚ)) / 2 := by
  have h := congrArg (Int.cast : ℤ → ℚ) (T.multiplicity_mul_intersection_self i)
  push_cast at h
  rw [genusContribution_def]
  linarith

/-- The multiplicity-weighted intersections of `i` with the other components are at least the
sum of `mₗwₗ` over the components `l` of `S` that meet `i`. -/
private lemma sum_multiplicity_mul_weight_le (S : Finset T.Component) (i : T.Component) :
    ∑ l ∈ S, (if l ≠ i ∧ 0 < T.intersection i l then
        (T.multiplicity l : ℚ) * (T.weight l : ℚ) else 0) ≤
      ∑ l ∈ univ.erase i, (T.multiplicity l : ℚ) * (T.intersection i l : ℚ) := by
  rw [← Finset.sum_filter]
  refine (Finset.sum_le_sum fun l hl ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (fun l hl ↦ ?_) fun l hl _ ↦ ?_)
  · have hpos := (Finset.mem_filter.mp hl).2.2
    have hle : (T.weight l : ℤ) ≤ T.intersection i l := by
      rw [T.intersection_comm] at hpos ⊢
      exact Int.le_of_dvd hpos (T.weight_dvd l i)
    have hle' : (T.weight l : ℚ) ≤ T.intersection i l := by exact_mod_cast hle
    exact mul_le_mul_of_nonneg_left hle' (by positivity)
  · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hl).2.1, Finset.mem_univ l⟩
  · have hmul := T.multiplicity_mul_intersection_nonneg (Finset.ne_of_mem_erase hl).symm
    exact_mod_cast hmul

/-- If every component of `S` meets at least two other components of `S`, the excess of `S` is
nonnegative. -/
private lemma excess_nonneg_of_two_le_valenceIn {S : Finset T.Component}
    (hS : ∀ i ∈ S, 2 ≤ T.valenceIn S i) : 0 ≤ T.excess S := by
  let q : T.Component → ℚ := fun l ↦ (T.multiplicity l : ℚ) * (T.weight l : ℚ)
  -- Double counting: summing `q l` over the ordered pairs `(i, l)` of meeting components of `S`.
  have hswap : ∑ i ∈ S, ∑ l ∈ S, (if l ≠ i ∧ 0 < T.intersection i l then q l else 0) =
      ∑ l ∈ S, q l * T.valenceIn S l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [valenceIn, Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [T.intersection_comm i l, ne_comm (a := l)]
    split_ifs <;> ring
  have hbound : ∑ l ∈ S, q l * T.valenceIn S l / 2 +
      ∑ i ∈ S, (q i * ((T.genus i : ℚ) - 1) + 1 - (T.valenceIn S i : ℚ) / 2) ≤ T.excess S := by
    rw [excess, ← Finset.sum_div, ← hswap, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [T.genusContribution_eq_add_sum i]
    have := T.sum_multiplicity_mul_weight_le S i
    linarith
  rw [← Finset.sum_add_distrib] at hbound
  refine le_trans (Finset.sum_nonneg fun i hi ↦ ?_) hbound
  have hv : (2 : ℚ) ≤ T.valenceIn S i := by exact_mod_cast hS i hi
  have hq : 1 ≤ q i := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast (T.multiplicity i).pos) (by exact_mod_cast (T.weight i).pos)
  have hg : (0 : ℚ) ≤ T.genus i := by positivity
  have hbase : (0 : ℚ) ≤ T.genus i - 1 + T.valenceIn S i / 2 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) hbase]

/-- The excess of the set of all components is the arithmetic genus minus the topological
genus. -/
private lemma excess_univ :
    T.excess univ = (T.arithmeticGenus : ℚ) - T.topologicalGenus := by
  have hv (i : T.Component) : T.valenceIn univ i = (T.intersectionGraph.neighborSet i).ncard := by
    rw [valenceIn, ← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [ne_comm]
  rw [← T.sum_genusDefect, excess, Finset.sum_congr rfl fun i _ ↦ T.genusDefect_def i]
  simp only [hv, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [T.sum_normalizedTerm_eq_sum_genusContribution, Finset.sum_neg_distrib]
  ring

namespace IsMinimal

variable {T}

/-- In a minimal numerical type with more than one component, every set of components has
nonnegative excess. Components meeting at most one other component of the set are removed one
at a time, which does not increase the excess since their genus contributions are nonnegative. -/
private lemma excess_nonneg (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component)
    (S : Finset T.Component) : 0 ≤ T.excess S := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : ∀ i ∈ S, 2 ≤ T.valenceIn S i
    · exact T.excess_nonneg_of_two_le_valenceIn hS
    push Not at hS
    obtain ⟨i, hi, hv⟩ := hS
    have hv' : (T.valenceIn S i : ℚ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ hv
    rw [T.excess_eq_excess_erase_add hi]
    have := ih _ (Finset.erase_ssubset hi)
    have := hT.genusContribution_nonneg h i
    linarith

/-- A minimal numerical type with more than one component has topological genus at most its
arithmetic genus ([Stacks, Tag 0C7C](https://stacks.math.columbia.edu/tag/0C7C)). -/
theorem topologicalGenus_le_arithmeticGenus (hT : T.IsMinimal)
    (h : 1 < Fintype.card T.Component) : T.topologicalGenus ≤ T.arithmeticGenus := by
  have hq := hT.excess_nonneg h univ
  rw [T.excess_univ, sub_nonneg] at hq
  exact_mod_cast hq

end IsMinimal

end NumericalType

end TauCeti
