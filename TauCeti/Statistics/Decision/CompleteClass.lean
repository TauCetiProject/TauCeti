/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Statistics.Decision.Criteria
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Pi

/-!
# Complete classes for finite parameter sets

In a closed convex set of risk vectors with coordinatewise lower bounds, every risk vector
is dominated by one that is both admissible and Bayes for some prior. First minimize the sum
of coordinates in the bounded box of dominating vectors. Then separate the strictly lower
orthant from the risk set and normalize the separating functional to have total weight one.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), Theorems 2.6.1, 2.10.1 and 2.10.2.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti

variable {Θ : Type*} {C : Set (Θ → ℝ)}

private theorem exists_admissible_risk_le_of_isClosed [Finite Θ] (hc : IsClosed C) (hb : BddBelow C)
    {x : Θ → ℝ} (hx : x ∈ C) :
    ∃ y : C, y.val ≤ x ∧ IsAdmissibleRisk (fun z : C ↦ z.val) y := by
  let := Fintype.ofFinite Θ
  obtain ⟨b, hb⟩ := hb
  have hbox : IsCompact (C ∩ Icc b x) := isCompact_Icc.of_isClosed_subset
    (hc.inter isClosed_Icc) inter_subset_right
  have hsum : Continuous fun z : Θ → ℝ ↦ ∑ i, z i :=
    continuous_finsetSum _ fun i _ ↦ continuous_apply i
  obtain ⟨y, hy, hmin⟩ := hbox.exists_isMinOn ⟨x, hx, hb hx, le_rfl⟩ hsum.continuousOn
  refine ⟨⟨y, hy.1⟩, hy.2.2, ?_⟩
  rw [isAdmissibleRisk_iff]
  rintro ⟨z, hzy, i, hi⟩
  exact ((Finset.sum_lt_sum (fun j _ ↦ hzy j) ⟨i, Finset.mem_univ _, hi⟩).not_ge)
    (hmin ⟨z.property, hb z.property, hzy.trans hy.2.2⟩)

private theorem exists_supporting_risk_weights [Fintype Θ] [Nonempty Θ] (hc : Convex ℝ C)
    {y : C} (hy : IsAdmissibleRisk (fun z : C ↦ z.val) y) :
    ∃ w : Θ → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ z ∈ C, ∑ i, w i * y.val i ≤ ∑ i, w i * z i := by
  classical
  let U : Set (Θ → ℝ) := pi univ fun i ↦ Iio (y.val i)
  have hU : ∀ v : Θ → ℝ, v ∈ U ↔ ∀ i, v i < y.val i := by simp [U]
  have hd : Disjoint U C := Set.disjoint_left.mpr fun v hv hvC ↦ by
    obtain ⟨i⟩ := ‹Nonempty Θ›
    have heq := hy.eq_of_le (δ' := ⟨v, hvC⟩) fun j ↦ ((hU v).1 hv j).le
    exact ((hU v).1 hv i).ne (congrFun heq i)
  obtain ⟨f, u, hfU, hfC⟩ := geometric_hahn_banach_open
    (convex_pi fun _ _ ↦ convex_Iio _) (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Iio) hc hd
  have hle {v : Θ → ℝ} (hv : v ≤ y.val) : f v ≤ u := by
    apply (closure_minimal (fun z hz ↦ (hfU z hz).le)
      (isClosed_le f.continuous continuous_const) : closure U ⊆ _)
    exact mem_closure_pi.mpr fun i _ ↦ by simpa only [closure_Iio, mem_Iic] using hv i
  let e (i : Θ) : Θ → ℝ := fun j ↦ if i = j then 1 else 0
  have hnonneg (i : Θ) : 0 ≤ f (e i) := by
    have h : y.val - e i ≤ y.val := fun j ↦ sub_le_self _ (by simp [e]; split <;> norm_num)
    have h' := (hle h).trans (hfC y.val y.property)
    rw [map_sub] at h'
    linarith
  have hrepr (z : Θ → ℝ) : f z = ∑ i, z i * f (e i) :=
    f.toLinearMap.pi_apply_eq_sum_univ z
  have hpos : 0 < ∑ i, f (e i) := by
    by_contra! h
    have hz : ∀ i, f (e i) = 0 := fun i ↦ (le_antisymm
      ((Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)).trans h) (hnonneg i))
    let v : Θ → ℝ := fun i ↦ y.val i - 1
    have hv := hfU v ((hU v).2 fun i ↦ sub_lt_self _ zero_lt_one)
    have hy' := hfC y.val y.property
    rw [hrepr v] at hv
    rw [hrepr y.val] at hy'
    simp only [hz, mul_zero, Finset.sum_const_zero] at hv hy'
    exact hv.not_ge hy'
  refine ⟨fun i ↦ f (e i) / ∑ j, f (e j), fun i ↦ div_nonneg (hnonneg i) hpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hpos.ne']
  · intro z hz
    have hweighted (v : Θ → ℝ) :
        ∑ i, (f (e i) / ∑ j, f (e j)) * v i = f v / ∑ j, f (e j) := by
      rw [hrepr v, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hweighted, hweighted]
    exact div_le_div_of_nonneg_right ((hle le_rfl).trans (hfC z hz)) hpos.le

/-- **Complete class theorem.** Every risk vector in a closed, convex, bounded-below risk set on
a nonempty finite parameter space is dominated by an admissible risk vector minimizing average
risk for a probability vector on the parameters. -/
theorem exists_admissible_bayes_risk_le_of_closed_convex [Fintype Θ] [Nonempty Θ] (hc : Convex ℝ C)
    (hclosed : IsClosed C) (hb : BddBelow C) {x : Θ → ℝ} (hx : x ∈ C) :
    ∃ y ∈ C, y ≤ x ∧ (¬ ∃ z ∈ C, z ≤ y ∧ ∃ i, z i < y i) ∧
      ∃ w : Θ → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
        ∀ z ∈ C, ∑ i, w i * y i ≤ ∑ i, w i * z i := by
  obtain ⟨y, hle, hy⟩ := exists_admissible_risk_le_of_isClosed hclosed hb hx
  refine ⟨y.val, y.property, hle, ?_, exists_supporting_risk_weights hc hy⟩
  rintro ⟨z, hz, hzy, i, hi⟩
  exact hi.ne (congrFun (hy.eq_of_le (δ' := ⟨z, hz⟩) hzy) i)

end TauCeti
