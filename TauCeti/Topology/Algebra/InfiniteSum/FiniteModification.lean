/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Finite changes of ordered harmonic sums

For coefficients in a division ring, changing finitely many coefficients adds an explicit
finite correction to the ordered harmonic sums. Once the cutoff exceeds the changed indices,
this is an exact identity (`Finset.sum_Icc_div_sub_eq_sum`). In a topological additive group,
`Finset.tendsto_sum_Icc_div_congr_finset_iff` transports convergence in both directions.
No completeness, absolute summability, or restriction on the characteristic is needed.
-/

public section

open Filter
open scoped Topology

namespace Finset

variable {K : Type*} [DivisionRing K] {a b : ℕ → K} {L : K}

/-- Once the cutoff contains every positive changed index, the difference of the ordered
harmonic sums is exactly the finite correction. Changes at index `0` contribute zero. -/
theorem sum_Icc_div_sub_eq_sum (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) {N : ℕ} (hN : S.sup id ≤ N) :
    (∑ n ∈ Icc 1 N, b n / (n : K)) - (∑ n ∈ Icc 1 N, a n / (n : K)) =
      ∑ n ∈ S, (b n - a n) / (n : K) := by
  classical
  have hsub : S.erase 0 ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hn0, hnS⟩ := mem_erase.mp hn
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0,
      (le_sup (f := id) hnS).trans hN⟩
  rw [← sum_sub_distrib]
  simp_rw [← sub_div]
  calc
    (∑ n ∈ Icc 1 N, (b n - a n) / (n : K)) =
        ∑ n ∈ S.erase 0, (b n - a n) / (n : K) := by
      apply (sum_subset hsub _).symm
      intro n hn hnS
      have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (mem_Icc.mp hn).1
      have : n ∉ S := fun h ↦ hnS (mem_erase.mpr ⟨hn0, h⟩)
      simp [hab n hn0 this]
    _ = ∑ n ∈ S, (b n - a n) / (n : K) := by
      apply sum_subset (erase_subset _ _)
      intro n hnS hn
      have : n = 0 := by simpa [hnS] using hn
      simp [this]

/-- The exact correction formula for finite changes holds eventually in the natural cutoff. -/
theorem eventually_sum_Icc_div_sub_eq_sum (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 1 N, b n / (n : K)) - (∑ n ∈ Icc 1 N, a n / (n : K)) =
        ∑ n ∈ S, (b n - a n) / (n : K) := by
  filter_upwards [eventually_ge_atTop (S.sup id)] with N hN
  exact sum_Icc_div_sub_eq_sum S hab hN

/-- Finite changes preserve convergence of ordered harmonic sums, with the explicit finite
correction to the limit. This does not assert an unconditional sum at `1`. -/
theorem tendsto_sum_Icc_div_congr_finset_iff [TopologicalSpace K]
    [IsTopologicalAddGroup K] (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, b n / (n : K)) atTop
        (𝓝 (L + ∑ n ∈ S, (b n - a n) / (n : K))) ↔
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / (n : K)) atTop (𝓝 L) := by
  have heq : (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, b n / (n : K)) =ᶠ[atTop]
      (fun N ↦ (∑ n ∈ Icc 1 N, a n / (n : K)) + ∑ n ∈ S, (b n - a n) / (n : K)) := by
    filter_upwards [eventually_sum_Icc_div_sub_eq_sum S hab] with N hN
    exact (sub_eq_iff_eq_add.mp hN).trans (add_comm _ _)
  exact (tendsto_congr' heq).trans (tendsto_add_const_iff _)

end Finset
