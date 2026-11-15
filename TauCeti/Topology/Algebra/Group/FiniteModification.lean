/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Finite changes of ordered sums

For sequences in an additive commutative group agreeing outside a finite set at positive
indices, `Finset.sum_Icc_sub_eq_sum` gives the exact difference of their ordered partial
sums once the cutoff contains every changed index. The correction omits index `0`.
`Finset.tendsto_sum_Icc_congr_finset_iff` transports convergence in both directions,
assuming only separate continuity of addition.

These are the finite-sum prerequisites for the finite coefficient corrections in
`TauCeti.NumberTheory.LSeries.BoundaryConvergence.FiniteModification`.
-/

public section

open Filter
open scoped Topology

namespace Finset

variable {G : Type*} [AddCommGroup G] {a b : ℕ → G} {L : G}

/-- Once the cutoff contains every positive changed index, the difference of the ordered
partial sums is exactly the finite correction, omitting index `0`. -/
theorem sum_Icc_sub_eq_sum (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) {N : ℕ} (hN : S.sup id ≤ N) :
    (∑ n ∈ Icc 1 N, b n) - (∑ n ∈ Icc 1 N, a n) =
      ∑ n ∈ S.erase 0, (b n - a n) := by
  classical
  have hsub : S.erase 0 ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hn0, hnS⟩ := mem_erase.mp hn
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0,
      (le_sup (f := id) hnS).trans hN⟩
  rw [← sum_sub_distrib]
  apply (sum_subset hsub _).symm
  intro n hn hnS
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (mem_Icc.mp hn).1
  have : n ∉ S := fun h ↦ hnS (mem_erase.mpr ⟨hn0, h⟩)
  simp [hab n hn0 this]

/-- Finite changes preserve convergence of ordered partial sums, with the explicit finite
correction to the limit. No agreement at index `0` is required. -/
theorem tendsto_sum_Icc_congr_finset_iff [TopologicalSpace G]
    [SeparatelyContinuousAdd G] (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, b n) atTop
        (𝓝 (L + ∑ n ∈ S.erase 0, (b n - a n))) ↔
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n) atTop (𝓝 L) := by
  have heq : (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, b n) =ᶠ[atTop]
      (fun N ↦ (∑ n ∈ Icc 1 N, a n) + ∑ n ∈ S.erase 0, (b n - a n)) := by
    filter_upwards [eventually_ge_atTop (S.sup id)] with N hN
    exact (sub_eq_iff_eq_add.mp (sum_Icc_sub_eq_sum S hab hN)).trans (add_comm _ _)
  exact (tendsto_congr' heq).trans (tendsto_add_const_iff _)

end Finset
