/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Attainment, coboundary characterization, and invariance for cross-degree pair costs

This file develops equal-degree rescaling, degree-`2` gauge invariance, attainment, and
non-coboundary lower bounds for cross-degree pair sums on `Finset (V × V)`:

* **Equal-degree `movedNorm` rescaling and upper bounds**
  (`Finset.mul_sum_distErr_mul_inv_eq_sum_movedNorm`,
  `Finset.mul_ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm`, and
  `Finset.ciInf₂_sum_distErr_mul_inv_le_ciInf_sum_movedNorm_div`): in equal degree `n`,
  multiplying the cross-degree cost (or its gauge infimum) by `n` recovers the `movedNorm (Fin n)`
  gauge cost, so for `2 ≤ n` the cross-degree gauge infimum over `m + 2 ≥ 2` is at most `1 / n`
  times the equal-degree `movedNorm` gauge infimum.
* **Global gauge invariance in degree `2`** (`Finset.ciInf₂_sum_distErr_inv_mul_mul_two`):
  transforming a degree-`2` assignment by a degree-`2` vertex gauge preserves the global
  cross-degree infimum over all `m + 2 ≥ 2`.
* **Attainment across infinitely many gauge degrees** (`Finset.exists_eq_ciInf_sum_distErr_mul_inv`
  and `Finset.exists_eq_ciInf₂_sum_distErr_mul_inv`): on any finite edge set `E : Finset (V × V)`
  over an arbitrary (possibly infinite) vertex type `V`, both the fixed-degree infimum and the
  two-parameter infimum over all degrees `m + 2 ≥ 2` are attained.
* **Uniform `1 / (n + 1)` non-coboundary gap and coboundary characterization**
  (`Finset.one_div_add_one_le_sum_distErr_mul_inv_of_not_exists` and
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_zero_iff`): if `α` is not a coboundary on `E`, every gauge
  of every degree `m : ℕ` incurs cost at least `1 / (n + 1)`; hence for `2 ≤ n`, the cross-degree
  infimum vanishes if and only if `α` is an equal-degree coboundary on `E`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2,
  equations (2.8)–(2.9) and the display after (2.9), pp. 6–7.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Zenodo, doi:10.5281/zenodo.23245792, Section 2 and Proposition 10.
-/

public section

open Finset

namespace Finset

open Equiv Equiv.Perm TauCeti

variable {V : Type*} {n m : ℕ}

/-! ### Nonnegativity and bounded-below helpers for cross-degree pair costs -/

theorem sum_distErr_mul_inv_nonneg (E : Finset (V × V)) (α : V → V → Perm (Fin n))
    (β : V → Perm (Fin m)) :
    0 ≤ ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  sum_nonneg fun _ _ => distErr_nonneg _ _

theorem bddBelow_range_sum_distErr_mul_inv (E : Finset (V × V)) (α : V → V → Perm (Fin n))
    (m : ℕ) :
    BddBelow (Set.range fun β : V → Perm (Fin m) =>
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) :=
  ⟨0, Set.forall_mem_range.mpr (E.sum_distErr_mul_inv_nonneg α)⟩

theorem ciInf_sum_distErr_mul_inv_nonneg (E : Finset (V × V)) (α : V → V → Perm (Fin n))
    (m : ℕ) :
    0 ≤ ⨅ β : V → Perm (Fin m), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  Real.iInf_nonneg (E.sum_distErr_mul_inv_nonneg α)

theorem bddBelow_range_ciInf_sum_distErr_mul_inv (E : Finset (V × V)) (α : V → V → Perm (Fin n)) :
    BddBelow (Set.range fun m : ℕ =>
      ⨅ β : V → Perm (Fin (m + 2)), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) :=
  ⟨0, Set.forall_mem_range.mpr fun m => E.ciInf_sum_distErr_mul_inv_nonneg α (m + 2)⟩

theorem ciInf₂_sum_distErr_mul_inv_nonneg (E : Finset (V × V)) (α : V → V → Perm (Fin n)) :
    0 ≤ ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  Real.iInf_nonneg fun m => E.ciInf_sum_distErr_mul_inv_nonneg α (m + 2)

/-! ### Equal-degree moved-norm normalization and upper bounds -/

/-- Multiplying the equal-degree cross-degree pair cost over `E` by the degree `n` recovers the
`movedNorm (Fin n)` gauge cost, for every `n : ℕ` including `n = 0`. -/
theorem mul_sum_distErr_mul_inv_eq_sum_movedNorm (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (β : V → Perm (Fin n)) :
    (n : ℝ) * (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2) := by
  rw [mul_sum]
  exact sum_congr rfl fun e _ => mul_distErr_mul_inv_eq_movedNorm (α e.1 e.2) (β e.1) (β e.2)

/-- In equal nonzero degree `n`, the cross-degree pair cost over `E` equals the `movedNorm (Fin n)`
gauge cost divided by `n`. -/
theorem sum_distErr_mul_inv_eq_sum_movedNorm_div [NeZero n] (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (β : V → Perm (Fin n)) :
    (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, E.mul_sum_distErr_mul_inv_eq_sum_movedNorm]

/-- Multiplying the equal-degree cross-degree gauge-cost infimum over `E` by `n` recovers the
`movedNorm (Fin n)` gauge-cost infimum, for every `n : ℕ`. -/
theorem mul_ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) :
    (n : ℝ) * (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      ⨅ β : V → Perm (Fin n), ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2) := by
  rw [Real.mul_iInf_of_nonneg (Nat.cast_nonneg n)]
  exact iInf_congr (E.mul_sum_distErr_mul_inv_eq_sum_movedNorm α)

/-- In equal nonzero degree `n`, the cross-degree gauge-cost infimum equals the `movedNorm (Fin n)`
gauge-cost infimum divided by `n`. -/
theorem ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div [NeZero n] (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) :
    (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (⨅ β : V → Perm (Fin n), ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, E.mul_ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm]

/-- When `2 ≤ n`, restricting gauges to equal degree `n` bounds the global cross-degree gauge-cost
infimum over `m + 2 ≥ 2` above by the equal-degree `distErr` infimum. -/
theorem ciInf₂_sum_distErr_mul_inv_le_ciInf_of_le (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      ⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rcases Nat.exists_eq_add_of_le' hn with ⟨k, rfl⟩
  exact ciInf_le (E.bddBelow_range_ciInf_sum_distErr_mul_inv α) k

/-- When `2 ≤ n`, the global cross-degree gauge-cost infimum over `m + 2 ≥ 2` is at most `1 / n`
times the equal-degree `movedNorm (Fin n)` gauge-cost infimum. -/
theorem ciInf₂_sum_distErr_mul_inv_le_ciInf_sum_movedNorm_div (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (⨅ β : V → Perm (Fin n),
        ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / n := by
  have : NeZero n := ⟨by omega⟩
  exact (E.ciInf₂_sum_distErr_mul_inv_le_ciInf_of_le α hn).trans_eq
    (E.ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div α)

/-- Transforming a degree-`2` edge assignment by a degree-`2` vertex gauge `γ` preserves the global
cross-degree gauge-cost infimum over all gauge degrees `m + 2 ≥ 2`. -/
theorem ciInf₂_sum_distErr_inv_mul_mul_two (E : Finset (V × V))
    (α : V → V → Perm (Fin 2)) (γ : V → Perm (Fin 2)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr ((γ e.1)⁻¹ * α e.1 e.2 * γ e.2) (β e.1 * (β e.2)⁻¹)) =
      ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  iInf_congr fun m => E.ciInf_sum_distErr_inv_mul_mul_of_le α γ (Nat.le_add_left 2 m)

/-! ### Attainment and non-coboundary lower bounds -/

/-- On any finite edge set `E` over an arbitrary vertex type `V`, the fixed-degree cross-degree
pair-cost infimum over `β : V → Perm (Fin m)` is attained. -/
theorem exists_eq_ciInf_sum_distErr_mul_inv (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (m : ℕ) :
    ∃ β : V → Perm (Fin m),
      (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
        ⨅ β' : V → Perm (Fin m), ∑ e ∈ E, distErr (α e.1 e.2) (β' e.1 * (β' e.2)⁻¹) := by
  let f (β : V → Perm (Fin m)) : ℝ := ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  let S : Finset ℝ := (Iic (#E * min n m)).image fun a : ℕ => (#E : ℝ) - (a : ℝ) / max n m
  have hsub : Set.range f ⊆ (S : Set ℝ) := by
    rintro _ ⟨β, rfl⟩
    rw [mem_coe, mem_image]
    refine ⟨∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹), mem_Iic.mpr ?_,
      (E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹)).symm⟩
    simpa [sum_const, smul_eq_mul] using
      sum_le_sum fun e (_ : e ∈ E) => agreeCount_le_min (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  obtain ⟨β, hβ⟩ := (Set.range_nonempty f).csInf_mem (S.finite_toSet.subset hsub)
  exact ⟨β, hβ⟩

/-- Degree-cutoff helper: because total agreements are at most `#E * n` while `max n (m + 2)` grows
with `m`, there is a finite degree bound `M` below which every cross-degree pair cost can be matched
or improved. -/
private theorem exists_cutoff_sum_distErr_mul_inv (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) :
    ∃ M : ℕ, ∀ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∃ (m₀ : ℕ) (β₀ : V → Perm (Fin (m₀ + 2))), m₀ ≤ M ∧
        (∑ e ∈ E, distErr (α e.1 e.2) (β₀ e.1 * (β₀ e.2)⁻¹)) ≤
          ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  let A (m : ℕ) (β : V → Perm (Fin (m + 2))) : ℕ :=
    ∑ e ∈ E, agreeCount (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  have hA_le (m : ℕ) (β : V → Perm (Fin (m + 2))) : A m β ≤ #E * n := by
    simpa [A, sum_const, smul_eq_mul] using sum_le_sum fun e (_ : e ∈ E) =>
      (agreeCount_le_min (α e.1 e.2) (β e.1 * (β e.2)⁻¹)).trans (min_le_left n (m + 2))
  by_cases hpos : ∃ (m₁ : ℕ) (β₁ : V → Perm (Fin (m₁ + 2))), 1 ≤ A m₁ β₁
  · rcases hpos with ⟨m₁, β₁, hA₁⟩
    refine ⟨#E * n * max n (m₁ + 2), fun m β => ?_⟩
    by_cases hm : m ≤ #E * n * max n (m₁ + 2)
    · exact ⟨m, β, hm, le_rfl⟩
    · have hm₁ : m₁ ≤ #E * n * max n (m₁ + 2) := by
        have hEn : 1 ≤ #E * n := hA₁.trans (hA_le m₁ β₁)
        have hlt : m₁ ≤ max n (m₁ + 2) := (Nat.le_add_right m₁ 2).trans (le_max_right n (m₁ + 2))
        exact hlt.trans (by simpa using Nat.mul_le_mul_right (max n (m₁ + 2)) hEn)
      refine ⟨m₁, β₁, hm₁, ?_⟩
      rw [E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β₁ e.1 * (β₁ e.2)⁻¹),
        E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹)]
      refine sub_le_sub_left ?_ _
      have hd₁ : (0 : ℝ) < max n (m₁ + 2) := by positivity
      have hd : (0 : ℝ) < max n (m + 2) := by positivity
      rw [div_le_div_iff₀ hd hd₁]
      have hmul : A m β * max n (m₁ + 2) ≤ A m₁ β₁ * max n (m + 2) := by
        calc A m β * max n (m₁ + 2)
            ≤ (#E * n) * max n (m₁ + 2) := Nat.mul_le_mul_right _ (hA_le m β)
          _ ≤ m := by omega
          _ ≤ 1 * max n (m + 2) := by
              rw [one_mul]
              exact (Nat.le_add_right m 2).trans (le_max_right n (m + 2))
          _ ≤ A m₁ β₁ * max n (m + 2) := Nat.mul_le_mul_right _ hA₁
      exact_mod_cast hmul
  · refine ⟨0, fun m β => ⟨0, 1, le_rfl, ?_⟩⟩
    push Not at hpos
    have h0 : A 0 1 = 0 := Nat.lt_one_iff.mp (hpos 0 1)
    have hm : A m β = 0 := Nat.lt_one_iff.mp (hpos m β)
    dsimp only [A] at h0 hm
    rw [E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => (1 : V → Perm (Fin 2)) e.1 *
        ((1 : V → Perm (Fin 2)) e.2)⁻¹),
      E.sum_distErr_eq_card_sub_div (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹), h0, hm]
    simp

/-- On any finite edge set `E` over an arbitrary vertex type `V`, the cross-degree gauge-cost
infimum over all gauge degrees `m + 2 ≥ 2` and all gauges `β : V → Perm (Fin (m + 2))` is attained.
-/
theorem exists_eq_ciInf₂_sum_distErr_mul_inv (E : Finset (V × V)) (α : V → V → Perm (Fin n)) :
    ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
        ⨅ (m' : ℕ) (β' : V → Perm (Fin (m' + 2))),
          ∑ e ∈ E, distErr (α e.1 e.2) (β' e.1 * (β' e.2)⁻¹) := by
  obtain ⟨M, hM⟩ := exists_cutoff_sum_distErr_mul_inv E α
  let g (m : ℕ) : ℝ :=
    ⨅ β : V → Perm (Fin (m + 2)), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  have hS_ne : ((Iic M).image g).Nonempty := ⟨g 0, mem_image_of_mem g (mem_Iic.mpr (Nat.zero_le M))⟩
  obtain ⟨m₀, -, hm₀_eq⟩ := mem_image.mp (min'_mem ((Iic M).image g) hS_ne)
  obtain ⟨β₀, hβ₀⟩ := E.exists_eq_ciInf_sum_distErr_mul_inv α (m₀ + 2)
  refine ⟨m₀, β₀, le_antisymm ?_ ?_⟩
  · refine le_ciInf fun m => le_ciInf fun β => ?_
    obtain ⟨m₁, β₁, hm₁M, hle⟩ := hM m β
    have hmin : g m₀ ≤ g m₁ := hm₀_eq ▸ min'_le _ _ (mem_image_of_mem g (mem_Iic.mpr hm₁M))
    exact (hβ₀.trans_le (hmin.trans
      (ciInf_le (E.bddBelow_range_sum_distErr_mul_inv α (m₁ + 2)) β₁))).trans hle
  · exact (ciInf_le (E.bddBelow_range_ciInf_sum_distErr_mul_inv α) m₀).trans_eq hβ₀.symm

/-- If `α : V → V → Perm (Fin n)` is not an equal-degree coboundary on `E`, then every vertex gauge
`β : V → Perm (Fin m)` of every degree `m : ℕ` has cross-degree pair cost at least `1 / (n + 1)`. -/
theorem one_div_add_one_le_sum_distErr_mul_inv_of_not_exists (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (β : V → Perm (Fin m))
    (hncob : ¬ ∃ γ : V → Perm (Fin n), ∀ e ∈ E, α e.1 e.2 = γ e.1 * (γ e.2)⁻¹) :
    1 / ((n : ℝ) + 1) ≤ ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rcases eq_or_ne n m with rfl | hnm
  · have hex : ∃ e ∈ E, α e.1 e.2 ≠ β e.1 * (β e.2)⁻¹ := by
      by_contra hall
      push Not at hall
      exact hncob ⟨β, hall⟩
    rcases hex with ⟨e₀, he₀, hne⟩
    have hq_ne : (β e₀.1)⁻¹ * α e₀.1 e₀.2 * β e₀.2 ≠ 1 := by
      intro h1
      apply hne
      calc α e₀.1 e₀.2
          = β e₀.1 * ((β e₀.1)⁻¹ * α e₀.1 e₀.2 * β e₀.2) * (β e₀.2)⁻¹ := by group
        _ = β e₀.1 * (β e₀.2)⁻¹ := by rw [h1, mul_one]
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hq_ne (Subsingleton.elim _ _)
    have : NeZero n := ⟨hn0⟩
    have h2 : (2 : ℝ) ≤ movedNorm (Fin n) ((β e₀.1)⁻¹ * α e₀.1 e₀.2 * β e₀.2) :=
      two_le_movedNorm_of_ne_one hq_ne
    have he₀_le : 1 / ((n : ℝ) + 1) ≤ distErr (α e₀.1 e₀.2) (β e₀.1 * (β e₀.2)⁻¹) := by
      rw [distErr_mul_inv_eq_movedNorm_div]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      rw [div_le_div_iff₀ (by positivity) hn_pos]
      nlinarith
    exact he₀_le.trans
      (single_le_sum (f := fun e => distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹))
        (fun _ _ => distErr_nonneg _ _) he₀)
  · have hE : E.Nonempty := by
      rw [← ne_empty_iff_nonempty]
      rintro rfl
      exact hncob ⟨1, by simp⟩
    rcases hE with ⟨e₀, he₀⟩
    exact (one_div_add_one_le_distErr_of_ne (α e₀.1 e₀.2) (β e₀.1 * (β e₀.2)⁻¹) hnm).trans
      (single_le_sum (f := fun e => distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹))
        (fun _ _ => distErr_nonneg _ _) he₀)

/-- If `α : V → V → Perm (Fin n)` is not an equal-degree coboundary on `E`, then its cross-degree
gauge-cost infimum over all degrees `m + 2 ≥ 2` is at least `1 / (n + 1)`. -/
theorem one_div_add_one_le_ciInf₂_sum_distErr_mul_inv_of_not_exists (E : Finset (V × V))
    (α : V → V → Perm (Fin n))
    (hncob : ¬ ∃ γ : V → Perm (Fin n), ∀ e ∈ E, α e.1 e.2 = γ e.1 * (γ e.2)⁻¹) :
    1 / ((n : ℝ) + 1) ≤
      ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  le_ciInf fun _ => le_ciInf fun β =>
    E.one_div_add_one_le_sum_distErr_mul_inv_of_not_exists α β hncob

/-- For `2 ≤ n`, the cross-degree gauge-cost infimum over all gauge degrees `m + 2 ≥ 2` vanishes if
and only if `α` is an equal-degree coboundary on `E`. The hypothesis `2 ≤ n` is sharp: for `n ≤ 1`,
every assignment is a coboundary, whereas on any nonempty `E` every gauge of degree `m + 2 ≥ 2` has
strictly positive distance with errors. -/
theorem ciInf₂_sum_distErr_mul_inv_eq_zero_iff (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 0 ↔
      ∃ β : V → Perm (Fin n), ∀ e ∈ E, α e.1 e.2 = β e.1 * (β e.2)⁻¹ := by
  constructor
  · intro h0
    by_contra hncob
    have hgap := E.one_div_add_one_le_ciInf₂_sum_distErr_mul_inv_of_not_exists α hncob
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · rintro ⟨β, hβ⟩
    have : NeZero n := ⟨by omega⟩
    have hle := E.ciInf₂_sum_distErr_mul_inv_le_ciInf_of_le α hn
    have hβ0 : (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 0 :=
      sum_eq_zero fun e he => by rw [hβ e he, distErr_self]
    exact le_antisymm
      (hle.trans ((ciInf_le (E.bddBelow_range_sum_distErr_mul_inv α n) β).trans_eq hβ0))
      (E.ciInf₂_sum_distErr_mul_inv_nonneg α)

/-- For `2 ≤ n`, the cross-degree gauge-cost infimum over all gauge degrees `m + 2 ≥ 2` is strictly
positive if and only if `α` is not an equal-degree coboundary on `E`. -/
theorem ciInf₂_sum_distErr_mul_inv_pos_iff (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n) :
    0 < (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ↔
      ¬ ∃ β : V → Perm (Fin n), ∀ e ∈ E, α e.1 e.2 = β e.1 * (β e.2)⁻¹ := by
  rw [lt_iff_le_and_ne, and_iff_right (E.ciInf₂_sum_distErr_mul_inv_nonneg α), ne_comm]
  exact not_iff_not.mpr (E.ciInf₂_sum_distErr_mul_inv_eq_zero_iff α hn)

end Finset

end
