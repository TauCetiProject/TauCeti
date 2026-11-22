/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Attainment, invariance, cross-degree cochain distance, and `h1Err`

This file develops attainment, coboundary vanishing, and invariance for cross-degree pair costs on
`Finset (V × V)` and introduces the Chapman–Lubotzky cross-degree cochain distance
(`Cochain.costErr`, `Cochain.gaugeDistErr`) and Cheeger constant (`TauCeti.h1Err`):

* **Equal-degree moved-norm rescaling and upper bounds**
  (`Finset.mul_sum_distErr_mul_inv_eq_sum_movedNorm`,
  `Finset.mul_ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm`,
  `Finset.ciInf₂_sum_distErr_mul_inv_le_ciInf_sum_movedNorm_div`, and
  `Cochain.gaugeDistErr_le_gaugeDist_div`): in equal degree `n`, multiplying the cross-degree cost
  (or its gauge infimum) by `n` recovers the `movedNorm (Fin n)` gauge cost, so for `2 ≤ n` the
  cross-degree gauge infimum over `m + 2 ≥ 2` is at most `1 / n` times the equal-degree
  `movedNorm` gauge infimum.
* **Global gauge invariance in degree `2`** (`Finset.ciInf₂_sum_distErr_inv_mul_mul_two` and
  `Cochain.gaugeDistErr_smul`): transforming a degree-`2` assignment by a degree-`2` vertex gauge
  preserves the global cross-degree infimum over all `m + 2 ≥ 2`.
* **Attainment across infinitely many gauge degrees** (`Finset.exists_eq_ciInf_sum_distErr_mul_inv`,
  `Finset.exists_eq_ciInf₂_sum_distErr_mul_inv`, and `Cochain.exists_costErr_eq_gaugeDistErr`): on
  any finite edge set `E : Finset (V × V)` over an arbitrary (possibly infinite) vertex type `V`,
  both the fixed-degree infimum and the two-parameter infimum over all degrees `m + 2 ≥ 2` are
  attained. Indeed, the total agreement count lies in `{0, …, #E * n}` while `max n (m + 2)` grows
  without bound, so large gauge degrees cannot improve on any configuration with at least one
  agreement.
* **Uniform `1 / (n + 1)` non-coboundary gap and coboundary characterization**
  (`Finset.one_div_add_one_le_sum_distErr_mul_inv_of_not_exists`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_zero_iff`,
  `Cochain.one_div_add_one_le_gaugeDistErr_of_not_isCoboundary`, and
  `Cochain.gaugeDistErr_eq_zero_iff_isCoboundary`): if `α` is not a coboundary, every gauge of
  every degree `m : ℕ` incurs cost at least `1 / (n + 1)`; hence for `2 ≤ n`, the cross-degree
  infimum vanishes if and only if `α` is an equal-degree coboundary.
* **Cochain unoriented edge sums, order independence, relabelling invariance, and `h1Err`**
  (`Cochain.costErr_eq_sum_edges`, `Cochain.gaugeDistErr_congr_linearOrder`,
  `Cochain.gaugeDistErr_relabel`, `Cochain.gaugeDistErr_relabelComplete`, and `TauCeti.h1Err`):
  reversing an edge inverts its permutation label without changing `distErr`, so `Cochain.costErr`,
  `Cochain.gaugeDistErr`, and `TauCeti.h1Err` are independent of the chosen linear order on `V` and
  invariant under arbitrary bijections `V ≃ W`.

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
pair-cost infimum over `β : V → Perm (Fin m)` is attained, because the total agreement count across
`E` takes finitely many values in `{0, …, #E * min n m}`. -/
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

/-! ### Cross-degree cochain distance `costErr`, `gaugeDistErr`, and `h1Err` -/

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

namespace Cochain

section CrossDegree

variable {V W : Type*} {n m : ℕ}

/-- The cross-degree cost of a gauge `β` of degree `m` against a cochain `α` of degree `n`: the
distance with errors from `α u v` to `β u * (β v)⁻¹`, summed over edges `u < v`. -/
noncomputable def costErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)

theorem costErr_def [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := (rfl)

/-- On the complete complex, `costErr` sums `distErr (α u v) (β u * (β v)⁻¹)` over all strictly
increasing vertex pairs `u < v`. -/
theorem costErr_complete [Fintype V] [LinearOrder V]
    (α : Cochain (complete V) (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_def]
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_edges_complete, card_pair_eq_two_iff,
    and_iff_left_iff_imp]
  exact LT.lt.ne

theorem costErr_nonneg [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    0 ≤ α.costErr β :=
  sum_nonneg fun _ _ => distErr_nonneg _ _

theorem bddBelow_range_costErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    BddBelow (Set.range (α.costErr (m := m))) :=
  ⟨0, Set.forall_mem_range.mpr (α.costErr_nonneg)⟩

theorem ciInf_costErr_nonneg [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    0 ≤ ⨅ β : V → Perm (Fin m), α.costErr β :=
  Real.iInf_nonneg α.costErr_nonneg

theorem bddBelow_range_ciInf_costErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun m : ℕ => ⨅ β : V → Perm (Fin (m + 2)), α.costErr β) :=
  ⟨0, Set.forall_mem_range.mpr fun m => α.ciInf_costErr_nonneg (m + 2)⟩

@[simp] theorem costErr_one_one [Fintype V] [LinearOrder V] [NeZero n] {X : TwoComplex V} :
    (1 : Cochain X (Perm (Fin n))).costErr (1 : V → Perm (Fin n)) = 0 := by
  simp [costErr_def]

/-- In equal degree `n`, multiplying `costErr` by `n` recovers `cost` with respect to
`Equiv.Perm.movedNorm (Fin n)`, for every `n : ℕ`. -/
theorem mul_costErr_eq_cost [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    (n : ℝ) * α.costErr β = α.cost (movedNorm (Fin n)) β := by
  rw [costErr_def, cost_def, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [mul_distErr_mul_inv_eq_movedNorm, movedNorm_apply]

/-- In equal nonzero degree `n`, `costErr` equals `cost` with respect to `movedNorm (Fin n)`
divided by `n`. -/
theorem costErr_eq_cost_div [Fintype V] [LinearOrder V] [NeZero n] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = α.cost (movedNorm (Fin n)) β / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_costErr_eq_cost β]

/-- In equal degree `n`, multiplying the `costErr` gauge infimum by `n` recovers
`gaugeDist (movedNorm (Fin n))`. -/
theorem mul_ciInf_costErr_eq_gaugeDist [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (n : ℝ) * (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) := by
  rw [Real.mul_iInf_of_nonneg (Nat.cast_nonneg n), gaugeDist_def]
  exact iInf_congr (α.mul_costErr_eq_cost)

/-- In equal nonzero degree `n`, the `costErr` gauge infimum equals `gaugeDist (movedNorm (Fin n))`
divided by `n`. -/
theorem ciInf_costErr_eq_gaugeDist_div [Fintype V] [LinearOrder V] [NeZero n] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_ciInf_costErr_eq_gaugeDist]

/-- Reversing a vertex pair inverts both `α u v` and the gauge quotient `β u * (β v)⁻¹`, leaving
the edge term `distErr` unchanged. -/
theorem distErr_apply_mul_inv_swap {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) (u v : V) :
    distErr (α v u) (β v * (β u)⁻¹) = distErr (α u v) (β u * (β v)⁻¹) := by
  rw [α.apply_swap u v, distErr_inv_mul_inv]

/-- The cross-degree gauge cost contribution of an unoriented edge `e`, or `0` if `e ∉ X.edges`. -/
noncomputable def edgeCostErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) (e : Finset V) : ℝ := by
  classical
  exact if he : e ∈ X.edges then
    distErr
      (α (X.exists_vertices_of_mem_edges he).choose
        (X.exists_vertices_of_mem_edges he).choose_spec.choose)
      (β (X.exists_vertices_of_mem_edges he).choose *
        (β (X.exists_vertices_of_mem_edges he).choose_spec.choose)⁻¹)
  else 0

/-- Evaluating `edgeCostErr` on any edge `e ∈ X.edges` via its two distinct endpoints. -/
theorem edgeCostErr_of_mem_edges {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) {e : Finset V} (he : e ∈ X.edges) {u v : V} (huv : u ≠ v)
    (hu : u ∈ e) (hv : v ∈ e) :
    α.edgeCostErr β e = distErr (α u v) (β u * (β v)⁻¹) := by
  classical
  simp only [edgeCostErr, he, ↓reduceDIte]
  obtain ⟨hu'v', hu', hv'⟩ := (X.exists_vertices_of_mem_edges he).choose_spec.choose_spec
  have he₁ :
      ({(X.exists_vertices_of_mem_edges he).choose,
        (X.exists_vertices_of_mem_edges he).choose_spec.choose} : Finset V) = e :=
    eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hu', singleton_subset_iff.mpr hv'⟩)
      (by rw [X.edge_card e he, card_pair hu'v'])
  have he₂ : ({u, v} : Finset V) = e :=
    eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv])
      (by rw [X.edge_card e he, card_pair huv])
  have hpair := he₁.trans he₂.symm
  rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
  rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₂, h₁]
  · rw [h₂, h₁]; exact α.distErr_apply_mul_inv_swap β u v

/-- Evaluating `edgeCostErr` directly on a pair `{u, v} ∈ X.edges`. -/
@[simp, grind =] theorem edgeCostErr_pair [DecidableEq V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) {u v : V}
    (he : ({u, v} : Finset V) ∈ X.edges) :
    α.edgeCostErr β {u, v} = distErr (α u v) (β u * (β v)⁻¹) :=
  α.edgeCostErr_of_mem_edges β he ((X.adj_iff_pair_mem_edges u v).mpr he).ne (by simp) (by simp)

@[simp] theorem edgeCostErr_of_notMem_edges {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) {e : Finset V} (he : e ∉ X.edges) : α.edgeCostErr β e = 0 := by
  classical simp [edgeCostErr, he]

theorem edgeCostErr_nonneg {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) (e : Finset V) : 0 ≤ α.edgeCostErr β e := by
  classical
  by_cases he : e ∈ X.edges <;> simp [edgeCostErr, he, distErr_nonneg]

/-- `costErr` equals the sum of `edgeCostErr` over the unoriented edges `X.edges`. -/
theorem costErr_eq_sum_edges [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β = ∑ e ∈ X.edges, α.edgeCostErr β e := by
  rw [costErr_def]
  refine sum_bij (fun p _ => ({p.1, p.2} : Finset V)) (fun p hp => (mem_filter.mp hp).2.2) ?_ ?_
    (fun p hp => (α.edgeCostErr_pair β (mem_filter.mp hp).2.2).symm)
  · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ hpair
    have hlt₁ : u₁ < v₁ := (mem_filter.mp hp₁).2.1
    have hlt₂ : u₂ < v₂ := (mem_filter.mp hp₂).2.1
    rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (lt_asymm hlt₁ hlt₂).elim
  · intro e he
    obtain ⟨u, v, hlt, hset⟩ := X.exists_increasing_of_mem_edges he
    exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, hlt, hset ▸ he⟩, hset⟩

/-- `costErr` does not depend on the `LinearOrder` chosen on `V`. -/
theorem costErr_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    @costErr V n m _ l₁ X α β = @costErr V n m _ l₂ X α β :=
  (@costErr_eq_sum_edges V n m _ l₁ X α β).trans (@costErr_eq_sum_edges V n m _ l₂ X α β).symm

@[simp] theorem edgeCostErr_relabel {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) (s : Finset W) :
    (α.relabel e).edgeCostErr γ s = α.edgeCostErr (γ ∘ e) (s.map e.symm.toEmbedding) := by
  by_cases hs : s ∈ (X.relabel e).edges
  · obtain ⟨u, v, huv, hu, hv⟩ := (X.relabel e).exists_vertices_of_mem_edges hs
    rw [(α.relabel e).edgeCostErr_of_mem_edges γ hs huv hu hv,
      α.edgeCostErr_of_mem_edges (γ ∘ e) ((X.mem_edges_relabel e s).mp hs)
        (e.symm.injective.ne huv) (mem_map_of_mem _ hu) (mem_map_of_mem _ hv)]
    simp
  · rw [edgeCostErr_of_notMem_edges _ _ hs,
      edgeCostErr_of_notMem_edges _ _ (mt (X.mem_edges_relabel e s).mpr hs)]

@[simp 1100] theorem edgeCostErr_relabel_map {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) (s : Finset V) :
    (α.relabel e).edgeCostErr γ (s.map e.toEmbedding) = α.edgeCostErr (γ ∘ e) s := by
  rw [α.edgeCostErr_relabel γ e]
  congr 1; ext; simp

/-- Relabelling a cochain along `e : V ≃ W` pulls the gauge back along `e` in `costErr`. -/
@[simp] theorem costErr_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {X : TwoComplex V} (α : Cochain X (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabel e).costErr γ = α.costErr (γ ∘ e) := by
  rw [costErr_eq_sum_edges, costErr_eq_sum_edges, X.sum_edges_relabel e]
  exact sum_congr rfl fun s _ => α.edgeCostErr_relabel_map γ e s

private theorem congr_complex {γ : Sort*}
    (F : ∀ X : TwoComplex W, Cochain X (Perm (Fin n)) → γ)
    {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂)
    {α₁ : Cochain X₁ (Perm (Fin n))} {α₂ : Cochain X₂ (Perm (Fin n))}
    (hα : ∀ u v, α₁ u v = α₂ u v) : F X₁ α₁ = F X₂ α₂ := by
  subst hX; congr 1; exact Cochain.ext fun u v _ => hα u v

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` pulls the gauge back along `e` in
`costErr`. -/
@[simp] theorem costErr_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabelComplete e).costErr γ = α.costErr (γ ∘ e) :=
  (congr_complex (fun _ δ => δ.costErr γ) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.costErr_relabel γ e)

/-- Relabelling a cochain along `e : V ≃ W` preserves the degree-`m` `costErr` infimum. -/
theorem ciInf_costErr_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {X : TwoComplex V} (α : Cochain X (Perm (Fin n))) (e : V ≃ W) (m : ℕ) :
    (⨅ γ : W → Perm (Fin m), (α.relabel e).costErr γ) =
      ⨅ β : V → Perm (Fin m), α.costErr β :=
  (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin m)))).iInf_congr fun γ =>
    (α.costErr_relabel γ e).symm

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves the degree-`m` `costErr`
infimum. -/
theorem ciInf_costErr_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) (m : ℕ) :
    (⨅ γ : W → Perm (Fin m), (α.relabelComplete e).costErr γ) =
      ⨅ β : V → Perm (Fin m), α.costErr β :=
  (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin m)))).iInf_congr fun γ =>
    (α.costErr_relabelComplete γ e).symm

/-- The cross-degree gauge distance of `α`: the infimum of `costErr` over all gauges of all
degrees `m + 2 ≥ 2`. -/
noncomputable def gaugeDistErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) : ℝ :=
  ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β

theorem gaugeDistErr_def [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr = ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β := (rfl)

theorem gaugeDistErr_nonneg [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) : 0 ≤ α.gaugeDistErr :=
  Real.iInf_nonneg fun m => α.ciInf_costErr_nonneg (m + 2)

theorem gaugeDistErr_le_costErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) {m : ℕ} (β : V → Perm (Fin (m + 2))) :
    α.gaugeDistErr ≤ α.costErr β :=
  (ciInf_le α.bddBelow_range_ciInf_costErr m).trans
    (ciInf_le (α.bddBelow_range_costErr (m + 2)) β)

theorem gaugeDistErr_le_costErr_of_le [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hm : 2 ≤ m) (β : V → Perm (Fin m)) :
    α.gaugeDistErr ≤ α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact α.gaugeDistErr_le_costErr β

theorem gaugeDistErr_le_ciInf_costErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hm : 2 ≤ m) :
    α.gaugeDistErr ≤ ⨅ β : V → Perm (Fin m), α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact ciInf_le α.bddBelow_range_ciInf_costErr k

/-- When `2 ≤ n`, the cross-degree gauge distance is at most `1 / n` times the equal-degree
`movedNorm (Fin n)` gauge distance. -/
theorem gaugeDistErr_le_gaugeDist_div [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n)) / n := by
  have : NeZero n := ⟨by omega⟩
  exact (α.gaugeDistErr_le_ciInf_costErr hn).trans_eq α.ciInf_costErr_eq_gaugeDist_div

theorem le_gaugeDistErr_iff [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    c ≤ α.gaugeDistErr ↔ ∀ (m : ℕ) (β : V → Perm (Fin (m + 2))), c ≤ α.costErr β := by
  rw [gaugeDistErr_def]
  exact ⟨fun h m β => h.trans (α.gaugeDistErr_le_costErr β),
    fun h => le_ciInf fun m => le_ciInf fun β => h m β⟩

theorem gaugeDistErr_lt_iff [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    α.gaugeDistErr < c ↔ ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β < c := by
  rw [← not_le, le_gaugeDistErr_iff]
  push Not
  exact Iff.rfl

/-- When `n ≤ m`, the degree-`m` `costErr` infimum is invariant under the equal-degree gauge
action on `α`. -/
theorem ciInf_costErr_smul_of_le [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (γ : V → Perm (Fin n)) (α : Cochain X (Perm (Fin n))) (hnm : n ≤ m) :
    (⨅ β : V → Perm (Fin m), (γ • α).costErr β) = ⨅ β : V → Perm (Fin m), α.costErr β := by
  set E : Finset (V × V) :=
    univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges)
  have hL (β : V → Perm (Fin m)) :
      (γ • α).costErr β =
        ∑ p ∈ E, distErr ((γ p.1)⁻¹ * α p.1 p.2 * γ p.2) (β p.1 * (β p.2)⁻¹) := by
    rw [costErr_def]
    refine sum_congr rfl fun p hp => ?_
    rw [smul_apply_of_adj γ α ((X.adj_iff_pair_mem_edges p.1 p.2).mpr (mem_filter.mp hp).2.2)]
  simp_rw [hL, costErr_def]
  exact E.ciInf_sum_distErr_inv_mul_mul_of_le α γ hnm

/-- Transforming a degree-`2` cochain by a degree-`2` gauge preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_smul [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (γ : V → Perm (Fin 2)) (α : Cochain X (Perm (Fin 2))) :
    (γ • α).gaugeDistErr = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def]
  exact iInf_congr fun m => ciInf_costErr_smul_of_le γ α (Nat.le_add_left 2 m)

/-- `gaugeDistErr` does not depend on the `LinearOrder` chosen on `V`. -/
theorem gaugeDistErr_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    @gaugeDistErr V n _ l₁ X α = @gaugeDistErr V n _ l₂ X α := by
  rw [@gaugeDistErr_def V n _ l₁ X α, @gaugeDistErr_def V n _ l₂ X α]
  exact iInf_congr fun m => iInf_congr fun β => costErr_congr_linearOrder l₁ l₂ α β

/-- Relabelling a cochain along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {X : TwoComplex V} (α : Cochain X (Perm (Fin n))) (e : V ≃ W) :
    (α.relabel e).gaugeDistErr = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def]
  exact iInf_congr fun m => α.ciInf_costErr_relabel e (m + 2)

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabelComplete [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDistErr = α.gaugeDistErr :=
  (congr_complex (fun _ γ => γ.gaugeDistErr) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.gaugeDistErr_relabel e)

/-- The cross-degree gauge distance `gaugeDistErr` is always attained by some gauge of some degree
`m + 2 ≥ 2`. -/
theorem exists_costErr_eq_gaugeDistErr [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β = α.gaugeDistErr :=
  (univ.filter (fun p : V × V =>
    p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges)).exists_eq_ciInf₂_sum_distErr_mul_inv α

private theorem not_exists_eq_mul_inv_of_not_isCoboundary [Fintype V] [LinearOrder V]
    {X : TwoComplex V} {α : Cochain X (Perm (Fin n))} (hncob : ¬ α.IsCoboundary) :
    ¬ ∃ γ : V → Perm (Fin n),
      ∀ e ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        α e.1 e.2 = γ e.1 * (γ e.2)⁻¹ := by
  rintro ⟨γ, hγ⟩
  apply hncob
  rw [isCoboundary_def]
  refine ⟨γ, fun u v huv => ?_⟩
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · exact hγ (u, v) (mem_filter.mpr ⟨mem_univ _, hlt, (X.adj_iff_pair_mem_edges u v).mp huv⟩)
  · exact (huv.ne rfl).elim
  · have hvu := hγ (v, u)
      (mem_filter.mpr ⟨mem_univ _, hgt, (X.adj_iff_pair_mem_edges v u).mp huv.symm⟩)
    rw [α.apply_swap v u, hvu, mul_inv_rev, inv_inv]

/-- Every non-coboundary cochain of degree `n` incurs `costErr` at least `1 / (n + 1)` against any
gauge of any degree `m`. -/
theorem one_div_add_one_le_costErr_of_not_isCoboundary [Fintype V] [LinearOrder V]
    {X : TwoComplex V} {α : Cochain X (Perm (Fin n))} (hncob : ¬ α.IsCoboundary)
    (β : V → Perm (Fin m)) :
    1 / ((n : ℝ) + 1) ≤ α.costErr β := by
  have hnot := not_exists_eq_mul_inv_of_not_isCoboundary hncob
  exact Finset.one_div_add_one_le_sum_distErr_mul_inv_of_not_exists _ α β hnot

/-- Every non-coboundary cochain of degree `n` has `gaugeDistErr` at least `1 / (n + 1)`. -/
theorem one_div_add_one_le_gaugeDistErr_of_not_isCoboundary [Fintype V] [LinearOrder V]
    {X : TwoComplex V} {α : Cochain X (Perm (Fin n))} (hncob : ¬ α.IsCoboundary) :
    1 / ((n : ℝ) + 1) ≤ α.gaugeDistErr :=
  (α.le_gaugeDistErr_iff).mpr fun _ β =>
    one_div_add_one_le_costErr_of_not_isCoboundary hncob β

/-- For `2 ≤ n`, `α.gaugeDistErr = 0` if and only if `α` is an equal-degree coboundary. The
hypothesis `2 ≤ n` is sharp: for `n ≤ 1`, `(1 : Cochain X (Perm (Fin n)))` is a coboundary,
whereas on any complex with an edge every gauge of degree `m + 2 ≥ 2` has strictly positive
`costErr`. -/
theorem gaugeDistErr_eq_zero_iff_isCoboundary [Fintype V] [LinearOrder V] {X : TwoComplex V}
    {α : Cochain X (Perm (Fin n))} (hn : 2 ≤ n) :
    α.gaugeDistErr = 0 ↔ α.IsCoboundary :=
  (univ.filter (fun p : V × V =>
    p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges)).ciInf₂_sum_distErr_mul_inv_eq_zero_iff α hn
    |>.trans
    ⟨fun h => by
        by_contra hncob
        exact not_exists_eq_mul_inv_of_not_isCoboundary hncob h,
      fun h => by
        rw [isCoboundary_def] at h
        obtain ⟨γ, hγ⟩ := h
        exact ⟨γ, fun e he => hγ e.1 e.2 ((X.adj_iff_pair_mem_edges e.1 e.2).mpr
          (mem_filter.mp he).2.2)⟩⟩

/-- For `2 ≤ n`, `0 < α.gaugeDistErr` if and only if `α` is not an equal-degree coboundary. -/
theorem gaugeDistErr_pos_iff_not_isCoboundary [Fintype V] [LinearOrder V] {X : TwoComplex V}
    {α : Cochain X (Perm (Fin n))} (hn : 2 ≤ n) :
    0 < α.gaugeDistErr ↔ ¬ α.IsCoboundary := by
  rw [← gaugeDistErr_eq_zero_iff_isCoboundary hn]
  exact α.gaugeDistErr_nonneg.lt_iff_ne'

@[simp] theorem gaugeDistErr_one [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (hn : 2 ≤ n) : (1 : Cochain X (Perm (Fin n))).gaugeDistErr = 0 :=
  (gaugeDistErr_eq_zero_iff_isCoboundary hn).mpr isCoboundary_one

end CrossDegree

end Cochain

/-! ### The Chapman–Lubotzky cross-degree Cheeger constant `h1Err` -/

section CrossDegreeCheeger

variable {V W : Type*}

/-- On `complete V` with `3 ≤ Fintype.card V` and `2 ≤ n`, some degree-`n` cochain has strictly
positive cross-degree gauge distance. -/
theorem exists_gaugeDistErr_pos_complete [Fintype V] [LinearOrder V] (hV : 3 ≤ Fintype.card V)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ α : Cochain (complete V) (Perm (Fin n)), 0 < α.gaugeDistErr := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨α, hα⟩ := exists_not_isCoboundary_complete (V := V) (G := Perm (Fin (k + 2))) hV
  exact ⟨α, (α.gaugeDistErr_pos_iff_not_isCoboundary hn).mpr hα⟩

/-- The Chapman–Lubotzky cross-degree Cheeger constant of `X`: the infimum over all cochain degrees
`n + 2 ≥ 2` and all cochains `α` with `0 < α.gaugeDistErr` of
`(α.defect (movedNorm (Fin (n + 2))) / (n + 2)) / α.gaugeDistErr`. -/
noncomputable def h1Err [Fintype V] [LinearOrder V] (X : TwoComplex V) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
    r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr}

theorem h1Err_def [Fintype V] [LinearOrder V] (X : TwoComplex V) :
    h1Err X = sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} := (rfl)

section FixedOrder

variable [Fintype V] [LinearOrder V]

private theorem bddBelow_setOf_defect_div_gaugeDistErr (X : TwoComplex V) :
    BddBelow {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} :=
  ⟨0, by
    rintro r ⟨n, α, hα, rfl⟩
    exact div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le⟩

/-- The cross-degree Cheeger constant is nonnegative. -/
theorem h1Err_nonneg (X : TwoComplex V) : 0 ≤ h1Err X :=
  Real.sInf_nonneg fun _ ⟨_, α, hα, hr⟩ =>
    hr ▸ div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le

/-- Every cochain of degree `n + 2 ≥ 2` at positive `gaugeDistErr` gives an upper bound on
`h1Err X`. -/
theorem h1Err_le_div {X : TwoComplex V} {n : ℕ} {α : Cochain X (Perm (Fin (n + 2)))}
    (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr :=
  csInf_le (bddBelow_setOf_defect_div_gaugeDistErr X) ⟨n, α, hα, rfl⟩

/-- When some cochain of degree `n + 2 ≥ 2` has positive `gaugeDistErr`, `c ≤ h1Err X` holds iff
`c` bounds every cross-degree expansion ratio from below. -/
theorem le_h1Err_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    c ≤ h1Err X ↔
      ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
        c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, le_csInf_iff (bddBelow_setOf_defect_div_gaugeDistErr X)
    ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun h n α hα => h _ ⟨n, α, hα, rfl⟩, fun h _ ⟨n, α, hα, hr⟩ => hr ▸ h n α hα⟩

/-- When some cochain of degree `n + 2 ≥ 2` has positive `gaugeDistErr`, `h1Err X < c` holds iff
some admissible cochain has cross-degree expansion ratio strictly below `c`. -/
theorem h1Err_lt_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    h1Err X < c ↔
      ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
        α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr < c := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, csInf_lt_iff (bddBelow_setOf_defect_div_gaugeDistErr X)
    ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun ⟨_, ⟨n, α, hα, hr⟩, hlt⟩ => ⟨n, α, hα, hr ▸ hlt⟩,
    fun ⟨n, α, hα, hlt⟩ => ⟨_, ⟨n, α, hα, rfl⟩, hlt⟩⟩

/-- Lower-bound criterion for `h1Err X` in the presence of a cochain at positive `gaugeDistErr`. -/
theorem le_h1Err_of_forall {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ}
    (hc : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
      c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr) :
    c ≤ h1Err X :=
  (le_h1Err_iff hne).mpr hc

end FixedOrder

/-- `h1Err X` does not depend on the `LinearOrder` chosen on `V`. -/
theorem h1Err_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (X : TwoComplex V) :
    @h1Err V _ l₁ X = @h1Err V _ l₂ X := by
  rw [@h1Err_def V _ l₁ X, @h1Err_def V _ l₂ X]
  congr 1; ext r
  refine exists_congr fun n => exists_congr fun α => ?_
  rw [Cochain.gaugeDistErr_congr_linearOrder l₁ l₂ α,
    Cochain.defect_congr_linearOrder l₁ l₂ isConjInvariant_movedNorm α]

/-- Relabelling `X` along `e : V ≃ W` preserves `h1Err`. -/
@[simp] theorem h1Err_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (X : TwoComplex V) (e : V ≃ W) : h1Err (X.relabel e) = h1Err X := by
  rw [h1Err_def, h1Err_def]; congr 1; ext r
  refine exists_congr fun n => ?_
  exact ((Cochain.relabelEquiv X e).exists_congr fun α => by
    simp [α.defect_relabel isConjInvariant_movedNorm e]).symm

/-- `h1Err` on the complete complex is preserved along any bijection `V ≃ W`. -/
theorem h1Err_complete_congr [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (e : V ≃ W) : h1Err (complete V) = h1Err (complete W) := by
  rw [← relabel_complete e, h1Err_relabel (complete V) e]

/-- `h1Err (complete V)` depends on `V` only through `Fintype.card V`. -/
theorem h1Err_complete_eq_of_card_eq [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (hcard : Fintype.card V = Fintype.card W) : h1Err (complete V) = h1Err (complete W) :=
  h1Err_complete_congr (Fintype.equivOfCardEq hcard)

end CrossDegreeCheeger

end TauCeti

end
