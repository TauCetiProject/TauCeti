/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Relabel
import Mathlib.Basic.Real.Pointwise
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Attainment, coboundary vanishing, and relabelling invariance of cross-degree pair costs

For edge labels `α : V → V → Equiv.Perm (Fin n)` and vertex gauges `β : V → Equiv.Perm (Fin m)`,
the cross-degree pair cost sums `Equiv.Perm.distErr (α u v) (β u * (β v)⁻¹)` over oriented edges
`(u, v)`, and the cross-degree gauge distance takes the infimum over all gauge degrees `m + 2 ≥ 2`.
This file develops the structural properties connecting this cross-degree functional to equal-degree
moved-point gauge costs, coboundaries, vertex orderings, and vertex relabellings:

* **Equal-degree moved-norm rescaling and upper bounds**
  (`Finset.mul_sum_distErr_mul_inv_eq_sum_movedNorm`,
  `Finset.mul_ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm`, and
  `Finset.ciInf₂_sum_distErr_mul_inv_le_ciInf_sum_movedNorm_div`): in equal degree `n`, multiplying
  the cross-degree pair cost (or its gauge infimum) by `n` recovers the `movedNorm (Fin n)` gauge
  cost, so for `2 ≤ n` the cross-degree gauge infimum over `m + 2 ≥ 2` is at most `1 / n` times the
  equal-degree `movedNorm` gauge infimum.
* **Global gauge invariance in degree `2`** (`Finset.ciInf₂_sum_distErr_inv_mul_mul_two`): because
  `2 ≤ m + 2` for every `m : ℕ`, transforming a degree-`2` assignment by a degree-`2` vertex gauge
  preserves the global cross-degree infimum over all `m + 2 ≥ 2`.
* **Attainment across infinitely many gauge degrees** (`Finset.exists_eq_ciInf_sum_distErr_mul_inv`
  and `Finset.exists_eq_ciInf₂_sum_distErr_mul_inv`): on any finite edge set `E : Finset (V × V)`
  over an arbitrary (possibly infinite) vertex type `V`, both the fixed-degree infimum and the
  two-parameter infimum over all degrees `m + 2 ≥ 2` are attained. Indeed, the total agreement count
  lies in `{0, …, #E * n}` while `max n (m + 2)` grows without bound, so large gauge degrees cannot
  improve on any configuration with at least one agreement.
* **Uniform `1 / (n + 1)` non-coboundary gap and coboundary characterization**
  (`Finset.one_div_add_one_le_sum_distErr_mul_inv_of_not_exists`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_zero_iff`, and
  `Finset.ciInf₂_sum_distErr_mul_inv_pos_iff`): if `α` is not a coboundary on `E`, every gauge of
  every degree `m : ℕ` incurs cost at least `1 / (n + 1)`; hence for `2 ≤ n`, the cross-degree
  infimum vanishes if and only if `α` is an equal-degree coboundary on `E`.
* **Orientation doubling, vertex-order independence, and relabelling invariance**
  (`TauCeti.TwoComplex.two_mul_sum_distErr_mul_inv`,
  `TauCeti.TwoComplex.sum_distErr_mul_inv_relabel`,
  `TauCeti.TwoComplex.ciInf₂_sum_distErr_mul_inv_relabel`, and
  `TauCeti.TwoComplex.ciInf₂_sum_distErr_mul_inv_congr_linearOrder`): when reversing an edge
  inverts its permutation label, summing over `u < v` equals half the orientation-free sum over
  both orientations of each edge, making cross-degree pair costs and their gauge infima independent
  of the chosen linear order on `V` and invariant under arbitrary bijections `V ≃ W`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, equations (2.8)–(2.9).
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Section 2 and Proposition 10.
-/

public section

open Finset

namespace Finset

open Equiv Equiv.Perm TauCeti

variable {V : Type*} {n m : ℕ}

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
  have hbdd : BddBelow (Set.range fun m : ℕ =>
      ⨅ β : V → Perm (Fin (m + 2)), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact le_ciInf fun _ => sum_nonneg fun _ _ => distErr_nonneg _ _
  exact ciInf_le hbdd k

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
  have hg_nonneg (m : ℕ) : 0 ≤ g m :=
    le_ciInf fun _ => sum_nonneg fun _ _ => distErr_nonneg _ _
  have hS_ne : ((Iic M).image g).Nonempty := ⟨g 0, mem_image_of_mem g (mem_Iic.mpr (Nat.zero_le M))⟩
  obtain ⟨m₀, -, hm₀_eq⟩ := mem_image.mp (min'_mem ((Iic M).image g) hS_ne)
  obtain ⟨β₀, hβ₀⟩ := E.exists_eq_ciInf_sum_distErr_mul_inv α (m₀ + 2)
  refine ⟨m₀, β₀, le_antisymm ?_ ?_⟩
  · refine le_ciInf fun m => le_ciInf fun β => ?_
    obtain ⟨m₁, β₁, hm₁M, hle⟩ := hM m β
    have hmin : g m₀ ≤ g m₁ := hm₀_eq ▸ min'_le _ _ (mem_image_of_mem g (mem_Iic.mpr hm₁M))
    have hbdd₁ : BddBelow (Set.range fun β' : V → Perm (Fin (m₁ + 2)) =>
        ∑ e ∈ E, distErr (α e.1 e.2) (β' e.1 * (β' e.2)⁻¹)) :=
      ⟨0, by rintro _ ⟨_, rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
    exact (hβ₀.trans_le (hmin.trans (ciInf_le hbdd₁ β₁))).trans hle
  · have hbdd : BddBelow (Set.range g) := ⟨0, by rintro _ ⟨m, rfl⟩; exact hg_nonneg m⟩
    exact (ciInf_le hbdd m₀).trans_eq hβ₀.symm

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
  have hnn : 0 ≤ ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
    le_ciInf fun _ => le_ciInf fun _ => sum_nonneg fun _ _ => distErr_nonneg _ _
  constructor
  · intro h0
    by_contra hncob
    have hgap := E.one_div_add_one_le_ciInf₂_sum_distErr_mul_inv_of_not_exists α hncob
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · rintro ⟨β, hβ⟩
    have : NeZero n := ⟨by omega⟩
    have hle := E.ciInf₂_sum_distErr_mul_inv_le_ciInf_of_le α hn
    have hbdd : BddBelow (Set.range fun β' : V → Perm (Fin n) =>
        ∑ e ∈ E, distErr (α e.1 e.2) (β' e.1 * (β' e.2)⁻¹)) :=
      ⟨0, by rintro _ ⟨_, rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
    have hβ0 : (∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) = 0 :=
      sum_eq_zero fun e he => by rw [hβ e he, distErr_self]
    exact le_antisymm (hle.trans ((ciInf_le hbdd β).trans_eq hβ0)) hnn

/-- For `2 ≤ n`, the cross-degree gauge-cost infimum over all gauge degrees `m + 2 ≥ 2` is strictly
positive if and only if `α` is not an equal-degree coboundary on `E`. -/
theorem ciInf₂_sum_distErr_mul_inv_pos_iff (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n) :
    0 < (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ↔
      ¬ ∃ β : V → Perm (Fin n), ∀ e ∈ E, α e.1 e.2 = β e.1 * (β e.2)⁻¹ := by
  have hnn : 0 ≤ ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
    le_ciInf fun _ => le_ciInf fun _ => sum_nonneg fun _ _ => distErr_nonneg _ _
  rw [lt_iff_le_and_ne, and_iff_right hnn, ne_comm]
  exact not_iff_not.mpr (E.ciInf₂_sum_distErr_mul_inv_eq_zero_iff α hn)

end Finset

/-! ### Orientation doubling, vertex-order independence, and relabelling on two-complexes -/

namespace TauCeti.TwoComplex

open Equiv Equiv.Perm

variable {V W : Type*} {n m : ℕ}

/-- When reversing an edge of `X` inverts `α`, twice the cross-degree pair cost summed over
increasing edges `p.1 < p.2` equals the orientation-free sum over all ordered pairs of endpoints of
edges of `X`. -/
theorem two_mul_sum_distErr_mul_inv [Fintype V] [LinearOrder V] (X : TwoComplex V)
    (α : V → V → Perm (Fin n)) (hα : ∀ u v, X.Adj u v → α v u = (α u v)⁻¹)
    (β : V → Perm (Fin m)) :
    2 * (∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) =
      ∑ p : V × V with ({p.1, p.2} : Finset V) ∈ X.edges,
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
    X.two_nsmul_sum_filter_lt_edges (fun u v => distErr (α u v) (β u * (β v)⁻¹)) fun u v huv => by
      rw [hα u v huv, distErr_inv_mul_inv]

/-- Relabelling `X : TwoComplex V` along an arbitrary bijection `e : V ≃ W` (not required to
preserve the vertex linear order) preserves the cross-degree pair cost of skew-symmetric edge
labels. -/
theorem sum_distErr_mul_inv_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (X : TwoComplex V) (e : V ≃ W) (α : W → W → Perm (Fin n))
    (hα : ∀ u v, (X.relabel e).Adj u v → α v u = (α u v)⁻¹)
    (β : W → Perm (Fin m)) :
    (∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
        distErr (α (e p.1) (e p.2)) (β (e p.1) * (β (e p.2))⁻¹)) =
      ∑ q : W × W with q.1 < q.2 ∧ ({q.1, q.2} : Finset W) ∈ (X.relabel e).edges,
        distErr (α q.1 q.2) (β q.1 * (β q.2)⁻¹) :=
  X.sum_filter_lt_edges_relabel e (fun u v => distErr (α u v) (β u * (β v)⁻¹)) fun u v huv => by
    rw [hα u v huv, distErr_inv_mul_inv]

/-- Relabelling `X : TwoComplex V` along an arbitrary bijection `e : V ≃ W` preserves the degree-`m`
cross-degree gauge-cost infimum of skew-symmetric edge labels. -/
theorem ciInf_sum_distErr_mul_inv_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (X : TwoComplex V) (e : V ≃ W) (α : W → W → Perm (Fin n))
    (hα : ∀ u v, (X.relabel e).Adj u v → α v u = (α u v)⁻¹) (m : ℕ) :
    (⨅ β : V → Perm (Fin m),
        ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
          distErr (α (e p.1) (e p.2)) (β p.1 * (β p.2)⁻¹)) =
      ⨅ β : W → Perm (Fin m),
        ∑ q : W × W with q.1 < q.2 ∧ ({q.1, q.2} : Finset W) ∈ (X.relabel e).edges,
          distErr (α q.1 q.2) (β q.1 * (β q.2)⁻¹) :=
  ((Equiv.arrowCongr e (.refl (Perm (Fin m)))).symm.iInf_congr fun β => by
    simpa using X.sum_distErr_mul_inv_relabel e α hα β).symm

/-- Relabelling `X : TwoComplex V` along an arbitrary bijection `e : V ≃ W` preserves the global
cross-degree gauge-cost infimum of skew-symmetric edge labels over all degrees `m + 2 ≥ 2`. -/
theorem ciInf₂_sum_distErr_mul_inv_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (X : TwoComplex V) (e : V ≃ W) (α : W → W → Perm (Fin n))
    (hα : ∀ u v, (X.relabel e).Adj u v → α v u = (α u v)⁻¹) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
          distErr (α (e p.1) (e p.2)) (β p.1 * (β p.2)⁻¹)) =
      ⨅ (m : ℕ) (β : W → Perm (Fin (m + 2))),
        ∑ q : W × W with q.1 < q.2 ∧ ({q.1, q.2} : Finset W) ∈ (X.relabel e).edges,
          distErr (α q.1 q.2) (β q.1 * (β q.2)⁻¹) :=
  iInf_congr fun m => X.ciInf_sum_distErr_mul_inv_relabel e α hα (m + 2)

/-- The cross-degree pair cost on `X : TwoComplex V` is independent of the chosen linear order on
`V` whenever reversing an edge of `X` inverts `α`. -/
theorem sum_distErr_mul_inv_congr_linearOrder [Fintype V] (X : TwoComplex V)
    (l₁ l₂ : LinearOrder V) (α : V → V → Perm (Fin n))
    (hα : ∀ u v, X.Adj u v → α v u = (α u v)⁻¹)
    (β : V → Perm (Fin m)) :
    (letI := l₁
      ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) =
    (letI := l₂
      ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) :=
  X.sum_filter_lt_edges_congr_linearOrder l₁ l₂
    (fun u v => distErr (α u v) (β u * (β v)⁻¹)) fun u v huv => by
      rw [hα u v huv, distErr_inv_mul_inv]

/-- The degree-`m` cross-degree gauge-cost infimum on `X : TwoComplex V` is independent of the
chosen linear order on `V` whenever reversing an edge of `X` inverts `α`. -/
theorem ciInf_sum_distErr_mul_inv_congr_linearOrder [Fintype V] (X : TwoComplex V)
    (l₁ l₂ : LinearOrder V) (α : V → V → Perm (Fin n))
    (hα : ∀ u v, X.Adj u v → α v u = (α u v)⁻¹) (m : ℕ) :
    (letI := l₁
      ⨅ β : V → Perm (Fin m),
        ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
          distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) =
    (letI := l₂
      ⨅ β : V → Perm (Fin m),
        ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
          distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) :=
  iInf_congr (X.sum_distErr_mul_inv_congr_linearOrder l₁ l₂ α hα)

/-- The cross-degree gauge-cost infimum over all degrees `m + 2 ≥ 2` on `X : TwoComplex V` is
independent of the chosen linear order on `V` whenever reversing an edge of `X` inverts `α`. -/
theorem ciInf₂_sum_distErr_mul_inv_congr_linearOrder [Fintype V] (X : TwoComplex V)
    (l₁ l₂ : LinearOrder V) (α : V → V → Perm (Fin n))
    (hα : ∀ u v, X.Adj u v → α v u = (α u v)⁻¹) :
    (letI := l₁
      ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
          distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) =
    (letI := l₂
      ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ p : V × V with p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges,
          distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)) :=
  iInf_congr fun m => X.ciInf_sum_distErr_mul_inv_congr_linearOrder l₁ l₂ α hα (m + 2)

end TauCeti.TwoComplex

end
