/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Admissible triples of spins

The tensor product of the irreducible representations of `SU(2)` of spins `j₁` and `j₂`
decomposes, without multiplicity, into the irreducible representations of the spins
`j = j₁ + j₂ - k`, `k = 0, 1, …, min(2j₁, 2j₂)`. The same fusion rule holds for the
finite-dimensional type-1 modules of `U_q(sl₂)` at a generic parameter `q`. This file defines the
admissible triples `(j₁, j₂, j)` of this fusion rule and the elementary facts about them.

Spins are encoded by their doubles: the spin `j = d / 2` is given by `d : ℕ`, which is also the
highest weight of the representation of spin `j`.

## Main definitions

* `TauCeti.SU2.IsTriad d₁ d₂ d`: the spins `(d₁ / 2, d₂ / 2, d / 2)` form an admissible triple,
  that is `d = d₁ + d₂ - 2k` for some `k ≤ min d₁ d₂`.
* `TauCeti.SU2.IsTriad.index`: the index `k = (d₁ + d₂ - d) / 2` of an admissible triple.

## Main results

* `TauCeti.SU2.isTriad_iff`: the admissible triples are those satisfying the triangle
  inequalities `|j₁ - j₂| ≤ j ≤ j₁ + j₂` with `j₁ + j₂ + j` an integer [Edmonds, (3.1.5)].
* `TauCeti.SU2.isTriad_comm`, `TauCeti.SU2.isTriad_rotate`: admissibility is invariant under
  permutations of the three spins.
* `TauCeti.SU2.sum_fin_sub_two_mul_eq_sum_range`: a sum over the indices `k ≤ min d₁ d₂` as a
  sum over the admissible `d`.
* `TauCeti.SU2.sum_isTriad_succ`: the dimension count `Σ_j (2j + 1) = (2j₁ + 1)(2j₂ + 1)` over
  the admissible `j`.

## References

* [Edmonds] A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press,
  1957, §3.1. Equation numbers refer to the 1957 printing.
* NIST Digital Library of Mathematical Functions, §34.2, <https://dlmf.nist.gov/34.2>.

The name `IsTriad` and the encoding by doubled spins follow the prior formalization lean-SFVK of
B. J. Braams (<https://github.com/bjbraams/lean-SFVK>, Apache-2.0), file
`SFVK/ClebschGordan/Basic/Coefficients.lean`.
-/

public section

namespace TauCeti.SU2

open Finset

/-- **Admissible triple** [Edmonds, (3.1.5)]; DLMF §34.2: the spin `d / 2` occurs in the tensor
product of the representations of spins `d₁ / 2` and `d₂ / 2`, that is `d = d₁ + d₂ - 2k` for some
`k ≤ min d₁ d₂`. By `isTriad_iff`, these are the triples satisfying the triangle inequalities
`|j₁ - j₂| ≤ j ≤ j₁ + j₂` with `j₁ + j₂ + j` an integer. -/
def IsTriad (d₁ d₂ d : ℕ) : Prop :=
  ∃ k : Fin (min d₁ d₂ + 1), d₁ + d₂ - 2 * (k : ℕ) = d

/-- Definitional characterization of `IsTriad`. -/
theorem isTriad_def {d₁ d₂ d : ℕ} :
    IsTriad d₁ d₂ d ↔ ∃ k : Fin (min d₁ d₂ + 1), d₁ + d₂ - 2 * (k : ℕ) = d := Iff.rfl

instance (d₁ d₂ : ℕ) : DecidablePred (IsTriad d₁ d₂) :=
  fun _ ↦ decidable_of_iff _ isTriad_def.symm

/-- **Triangle and parity characterization** of admissible triples [Edmonds, (3.1.5)]. -/
theorem isTriad_iff {d₁ d₂ d : ℕ} :
    IsTriad d₁ d₂ d ↔ d ≤ d₁ + d₂ ∧ d₁ ≤ d₂ + d ∧ d₂ ≤ d₁ + d ∧ Even (d₁ + d₂ + d) := by
  rw [Nat.even_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have := k.isLt
    omega
  · rintro ⟨_, _, _, _⟩
    exact ⟨⟨(d₁ + d₂ - d) / 2, by omega⟩, by dsimp only; omega⟩

/-- Admissibility is symmetric in the first two spins. -/
theorem isTriad_comm (d₁ d₂ d : ℕ) : IsTriad d₁ d₂ d ↔ IsTriad d₂ d₁ d := by
  simp only [isTriad_iff, Nat.even_iff]
  omega

/-- Admissibility is invariant under the cyclic permutation of the three spins. -/
theorem isTriad_rotate (d₁ d₂ d : ℕ) : IsTriad d₁ d₂ d ↔ IsTriad d₂ d d₁ := by
  simp only [isTriad_iff, Nat.even_iff]
  omega

/-- The spin of an admissible triple is at most the sum of the other two. -/
theorem IsTriad.le_add {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) : d ≤ d₁ + d₂ := by
  rcases h with ⟨_, rfl⟩
  omega

/-- The index `k ≤ min d₁ d₂` with `d = d₁ + d₂ - 2k` of an admissible triple, computed
explicitly as `(d₁ + d₂ - d) / 2`. -/
def IsTriad.index {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) : Fin (min d₁ d₂ + 1) :=
  ⟨(d₁ + d₂ - d) / 2, by rcases h with ⟨k, rfl⟩; have := k.isLt; omega⟩

/-- The underlying natural number of `h.index` is `(d₁ + d₂ - d) / 2`. -/
theorem IsTriad.val_index {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) :
    (h.index : ℕ) = (d₁ + d₂ - d) / 2 := (rfl)

/-- The index of an admissible triple recovers its third spin. -/
@[simp] theorem IsTriad.sub_two_mul_index {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) :
    d₁ + d₂ - 2 * (h.index : ℕ) = d := by
  rcases h with ⟨k, rfl⟩; have := k.isLt; simp only [index]; omega

/-- Uniqueness of the index of an admissible triple. -/
theorem IsTriad.index_eq_of_eq {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d)
    {k : Fin (min d₁ d₂ + 1)} (hk : d₁ + d₂ - 2 * (k : ℕ) = d) : h.index = k := by
  ext; have := k.isLt; simp only [index, ← hk]; omega

/-- `h.index = k` holds exactly when `d₁ + d₂ - 2k = d`. -/
@[simp] theorem IsTriad.index_eq_iff {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d)
    (k : Fin (min d₁ d₂ + 1)) : h.index = k ↔ d₁ + d₂ - 2 * (k : ℕ) = d :=
  ⟨fun hk ↦ hk ▸ h.sub_two_mul_index, h.index_eq_of_eq⟩

/-- Every index `k ≤ min d₁ d₂` gives an admissible triple. -/
theorem isTriad_sub_two_mul {d₁ d₂ : ℕ} (k : Fin (min d₁ d₂ + 1)) :
    IsTriad d₁ d₂ (d₁ + d₂ - 2 * (k : ℕ)) := ⟨k, rfl⟩

/-- The index of `d₁ + d₂ - 2k` is `k`. -/
@[simp] theorem IsTriad.index_sub_two_mul {d₁ d₂ : ℕ} (k : Fin (min d₁ d₂ + 1)) :
    (isTriad_sub_two_mul k).index = k :=
  (isTriad_sub_two_mul k).index_eq_of_eq rfl

/-- The stretched triple `(j₁, j₂, j₁ + j₂)` (`k = 0`) is always admissible. -/
theorem isTriad_add (d₁ d₂ : ℕ) : IsTriad d₁ d₂ (d₁ + d₂) := ⟨0, by simp⟩

/-- Coupling spin `0` on the left gives the second spin only. -/
@[simp] theorem isTriad_zero_left {d₂ d : ℕ} : IsTriad 0 d₂ d ↔ d = d₂ :=
  ⟨by rintro ⟨k, rfl⟩; have := k.isLt; omega, fun h ↦ h ▸ ⟨0, by simp⟩⟩

/-- Coupling spin `0` on the right gives the first spin only. -/
@[simp] theorem isTriad_zero_right {d₁ d : ℕ} : IsTriad d₁ 0 d ↔ d = d₁ :=
  ⟨by rintro ⟨k, rfl⟩; have := k.isLt; omega, fun h ↦ h ▸ ⟨0, by simp⟩⟩

/-- Reindexing a sum over the indices `k : Fin (min d₁ d₂ + 1)` as a sum over the spins
`d ∈ Finset.range (d₁ + d₂ + 1)` when `g` vanishes off the admissible `d`. -/
theorem sum_fin_sub_two_mul_eq_sum_range {M : Type*} [AddCommMonoid M] (d₁ d₂ : ℕ) (g : ℕ → M)
    (hg : ∀ d, ¬IsTriad d₁ d₂ d → g d = 0) :
    ∑ k : Fin (min d₁ d₂ + 1), g (d₁ + d₂ - 2 * (k : ℕ)) = ∑ d ∈ range (d₁ + d₂ + 1), g d := by
  trans ∑ d ∈ (range (d₁ + d₂ + 1)).filter (IsTriad d₁ d₂), g d
  · refine sum_bij (fun (k : Fin (min d₁ d₂ + 1)) _ ↦ d₁ + d₂ - 2 * (k : ℕ)) ?_ ?_ ?_
      fun _ _ ↦ rfl
    · intro k _; rw [mem_filter, mem_range]
      exact ⟨by omega, isTriad_sub_two_mul k⟩
    · intro k₁ _ k₂ _ _; have := k₁.isLt; have := k₂.isLt; ext; omega
    · intro d hd; rw [mem_filter] at hd
      exact ⟨hd.2.index, mem_univ _, hd.2.sub_two_mul_index⟩
  · exact sum_filter_of_ne fun d _ hgd ↦ by by_contra h; exact hgd (hg d h)

/-- **The dimension count** `Σ_j (2j + 1) = (2j₁ + 1)(2j₂ + 1)`, the sum over the admissible
`j`: the dimensions of the representations occurring in the tensor product of the
representations of spins `j₁` and `j₂` add up to the dimension of that tensor product. -/
theorem sum_isTriad_succ (d₁ d₂ : ℕ) :
    ∑ d ∈ (range (d₁ + d₂ + 1)).filter (IsTriad d₁ d₂), (d + 1) = (d₁ + 1) * (d₂ + 1) := by
  rw [sum_filter,
    ← sum_fin_sub_two_mul_eq_sum_range d₁ d₂ _ fun d hd ↦ ite_eq_right fun h ↦ (hd h).elim,
    ← sum_range_min_add_one_sub_two_mul, ← Fin.sum_univ_eq_sum_range fun k ↦ d₁ + d₂ - 2 * k + 1]
  exact sum_congr rfl fun k _ ↦ ite_eq_left (isTriad_sub_two_mul k)

end TauCeti.SU2
