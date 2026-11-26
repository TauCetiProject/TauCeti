/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Fintype.Pi
public import TauCeti.Algebra.Order.BigOperators.Dominance
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.Floor.Ring

/-!
# Newton vectors of `GL_n` and the admissible set `B(GL_n, μ)`

By the Dieudonné–Manin classification, an isocrystal of height `n` over an algebraically closed
field of characteristic `p` is determined up to isomorphism by its *Newton vector*: the decreasing
list `ν = (ν₀ ≥ ν₁ ≥ ⋯ ≥ νₙ₋₁)` of its rational slopes, counted with multiplicity. A slope `λ`
occurs with a multiplicity `m` such that `m λ ∈ ℤ`, since the simple isocrystal of slope `r / s` in
lowest terms has height `s`. This identifies the set `B(GL_n)` of `σ`-conjugacy classes of
`GL_n(L)` with the set of such vectors; under it, the Kottwitz invariant is the total slope.

This file develops the combinatorics of these vectors that the Newton stratification uses. It
builds on the dominance order and the pairing with `2ρ` of
`TauCeti.Algebra.Order.BigOperators.Dominance`.

* The pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)` with the sum of the positive roots of `GL_n`
  (`TauCeti.twoRhoPairing`). For the Newton vector `ν_b` of a Newton stratum of a Shimura variety
  of PEL type, `d_b = ⟨2ρ, ν_b⟩` is the dimension of its central leaves.
* The order `ν ≼ ν'` on Newton vectors is the dominance order `TauCeti.Dominates ν ν'`: equal
  totals, and leading partial sums of `ν` at most those of `ν'`. The pairing with `2ρ` is
  monotone (`TauCeti.Dominates.twoRhoPairing_le`) and strictly monotone
  (`TauCeti.Dominates.twoRhoPairing_lt`) for it.
* For an integral vector `μ`, `TauCeti.admissibleNewtonVectors μ` consists of the Newton vectors
  `ν ≼ μ`, that is `TauCeti.Dominates ν μ`. The vector `μ` is used in its given order: when `μ` is
  decreasing, the dominant representative of an integral cocharacter, this is the admissible set
  `B(GL_n, μ)`; for other `μ` it is only the set of Newton vectors dominated by `μ`. It is finite
  for every `μ` (`TauCeti.finite_admissibleNewtonVectors`): its slopes lie between the last and
  the first coordinates of `μ`, and have denominators dividing `n!`. When `μ` is decreasing it is
  itself the largest element of `B(GL_n, μ)`, the ordinary class. Every Newton vector `ν ≼ μ` has
  `⟨2ρ, ν⟩ ≤ ⟨2ρ, μ⟩` (`TauCeti.Dominates.twoRhoPairing_le`), and in a product of general linear
  groups the sums of these pairings agree only for `ν = μ`
  (`TauCeti.sum_twoRhoPairing_eq_sum_twoRhoPairing_intCast_iff`).

For instance `B(GL₂, (1, 0))` consists of the ordinary vector `(1, 0)` and the basic vector
`(1/2, 1/2)` (`TauCeti.admissibleNewtonVectors_one_zero`), with pairings `1` and `0`; the vector
`(1/2, 0)` is not a Newton vector, since the slope `1/2` would occur only once.

## Main definitions

* `TauCeti.IsNewtonVector ν`: `ν` is decreasing and each slope `λ` of multiplicity `m` has
  `m λ ∈ ℤ`.
* `TauCeti.admissibleNewtonVectors μ`: the Newton vectors `ν ≼ μ` for an integral vector `μ`;
  for decreasing `μ` this is `B(GL_n, μ)`.

## Main results

* `TauCeti.IsNewtonVector.exists_int_factorial_mul_eq`: `n! νᵢ` is an integer.
* `TauCeti.IsNewtonVector.exists_int_eq_of_card_eq_one`: a slope of multiplicity one is an
  integer.
* `TauCeti.finite_admissibleNewtonVectors`: for every integral vector `μ`, the Newton vectors
  `ν ≼ μ` form a finite set; for decreasing `μ` this is `B(GL_n, μ)`.
* `TauCeti.sum_twoRhoPairing_eq_sum_twoRhoPairing_intCast_iff`: for Newton vectors `ν_w ≼ μ_w`,
  the sums of the pairings with `2ρ` of `ν` and of `μ` agree only for `ν = μ`; for decreasing
  `μ_w` these are the families in `∏_w B(GL_n, μ_w)`.
* `TauCeti.admissibleNewtonVectors_one_zero`: `B(GL₂, (1, 0)) = {(1, 0), (1/2, 1/2)}`.

## References

* R. E. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), §§4–6.
* M. Rapoport and M. Richartz, *On the classification and specialization of F-isocrystals with
  additional structure*, Compositio Math. 103 (1996), §§1–2.
* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), §3.1.
-/

public section

open Finset

namespace TauCeti

variable {n : ℕ}

/-! ### Newton vectors -/

/-- `ν` is a **Newton vector**: the slope vector of an isocrystal of height `n`. Its coordinates
decrease, and each slope `λ = νᵢ`, occurring with multiplicity `m`, satisfies `m λ ∈ ℤ`. -/
structure IsNewtonVector (ν : Fin n → ℚ) : Prop where
  /-- The slopes are listed in decreasing order. -/
  antitone : Antitone ν
  /-- A slope `λ` of multiplicity `m` has `m λ ∈ ℤ`. -/
  exists_int_card_mul_eq : ∀ i, ∃ z : ℤ, (#{j | ν j = ν i} : ℚ) * ν i = z

/-- A decreasing integral vector is a Newton vector. -/
theorem isNewtonVector_intCast {μ : Fin n → ℤ} (hμ : Antitone μ) :
    IsNewtonVector fun i ↦ (μ i : ℚ) := by
  refine ⟨fun i j hij ↦ Int.cast_le.mpr (hμ hij), fun i ↦ ?_⟩
  exact ⟨#{j | (μ j : ℚ) = μ i} * μ i, by simp⟩

/-- A constant vector `(c, …, c)` of height `n` is a Newton vector exactly when `n c ∈ ℤ`. These
are the basic Newton vectors. -/
theorem isNewtonVector_const_iff {c : ℚ} :
    IsNewtonVector (fun _ : Fin n ↦ c) ↔ ∃ z : ℤ, n * c = z := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hz⟩ ↦ ⟨fun _ _ _ ↦ le_rfl, fun _ ↦ ⟨z, by simpa using hz⟩⟩⟩
  rcases n with _ | n
  · exact ⟨0, by simp⟩
  · simpa using h.exists_int_card_mul_eq 0

/-- **Denominators of slopes.** The coordinates of a Newton vector of height `n` become integers
after multiplication by `n!`. -/
theorem IsNewtonVector.exists_int_factorial_mul_eq {ν : Fin n → ℚ} (hν : IsNewtonVector ν)
    (i : Fin n) : ∃ z : ℤ, (n.factorial : ℚ) * ν i = z := by
  obtain ⟨z, hz⟩ := hν.exists_int_card_mul_eq i
  have hpos : 0 < #{j | ν j = ν i} := card_pos.mpr ⟨i, by simp⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hpos (card_le_univ _ |>.trans (Fintype.card_fin n).le)
  exact ⟨c * z, by rw [hc]; push_cast; rw [mul_comm (#_ : ℚ), mul_assoc, hz]⟩

/-- A slope of multiplicity one is an integer. -/
theorem IsNewtonVector.exists_int_eq_of_card_eq_one {ν : Fin n → ℚ} (hν : IsNewtonVector ν)
    {i : Fin n} (h : #{j | ν j = ν i} = 1) : ∃ z : ℤ, ν i = z := by
  simpa [h] using hν.exists_int_card_mul_eq i

/-! ### The admissible set -/

/-- The Newton vectors `ν` dominated by an integral vector `μ`, `ν ≼ μ` (`TauCeti.Dominates ν μ`),
that is with the same total slope as `μ` and leading partial sums at most those of `μ`. The
vector `μ` is not sorted. When `μ` is decreasing, the dominant representative of an integral
cocharacter, this is the **admissible set** `B(GL_n, μ)`: the set of Newton vectors of the
`μ`-admissible classes in `B(GL_n)`. For other `μ` it is only the set of Newton vectors dominated
by `μ`. -/
def admissibleNewtonVectors (μ : Fin n → ℤ) : Set (Fin n → ℚ) :=
  {ν | IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ)}

/-- Membership in `TauCeti.admissibleNewtonVectors μ`: a Newton vector `ν` with `ν ≼ μ`. -/
@[simp]
theorem mem_admissibleNewtonVectors {μ : Fin n → ℤ} {ν : Fin n → ℚ} :
    ν ∈ admissibleNewtonVectors μ ↔ IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ) :=
  Iff.rfl

/-- A decreasing integral cocharacter lies in its own admissible set: it is the ordinary class. -/
theorem intCast_mem_admissibleNewtonVectors {μ : Fin n → ℤ} (hμ : Antitone μ) :
    (fun i ↦ (μ i : ℚ)) ∈ admissibleNewtonVectors μ :=
  ⟨isNewtonVector_intCast hμ, Dominates.refl _⟩

/-- **Finiteness of the admissible set.** For every integral vector `μ`, the set of Newton
vectors `ν ≼ μ` is finite: their coordinates lie between the last and the first coordinates of
`μ`, and in `(1 / n!) ℤ`. For decreasing `μ` this is the admissible set `B(GL_n, μ)`. -/
theorem finite_admissibleNewtonVectors (μ : Fin n → ℤ) : (admissibleNewtonVectors μ).Finite := by
  rcases n with _ | n
  · exact Set.toFinite _
  refine (Set.Finite.pi (t := fun _ ↦ {q : ℚ | q ∈ Set.Icc (μ (Fin.last n) : ℚ) (μ 0) ∧
      ∃ m : ℤ, ((n + 1).factorial : ℚ) * q = m}) fun _ ↦
    finite_setOf_mem_Icc_natCast_mul_eq_intCast (Nat.factorial_ne_zero _) _ _).subset ?_
  rintro ν ⟨hν, hdom⟩ i -
  exact ⟨⟨hdom.apply_last_le_apply hν.antitone i, hdom.apply_le_apply_zero hν.antitone i⟩,
    hν.exists_int_factorial_mul_eq i⟩

/-- **The ordinary class in a product of general linear groups.** Let `ν = (ν_w)_w` be a finite
family of Newton vectors with `ν_w ≼ μ_w` for every `w`. Then
`∑_w ⟨2ρ, ν_w⟩ = ∑_w ⟨2ρ, μ_w⟩` only for `ν_w = μ_w` for every `w`. Since each
`⟨2ρ, ν_w⟩ ≤ ⟨2ρ, μ_w⟩` (`TauCeti.Dominates.twoRhoPairing_le`), for decreasing `μ_w` and the group
`∏_w GL_n` this says that the ordinary class is the only admissible class whose dimension `d_b`
attains the maximum. -/
theorem sum_twoRhoPairing_eq_sum_twoRhoPairing_intCast_iff {W : Type*} [Fintype W]
    {μ : W → Fin n → ℤ} {ν : W → Fin n → ℚ} (hν : ∀ w, ν w ∈ admissibleNewtonVectors (μ w)) :
    ∑ w, twoRhoPairing (ν w) = ∑ w, twoRhoPairing (fun i ↦ (μ w i : ℚ)) ↔
      ν = fun w i ↦ (μ w i : ℚ) :=
  sum_twoRhoPairing_eq_sum_twoRhoPairing_iff fun w ↦ (hν w).2

/-- **`B(GL₂, (1, 0))`.** The admissible set of the cocharacter `(1, 0)` of `GL₂` consists of the
ordinary vector `(1, 0)` and the basic vector `(1/2, 1/2)`. -/
theorem admissibleNewtonVectors_one_zero :
    admissibleNewtonVectors ![1, 0] = {![1, 0], ![1 / 2, 1 / 2]} := by
  ext ν
  simp only [mem_admissibleNewtonVectors, dominates_iff_fin_two, Set.mem_insert_iff,
    Set.mem_singleton_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_zero]
  constructor
  · rintro ⟨hN, htot, h₀⟩
    have h₁₀ : ν 1 ≤ ν 0 := hN.antitone (Fin.zero_le 1)
    by_cases heq : ν 0 = ν 1
    · -- equal slopes: the basic vector
      right
      ext i
      fin_cases i <;> simp <;> linarith
    · -- distinct slopes: each occurs once, so is an integer, which forces `(1, 0)`
      left
      obtain ⟨z, hz⟩ := hN.exists_int_eq_of_card_eq_one (i := 0)
        (card_eq_one.mpr ⟨0, by ext j; fin_cases j <;> simp [Ne.symm heq]⟩)
      have hz₁ : z ≤ 1 := by exact_mod_cast hz ▸ h₀
      have hz₀ : 0 < z := by exact_mod_cast (show (0 : ℚ) < z by linarith)
      have hν₀ : ν 0 = 1 := by rw [hz, show z = 1 by omega, Int.cast_one]
      ext i
      fin_cases i <;> simp <;> linarith
  · rintro (rfl | rfl)
    · refine ⟨?_, by norm_num, by norm_num⟩
      have : (![1, 0] : Fin 2 → ℚ) = fun i ↦ ((![1, 0] : Fin 2 → ℤ) i : ℚ) := by
        ext i; fin_cases i <;> simp
      rw [this]
      exact isNewtonVector_intCast (by simp [antitone_vecCons])
    · refine ⟨?_, by norm_num, by norm_num⟩
      have : (![1 / 2, 1 / 2] : Fin 2 → ℚ) = fun _ ↦ 1 / 2 := by
        ext i; fin_cases i <;> simp
      rw [this, isNewtonVector_const_iff]
      exact ⟨1, by norm_num⟩

end TauCeti
