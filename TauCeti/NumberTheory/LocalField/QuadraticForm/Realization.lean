/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Hasse

import TauCeti.NumberTheory.LocalField.Squares

/-!
# Realization of local invariants of quadratic forms

Let `K` be a nonarchimedean local field in which `2` is invertible, in any residue characteristic.
A regular quadratic form over `K` has three invariants: its rank `n`, its discriminant
`d ∈ Kˣ/(Kˣ)²` and its local Hasse invariant `s ∈ {±1}`. This file determines exactly which
triples `(n, d, s)` with `n ≥ 1` occur: all of them, except `n = 1` with `s = -1`, and `n = 2`
with `d = [-1]` and `s = -1`.

Both exceptions are forced. A form of rank one has the empty Hasse product, and a binary form of
discriminant `[-1]` is the hyperbolic plane `⟨1, -1⟩`, whose Hasse invariant is `(1, -1)_K = 1`
(`TauCeti.RegularFormClass.localHasse_eq_one_of_rank_le_one` and
`TauCeti.RegularFormClass.localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one`).
Conversely, `⟨a, a δ⟩` has discriminant `[δ]` and Hasse invariant `(a, -δ)_K`, which is `-1` for a
suitable `a` as soon as `-δ` is a nonsquare, by nondegeneracy of the Hilbert symbol. In rank three
one adds a rank-one form `⟨c⟩` to such a binary form, with `c` chosen so that the binary form falls
outside the second exception, and in higher rank one adds copies of `⟨1⟩`, which change none of the
invariants.

This is the existence half of the classification of regular forms over `K` by `(n, d, s)`, and
the local input to the realization of admissible systems of invariants over a number field.

## Main results

* `TauCeti.RegularFormClass.exists_of_realization`: every triple `(n, d, s)` with `n ≥ 1` outside
  the two exceptions is the rank, discriminant and local Hasse invariant of a regular form.
* `TauCeti.RegularFormClass.exists_rank_eq_discr_eq_localHasse_eq_iff`: the realizable triples of
  positive rank are exactly those outside the two exceptions.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:23.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.3, Proposition 6.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

namespace RegularFormClass

/-- Realization in rank two: a binary class of discriminant `[δ]` has every local Hasse invariant
when `-δ` is a nonsquare, witnessed by `⟨a, a δ⟩` with `(a, -δ)_K = s`. -/
private theorem exists_rank_eq_two (δ : Kˣ) {s : ℤˣ} (hs : IsSquare (-δ) → s = 1) :
    ∃ x : RegularFormClass K, x.rank = 2 ∧ discr x = squareClass δ ∧ localHasse x = s := by
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, hilbertSymbol a (-δ) = s := by
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact ⟨1, hilbertSymbol_one_left _⟩
    · obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one (Invertible.ne_zero (2 : K))
        fun h => absurd (hs h) (by decide)
      exact ⟨b, by rw [hilbertSymbol_comm, hb]⟩
  refine ⟨Quotient.mk (regularFormSetoid K) ⟨2, ![a, a * δ]⟩, rank_mk _, ?_, ?_⟩
  · rw [discr_mk, Fin.prod_univ_two, squareClass_eq_iff_isSquare_mul]
    exact ⟨a * δ, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ac_rfl⟩
  · rw [localHasse_mk_binary, hilbertSymbol_self_mul (Invertible.ne_zero (2 : K)), ha]

/-- Realization in rank three: every discriminant and every local Hasse invariant occur. The class
is `y ⊥ ⟨c⟩`, where `-cδ` is a nonsquare and `y` is a binary class of discriminant `[cδ]`. -/
private theorem exists_rank_eq_three (δ : Kˣ) (s : ℤˣ) :
    ∃ x : RegularFormClass K, x.rank = 3 ∧ discr x = squareClass δ ∧ localHasse x = s := by
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, ¬IsSquare (-(c * δ)) := by
    by_cases hδ : IsSquare (-δ)
    · -- a uniformizer is a nonsquare, and so is its product with the square `-δ`
      obtain ⟨π, hπ⟩ := exists_isUniformizer K
      refine ⟨π, fun h => not_isSquare_of_isUniformizer hπ ?_⟩
      simpa [mul_neg] using h.mul hδ.inv
    · exact ⟨1, by simpa using hδ⟩
  obtain ⟨y, hy, hyd, hys⟩ :=
    exists_rank_eq_two (c * δ) (s := s * hilbertSymbol c (-δ)) fun h => absurd h hc
  refine ⟨y + Quotient.mk (regularFormSetoid K) ⟨1, fun _ => c⟩, ?_, ?_, ?_⟩
  · simp [rank_add, hy, rank_mk]
  · rw [discr_add, hyd, discr_mk, Fin.prod_univ_one, ← squareClass_mul,
      squareClass_eq_iff_isSquare_mul]
    exact ⟨c * δ, by ac_rfl⟩
  · rw [localHasse_add, hys, localHasse_mk_rankOne, hyd, discr_mk, Fin.prod_univ_one,
      hilbertSymbolOnSquareClasses_squareClass, hilbertSymbol_comm (c * δ),
      hilbertSymbol_self_mul (Invertible.ne_zero (2 : K)), mul_one, mul_assoc,
      Int.units_mul_self, mul_one]

/-- Realization in every rank at least three: adding `⟨1⟩` changes neither the discriminant nor
the local Hasse invariant. -/
private theorem exists_rank_eq_of_three_le {n : ℕ} (hn : 3 ≤ n) (δ : Kˣ) (s : ℤˣ) :
    ∃ x : RegularFormClass K, x.rank = n ∧ discr x = squareClass δ ∧ localHasse x = s := by
  induction n, hn using Nat.le_induction with
  | base => exact exists_rank_eq_three δ s
  | succ n _ ih =>
    obtain ⟨x, hx, hxd, hxs⟩ := ih
    refine ⟨x + 1, ?_, ?_, ?_⟩
    · rw [rank_add, hx, rank_one]
    · rw [discr_add, hxd, discr_one, add_zero (M := SquareClassGroup K)]
    · rw [localHasse_add, hxs, localHasse_one, discr_one,
        hilbertSymbolOnSquareClasses_zero_right, mul_one, mul_one]

/-- **Realization of local invariants** (O'Meara 63:23, Serre IV Prop 6). Over a nonarchimedean
local field, every triple `(n, d, s)` of a rank `n ≥ 1`, a square class `d` and a sign `s` is the
rank, discriminant and local Hasse invariant of a regular form, except when `n = 1` and `s = -1`,
or when `n = 2`, `d = [-1]` and `s = -1`. The two hypotheses exclude exactly these cases, and both
exclusions are necessary (`exists_rank_eq_discr_eq_localHasse_eq_iff`). -/
theorem exists_of_realization {n : ℕ} (hn : 1 ≤ n) (d : SquareClassGroup K) (s : ℤˣ)
    (h₁ : n = 1 → s = 1) (h₂ : n = 2 → d = squareClass (-1 : Kˣ) → s = 1) :
    ∃ x : RegularFormClass K, x.rank = n ∧ discr x = d ∧ localHasse x = s := by
  obtain ⟨δ, rfl⟩ : ∃ δ : Kˣ, squareClass δ = d := ⟨_, squareClass_toMul_out d⟩
  match n, hn with
  | 1, _ =>
    refine ⟨Quotient.mk (regularFormSetoid K) ⟨1, fun _ => δ⟩, rank_mk _, ?_, ?_⟩
    · rw [discr_mk, Fin.prod_univ_one]
    · rw [localHasse_mk_rankOne, h₁ rfl]
  | 2, _ =>
    exact exists_rank_eq_two δ fun h => h₂ rfl <|
      (squareClass_eq_iff_isSquare_mul _ _).mpr (by rwa [mul_neg_one])
  | n + 3, _ => exact exists_rank_eq_of_three_le (by omega) δ s

/-- **The realizable local invariants** (O'Meara 63:23, Serre IV Prop 6). For `n ≥ 1`, a regular
form of rank `n`, discriminant `d` and local Hasse invariant `s` exists if and only if neither
`n = 1` and `s = -1`, nor `n = 2`, `d = [-1]` and `s = -1`. -/
theorem exists_rank_eq_discr_eq_localHasse_eq_iff {n : ℕ} (hn : 1 ≤ n) (d : SquareClassGroup K)
    (s : ℤˣ) :
    (∃ x : RegularFormClass K, x.rank = n ∧ discr x = d ∧ localHasse x = s) ↔
      (n = 1 → s = 1) ∧ (n = 2 → d = squareClass (-1 : Kˣ) → s = 1) := by
  refine ⟨?_, fun h => exists_of_realization hn d s h.1 h.2⟩
  rintro ⟨x, rfl, rfl, rfl⟩
  exact ⟨fun h => localHasse_eq_one_of_rank_le_one h.le,
    localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one⟩

end RegularFormClass

end TauCeti
