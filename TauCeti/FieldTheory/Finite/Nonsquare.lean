/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Complementary nonsquares in a finite field

In a finite field `F` of odd characteristic some `x` has both `x` and `1 - x` nonsquares. Indeed,
multiplication by a fixed nonsquare sends the nonzero squares injectively to the nonsquares, so
there are at least as many nonsquares as nonzero squares. If `1 - x` were a square for every
nonsquare `x`, then `x ↦ 1 - x` would send the nonsquares injectively to the nonzero squares
other than `1`, which are fewer.

This is the input to the vanishing of every Steinberg symbol over a finite field: writing `x` and
`1 - x` as powers of a generator `g` of the cyclic group `Fˣ`, both exponents are odd, so the
relation `{x, 1 - x} = 0` kills the two-torsion symbol `{g, g}`.

## Main results

* `TauCeti.FiniteField.exists_not_isSquare_and_not_isSquare_one_sub`: in a finite field of
  characteristic other than `2`, some `x` has `x` and `1 - x` both nonsquares.

## References

* C. Weibel, *The K-book*, Chapter III, Corollary 6.1.1.
-/

public section

namespace TauCeti.FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- **Complementary nonsquares.** In a finite field of characteristic other than `2` there is an
`x` such that neither `x` nor `1 - x` is a square. -/
theorem exists_not_isSquare_and_not_isSquare_one_sub (hF : ringChar F ≠ 2) :
    ∃ x : F, ¬IsSquare x ∧ ¬IsSquare (1 - x) := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hF
  have hn0 : n ≠ 0 := by rintro rfl; exact hn IsSquare.zero
  by_contra! h
  let N := Finset.univ.filter fun x : F ↦ ¬IsSquare x
  let Q := Finset.univ.filter fun x : F ↦ IsSquare x ∧ x ≠ 0
  -- A nonzero square times the nonsquare `n` is a nonsquare.
  have hQN : Q.card ≤ N.card := by
    refine Finset.card_le_card_of_injOn (n * ·) (fun a ha ↦ ?_)
      (mul_right_injective₀ hn0).injOn
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, N, Q] at ha ⊢
    obtain ⟨⟨c, rfl⟩, hc⟩ := ha
    rintro ⟨b, hb⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    exact hn ⟨b * c⁻¹, by field_simp; linear_combination hb⟩
  -- Under `h`, the map `x ↦ 1 - x` sends the nonsquares into the nonzero squares other than `1`.
  have hNQ : N.card ≤ (Q.erase 1).card := by
    refine Finset.card_le_card_of_injOn (1 - ·) (fun x hx ↦ ?_) (sub_right_injective).injOn
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, N] at hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx IsSquare.zero
    have hx1 : x ≠ 1 := by rintro rfl; exact hx IsSquare.one
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff, Q]
    exact ⟨⟨h x hx, sub_ne_zero.2 hx1.symm⟩, fun h1 ↦ hx0 (by linear_combination -h1)⟩
  have h1 : (1 : F) ∈ Q := by simp [Q]
  have := Finset.card_erase_of_mem h1
  have := Finset.card_pos.2 ⟨1, h1⟩
  omega

end TauCeti.FiniteField
