/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.Ring.CharZero

/-!
# Character means on the complement of a quadratic kernel

On the nonidentity coset of a nontrivial quadratic character's kernel, the trivial character
has mean `1`, the quadratic character has mean `-1`, and every other linear character has
mean zero. This is the projection onto the difference of the two Fourier coefficients that
occurs when averaging main terms in Frobenius-restricted prime sums.
-/

public section

open scoped BigOperators

namespace MonoidHom

/-- A character whose square is trivial has values in `{1, -1}`. -/
theorem apply_eq_one_or_eq_neg_one_of_mul_self_eq_one {G K : Type*} [Monoid G]
    [CommRing K] [IsDomain K] (q : G →* Kˣ) (hq : q * q = 1) (g : G) :
    (q g : K) = 1 ∨ (q g : K) = -1 := by
  apply sq_eq_one_iff.mp
  simpa only [pow_two, mul_apply, Units.val_mul, one_apply, Units.val_one] using
    congrArg (fun f : G →* Kˣ ↦ (f g : K)) hq

open Classical in
/-- The mean of a linear character off the kernel of a nontrivial quadratic character `q`.
Only the trivial character and `q` have nonzero mean there. -/
theorem expect_apply_off_ker_of_mul_self_eq_one {G K : Type*} [Group G] [Fintype G]
    [Field K] [CharZero K] (q χ : G →* Kˣ) (hq : q * q = 1) (hq₁ : q ≠ 1) :
    (𝔼 g with q g ≠ 1, (χ g : K)) = if χ = 1 then 1 else if χ = q then -1 else 0 := by
  have hsum (ψ : G →* Kˣ) : (∑ g, (ψ g : K)) = if ψ = 1 then (Fintype.card G : K) else 0 := by
    have hiff : (Units.coeHom K).comp ψ = 1 ↔ ψ = 1 := by
      constructor
      · intro h
        ext g
        exact DFunLike.congr_fun h g
      · rintro rfl
        ext
        simp
    simpa only [comp_apply, Units.coeHom_apply, Nat.cast_ite, Nat.cast_zero, hiff] using
      (sum_hom_units ((Units.coeHom K).comp ψ))
  have htwice (ψ : G →* Kˣ) :
      2 * (∑ g with q g ≠ 1, (ψ g : K)) = (∑ g, (ψ g : K)) - ∑ g, ((q * ψ) g : K) := by
    rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    rcases q.apply_eq_one_or_eq_neg_one_of_mul_self_eq_one hq g with hg | hg
    · have hunit : q g = 1 := Units.ext (by simpa only [Units.val_one] using hg)
      simp [hunit]
    · have hunit : q g ≠ 1 := fun he ↦ one_ne_zero (CharZero.neg_eq_self_iff.mp
        (by simpa only [he, Units.val_one] using hg.symm))
      simp [hunit, hg, two_mul]
  have hcard : 2 * ((Finset.univ.filter fun g ↦ q g ≠ 1).card : K) = Fintype.card G := by
    simpa [hsum, hq₁] using htwice 1
  have hne : ((Finset.univ.filter fun g ↦ q g ≠ 1).card : K) ≠ 0 := by
    intro hz
    exact (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := G)) :
      (Fintype.card G : K) ≠ 0) (by simpa [hz] using hcard.symm)
  have hmul : q * χ = 1 ↔ χ = q := by
    constructor
    · intro h
      apply DFunLike.ext
      intro g
      apply mul_left_cancel (a := q g)
      simpa only [mul_apply] using DFunLike.congr_fun (h.trans hq.symm) g
    · rintro rfl
      exact hq
  rw [Finset.expect_eq_sum_div_card, div_eq_iff hne]
  have hh := htwice χ
  rw [hsum, hsum, hmul, ← hcard] at hh
  apply mul_left_cancel₀ (two_ne_zero : (2 : K) ≠ 0)
  rw [hh]
  by_cases h₁ : χ = 1
  · subst χ
    simp [Ne.symm hq₁]
  · by_cases h₂ : χ = q <;> simp [h₁, h₂, hq₁, mul_neg]

end MonoidHom
