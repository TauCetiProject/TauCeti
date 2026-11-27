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

/-- A character whose square is trivial takes only the values `1` and `-1`. -/
theorem apply_eq_one_or_eq_neg_one_of_mul_self_eq_one {G K : Type*} [Monoid G]
    [CommRing K] [IsDomain K] (q : G →* Kˣ) (hq : q * q = 1) (g : G) :
    q g = 1 ∨ q g = -1 := by
  have h := congrArg (fun f : G →* Kˣ ↦ (f g : K)) hq
  simp only [mul_apply, Units.val_mul, one_apply, Units.val_one] at h
  exact (mul_self_eq_one_iff.mp h).imp Units.val_eq_one.mp Units.val_eq_neg_one.mp

/-- Away from characteristic `2`, a character whose square is trivial is nontrivial at `g`
exactly when its value there is `-1`. -/
theorem apply_ne_one_iff_of_mul_self_eq_one {G K : Type*} [Monoid G] [CommRing K]
    [IsDomain K] [NeZero (2 : K)] (q : G →* Kˣ) (hq : q * q = 1) (g : G) :
    q g ≠ 1 ↔ (q g : K) = -1 := by
  rw [Units.val_eq_neg_one]
  refine ⟨(q.apply_eq_one_or_eq_neg_one_of_mul_self_eq_one hq g).resolve_left, ?_⟩
  rintro h h₁
  have h' : (1 : K) = -1 := by simpa [h₁] using congrArg Units.val h
  refine two_ne_zero (α := K) ?_
  calc (2 : K) = 1 + 1 := one_add_one_eq_two.symm
    _ = 1 + -1 := by rw [← h']
    _ = 0 := add_neg_cancel 1

/-- The mean of a linear character off the kernel of a nontrivial quadratic character `q`.
Only the trivial character and `q` have nonzero mean there. -/
theorem expect_filter_apply_ne_one_apply_of_mul_self_eq_one {G K : Type*} [Group G] [Fintype G]
    [Field K] [CharZero K] (q χ : G →* Kˣ) [DecidablePred fun g ↦ q g ≠ 1]
    [Decidable (χ = 1)] [Decidable (χ = q)] (hq : q * q = 1) (hq₁ : q ≠ 1) :
    (𝔼 g with q g ≠ 1, (χ g : K)) = if χ = 1 then 1 else if χ = q then -1 else 0 := by
  classical
  have hcomp (ψ : G →* Kˣ) : (Units.coeHom K).comp ψ = 1 ↔ ψ = 1 := by
    simp only [DFunLike.ext_iff, comp_apply, one_apply, Units.coeHom_apply, Units.val_eq_one]
  have htwice (ψ : G →* Kˣ) :
      2 * (∑ g with q g ≠ 1, (ψ g : K)) =
        (∑ g, (Units.coeHom K).comp ψ g) - ∑ g, (Units.coeHom K).comp (q * ψ) g := by
    simp only [comp_apply, Units.coeHom_apply]
    rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : q g = 1
    · simp [hg]
    · simp [hg, (q.apply_ne_one_iff_of_mul_self_eq_one hq g).mp hg, two_mul]
  have hcard : 2 * ((Finset.univ.filter fun g ↦ q g ≠ 1).card : K) = Fintype.card G := by
    have h := htwice 1
    rw [mul_one q, sum_hom_units_eq_zero _ ((hcomp q).not.mpr hq₁)] at h
    simpa using h
  have hne : ((Finset.univ.filter fun g ↦ q g ≠ 1).card : K) ≠ 0 := by
    intro hz
    exact (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := G)) :
      (Fintype.card G : K) ≠ 0) (by simpa [hz] using hcard.symm)
  have hmul : q * χ = 1 ↔ χ = q :=
    ⟨fun h ↦ mul_left_cancel (h.trans hq.symm), fun h ↦ h ▸ hq⟩
  rw [Finset.expect_eq_sum_div_card, div_eq_iff hne]
  have hh := htwice χ
  rw [sum_hom_units, sum_hom_units] at hh
  simp only [hcomp, hmul, Nat.cast_ite, Nat.cast_zero, ← hcard] at hh
  apply mul_left_cancel₀ (two_ne_zero : (2 : K) ≠ 0)
  rw [hh]
  by_cases h₁ : χ = 1
  · subst χ
    simp [Ne.symm hq₁]
  · by_cases h₂ : χ = q <;> simp [h₁, h₂, hq₁, mul_neg]

end MonoidHom
