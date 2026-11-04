/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Basic
public import TauCeti.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.RingTheory.Norm.Quadratic

/-!
# Norms from the Gaussian rational field

For `E = ℚ(i)`, a nonzero rational number is a norm from `E` exactly when it is positive and
its valuation at each prime congruent to `3` modulo `4` is even. Thus the rational norm quotient
is detected by the real sign and these valuation parities: two units represent the same class
exactly when their quotient is positive and their valuations have even differences.

The criterion follows from the quadratic norm equation and the rational two-square theorem.
The cyclic Hasse norm theorem then identifies the same explicit conditions with solvability of
the norm equation at all finite and infinite completions. The sign coordinate is essential in
this valuation-parity description: `-1` is not a norm, although every valuation is even.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 (the Hasse norm theorem).
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Chapter XX
  (sums of two squares).
-/

public noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

variable {E : Type} [Field E] [CharZero E] [IsCyclotomicExtension {4} ℚ E]

local instance : FiniteDimensional ℚ E :=
  IsCyclotomicExtension.finiteDimensional {4} ℚ E

/-- A nonzero rational number is a norm from `ℚ(i)` exactly when it is positive and has even
valuation at every prime congruent to `3` modulo `4`. -/
theorem mem_normGroup_Qi_iff (a : ℚˣ) :
    a ∈ normGroup ℚ E ↔
      0 < (a : ℚ) ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p (a : ℚ)) := by
  let : Algebra.IsQuadraticExtension ℚ E :=
    ⟨(IsCyclotomicExtension.Rat.finrank 4 E).trans (by decide)⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ E
    (by simp : 4 ∈ ({4} : Set ℕ)) (by norm_num : (4 : ℕ) ≠ 0)
  have hζrange : ζ ∉ Set.range (algebraMap ℚ E) := by
    rintro ⟨q, hq⟩
    have hq2 : q ^ 2 = (-1 : ℚ) := (algebraMap ℚ E).injective (by
      simpa only [map_pow, map_neg, map_one, hq] using hζ.sq_eq_neg_one)
    nlinarith [sq_nonneg q]
  rw [mem_normGroup_iff_exists_sq_sub_mul_sq E hζrange
    (by simpa using hζ.sq_eq_neg_one : ζ ^ 2 = algebraMap ℚ E (-1)) a]
  simp only [neg_mul, one_mul, sub_neg_eq_add]
  exact Rat.eq_sq_add_sq_iff.trans (and_congr_left fun _ ↦
    le_iff_lt_or_eq.trans (or_iff_left (Ne.symm a.ne_zero)))

/-- Two nonzero rationals have the same class modulo norms from `ℚ(i)` exactly when they have
the same real sign and even differences of valuations at primes congruent to `3` modulo `4`. -/
theorem normQuotient_Qi_eq_iff (a b : ℚˣ) :
    (QuotientGroup.mk a : ℚˣ ⧸ normGroup ℚ E) = QuotientGroup.mk b ↔
      0 < (a : ℚ) / (b : ℚ) ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 →
        Even (padicValRat p (a : ℚ) - padicValRat p (b : ℚ)) := by
  rw [QuotientGroup.eq_iff_div_mem, mem_normGroup_Qi_iff]
  simp only [Units.val_div_eq_div_val]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.div a.ne_zero b.ne_zero]

/-- In the Gaussian rational extension, being a norm at every finite and infinite place is
exactly positivity together with even valuations at primes congruent to `3` modulo `4`.
The positivity condition records the real norm obstruction. -/
theorem isLocalNormEverywhere_Qi_iff [NumberField E] (a : ℚˣ) :
    GlobalNumberFields.IsLocalNormEverywhere ℚ E a ↔
      0 < (a : ℚ) ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p (a : ℚ)) := by
  let : IsGalois ℚ E := IsCyclotomicExtension.isGalois {4} ℚ E
  let : IsCyclic (E ≃ₐ[ℚ] E) := isCyclic_of_prime_card (p := 2) (by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank 4 E]
    decide)
  exact (isGlobalNorm_iff_isLocalNormEverywhere ℚ E a).symm.trans (mem_normGroup_Qi_iff a)

/- The real obstruction and the inert prime `3` give distinct nontrivial norm classes;
`2`, the ramified prime, is a norm. -/
example : (-1 : ℚˣ) ∉ normGroup ℚ E := by
  rw [mem_normGroup_Qi_iff]
  norm_num

example : Units.mk0 (3 : ℚ) (by norm_num) ∉ normGroup ℚ E := by
  intro h
  have hp := (mem_normGroup_Qi_iff _).1 h |>.2 3 Nat.prime_three rfl
  have hval : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  simp only [Units.val_mk0] at hp
  norm_num [hval] at hp

example : Units.mk0 (2 : ℚ) (by norm_num) ∈ normGroup ℚ E := by
  apply (mem_normGroup_Qi_iff _).2
  exact ⟨by norm_num, (Rat.eq_sq_add_sq_iff.1 ⟨1, 1, by norm_num⟩).2⟩

end TauCeti.ClassFieldTheory
