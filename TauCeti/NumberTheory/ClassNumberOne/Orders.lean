/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassNumberOne.HeegnerNumbers
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.ClassNumberOne
import TauCeti.NumberTheory.ClassNumberOne.SmallDiscriminant
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The thirteen imaginary quadratic orders of class number one

Every order `O` of an imaginary quadratic field `K` is `O_f = ℤ + f 𝓞 K` for its index `f`, of
discriminant `f² D` with `D = disc K` a negative fundamental discriminant. By Cox's formula,
`O_f` has trivial Picard group exactly when `h(K) = 1` and `(D, f)` passes the conductor test:
either `f = 1`, or `f = 2` and `D ≡ 1 (mod 8)`, or `D = -3` and `f ∈ {2, 3}`, or `D = -4` and
`f = 2` (`TauCeti.GlobalNumberFields.NumberFieldOrder.card_pic_eq_one_iff`).

The thirteen discriminants `-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163` are the
values `f² D` for which `D` is one of the nine discriminants `-n`, `n ∈ heegnerDiscriminants`, of
the imaginary quadratic fields known to have class number one, and `(D, f)` passes the conductor
test. This file proves that comparison: an integer `f² D` with `D` a negative fundamental
discriminant is among the thirteen iff `D` is among the nine and `(D, f)` passes the conductor
test. In particular each of the thirteen values has a unique such decomposition `f² D`: besides
the nine fundamental ones, `-12 = 2² · (-3)`, `-16 = 2² · (-4)`, `-27 = 3² · (-3)` and
`-28 = 2² · (-7)`.

Consequently every order whose discriminant is one of the thirteen has trivial Picard group and
lies in one of the nine fields, and in each of the nine fields, as in every imaginary quadratic
field of discriminant greater than `-51`, the orders of trivial Picard group are exactly those
whose discriminant is one of the thirteen. Together with the theorem that the nine fields are the
only imaginary quadratic fields of class number one, the criterion `card_pic_eq_one_iff` and the
comparison `exists_discr_eq_neg_mem_classNumberOneOrderDiscriminants_iff` classify all imaginary
quadratic orders of class number one.

## Main definitions

* `TauCeti.classNumberOneOrderDiscriminants`: the absolute values
  `3, 4, 7, 8, 11, 12, 16, 19, 27, 28, 43, 67, 163` of the thirteen discriminants.

## Main results

* `TauCeti.sq_mul_mem_classNumberOneOrderDiscriminants_iff`: for a fundamental discriminant `-n`
  and every `f`, `f² n` is one of the thirteen values iff `n ∈ heegnerDiscriminants` and `(-n, f)`
  passes the conductor test.

In the namespace `TauCeti.GlobalNumberFields.NumberFieldOrder`, for an order `O` of a quadratic
field `K`:

* `exists_discr_eq_neg_mem_classNumberOneOrderDiscriminants_iff`: the discriminant of `O` is one
  of the thirteen iff `disc K` is one of the nine and the index of `O` and `disc K` pass the
  conductor test.
* `card_pic_eq_one_of_mem_classNumberOneOrderDiscriminants`: if the discriminant of `O` is one of
  the thirteen, then `O` has trivial Picard group.
* `card_pic_eq_one_iff_of_mem_heegnerDiscriminants`,
  `card_pic_eq_one_iff_of_neg_fifty_one_lt_discr`: if `disc K` is one of the nine, or greater
  than `-51`, then `O` has trivial Picard group iff its discriminant is one of the thirteen.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (Theorem 7.24 and the orders of class number
  one).
-/

public section

open Module NumberField

namespace TauCeti

/-- The absolute values `3, 4, 7, 8, 11, 12, 16, 19, 27, 28, 43, 67, 163` of the discriminants of
the thirteen imaginary quadratic orders of class number one: these orders have discriminant `-n`
for `n` in this set. Besides the nine field discriminants of `heegnerDiscriminants`, it contains
the discriminants `-12 = 2² · (-3)`, `-16 = 2² · (-4)`, `-27 = 3² · (-3)` and `-28 = 2² · (-7)` of
four nonmaximal orders. That every order with one of these discriminants has class number one is
`NumberFieldOrder.card_pic_eq_one_of_mem_classNumberOneOrderDiscriminants`. -/
def classNumberOneOrderDiscriminants : Finset ℕ :=
  {3, 4, 7, 8, 11, 12, 16, 19, 27, 28, 43, 67, 163}

/-- Membership in `classNumberOneOrderDiscriminants`, spelled out. -/
@[simp] theorem mem_classNumberOneOrderDiscriminants {n : ℕ} :
    n ∈ classNumberOneOrderDiscriminants ↔
      n = 3 ∨ n = 4 ∨ n = 7 ∨ n = 8 ∨ n = 11 ∨ n = 12 ∨ n = 16 ∨ n = 19 ∨ n = 27 ∨ n = 28 ∨
        n = 43 ∨ n = 67 ∨ n = 163 := by
  simp [classNumberOneOrderDiscriminants]

/-- **The thirteen order discriminants as `f² D`.** Let `-n` be a fundamental discriminant and
`f` a natural number. Then `f² n` is one of the thirteen values of
`classNumberOneOrderDiscriminants` iff `n` is one of the nine values of `heegnerDiscriminants` and
either `f = 1`, or `f = 2` and `-n ≡ 1 (mod 8)`, or `n = 3` and `f ∈ {2, 3}`, or `n = 4` and
`f = 2`. -/
theorem sq_mul_mem_classNumberOneOrderDiscriminants_iff {f n : ℕ}
    (hn : Int.IsFundamentalDiscr (-(n : ℤ))) :
    f ^ 2 * n ∈ classNumberOneOrderDiscriminants ↔ n ∈ heegnerDiscriminants ∧
      (f = 1 ∨ (f = 2 ∧ n % 8 = 7) ∨ (n = 3 ∧ (f = 2 ∨ f = 3)) ∨ (n = 4 ∧ f = 2)) := by
  simp only [mem_classNumberOneOrderDiscriminants, mem_heegnerDiscriminants]
  refine ⟨fun h ↦ ?_, fun ⟨hn9, hf⟩ ↦ ?_⟩
  · -- The quotients `m / f²` of the thirteen values `m` that are not fundamental discriminants.
    have hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 12 ∧ n ≠ 16 ∧ n ≠ 27 ∧ n ≠ 28 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hn <;> decide +kernel
    have hn0 : n ≠ 0 := by rintro rfl; exact hn.ne_zero (by simp)
    have hf13 : f < 13 := by
      by_contra! hf13
      have : 169 ≤ f ^ 2 * n := by nlinarith [Nat.one_le_iff_ne_zero.mpr hn0]
      omega
    interval_cases f <;> omega
  · rcases hf with rfl | ⟨rfl, h8⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> omega

end TauCeti

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

/-- **Orders with one of the thirteen discriminants.** The discriminant of an order `O` of a
quadratic field `K` with discriminant `D` is one of the thirteen values `-m`,
`m ∈ classNumberOneOrderDiscriminants`, iff `D` is one of the nine values `-n`,
`n ∈ heegnerDiscriminants`, and either `O` is maximal, or `O` has index `2` and `D ≡ 1 (mod 8)`,
or `D = -3` and `O` has index `2` or `3`, or `D = -4` and `O` has index `2`. -/
theorem exists_discr_eq_neg_mem_classNumberOneOrderDiscriminants_iff (hK : finrank ℚ K = 2)
    (O : NumberFieldOrder K) :
    (∃ m ∈ classNumberOneOrderDiscriminants, O.discr = -m) ↔
      (∃ n ∈ heegnerDiscriminants, NumberField.discr K = -n) ∧
        (O.index = 1 ∨ (O.index = 2 ∧ NumberField.discr K % 8 = 1) ∨
          (NumberField.discr K = -3 ∧ (O.index = 2 ∨ O.index = 3)) ∨
            (NumberField.discr K = -4 ∧ O.index = 2)) := by
  rcases lt_or_ge (NumberField.discr K) 0 with hneg | hpos
  swap
  · -- Over a real quadratic field both discriminants are positive, and both sides fail.
    have hO : 0 ≤ O.discr := by rw [discr_eq_index_sq_mul]; positivity
    refine iff_of_false (fun ⟨m, hm, h⟩ ↦ ?_) (fun ⟨⟨n, hn, h⟩, _⟩ ↦ ?_)
    · simp only [mem_classNumberOneOrderDiscriminants] at hm; omega
    · simp only [mem_heegnerDiscriminants] at hn; omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, NumberField.discr K = -n := ⟨(NumberField.discr K).natAbs, by omega⟩
  have hfund : Int.IsFundamentalDiscr (-n) := hn ▸ Multiquadratic.isFundamentalDiscr_discr hK
  have hO : O.discr = -((O.index ^ 2 * n : ℕ) : ℤ) := by
    rw [discr_eq_index_sq_mul, hn]; push_cast; ring
  have hm : (∃ m ∈ classNumberOneOrderDiscriminants, O.discr = -m) ↔
      O.index ^ 2 * n ∈ classNumberOneOrderDiscriminants := by
    simp only [hO, neg_inj, Nat.cast_inj]
    exact ⟨fun ⟨_, hm, h⟩ ↦ h ▸ hm, fun h ↦ ⟨_, h, rfl⟩⟩
  have hD : (∃ n' ∈ heegnerDiscriminants, NumberField.discr K = -n') ↔
      n ∈ heegnerDiscriminants := by
    simp only [hn, neg_inj, Nat.cast_inj]
    exact ⟨fun ⟨_, hm, h⟩ ↦ h ▸ hm, fun h ↦ ⟨_, h, rfl⟩⟩
  rw [hm, hD, sq_mul_mem_classNumberOneOrderDiscriminants_iff hfund, hn]
  exact and_congr_right fun _ ↦ by omega

/-- **The orders of class number one in the nine fields.** In a quadratic field whose
discriminant is one of the nine values `-n`, `n ∈ heegnerDiscriminants`, an order has trivial
Picard group iff its discriminant is one of the thirteen values `-m`,
`m ∈ classNumberOneOrderDiscriminants`. -/
theorem card_pic_eq_one_iff_of_mem_heegnerDiscriminants (hK : finrank ℚ K = 2)
    (O : NumberFieldOrder K) {n : ℕ} (hn : n ∈ heegnerDiscriminants)
    (hD : NumberField.discr K = -n) :
    Nat.card (Pic O) = 1 ↔ ∃ m ∈ classNumberOneOrderDiscriminants, O.discr = -m := by
  have : IsTotallyComplex K := .of_discr_lt_zero (by
    simp only [mem_heegnerDiscriminants] at hn; omega) hK
  rw [card_pic_eq_one_iff hK, exists_discr_eq_neg_mem_classNumberOneOrderDiscriminants_iff hK,
    NumberField.classNumber_eq_one_of_mem_heegnerDiscriminants hK hD hn]
  exact and_congr_left fun _ ↦ iff_of_true rfl ⟨n, hn, hD⟩

/-- **The thirteen orders have class number one.** An order of a quadratic field whose
discriminant is one of `-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163` has trivial
Picard group. -/
theorem card_pic_eq_one_of_mem_classNumberOneOrderDiscriminants (hK : finrank ℚ K = 2)
    (O : NumberFieldOrder K) {m : ℕ} (hm : m ∈ classNumberOneOrderDiscriminants)
    (hO : O.discr = -m) : Nat.card (Pic O) = 1 := by
  obtain ⟨⟨n, hn, hD⟩, -⟩ :=
    (exists_discr_eq_neg_mem_classNumberOneOrderDiscriminants_iff hK O).mp ⟨m, hm, hO⟩
  exact (card_pic_eq_one_iff_of_mem_heegnerDiscriminants hK O hn hD).mpr ⟨m, hm, hO⟩

/-- **The orders of class number one above discriminant `-51`.** In an imaginary quadratic field
of discriminant greater than `-51`, an order has trivial Picard group iff its discriminant is one
of the thirteen values `-m`, `m ∈ classNumberOneOrderDiscriminants`. -/
theorem card_pic_eq_one_iff_of_neg_fifty_one_lt_discr [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (O : NumberFieldOrder K) (h51 : -51 < NumberField.discr K) :
    Nat.card (Pic O) = 1 ↔ ∃ m ∈ classNumberOneOrderDiscriminants, O.discr = -m := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, NumberField.discr K = -n :=
    ⟨(NumberField.discr K).natAbs, by have := IsTotallyComplex.discr_lt_zero hK; omega⟩
  rw [card_pic_eq_one_iff hK, exists_discr_eq_neg_mem_classNumberOneOrderDiscriminants_iff hK,
    TauCeti.NumberField.classNumber_eq_one_iff_of_neg_fifty_one_lt_discr hK hn h51]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ⟨n, h, hn⟩, fun ⟨n', hn', h⟩ ↦ ?_⟩
  obtain rfl : n = n' := by omega
  exact hn'

end TauCeti.GlobalNumberFields.NumberFieldOrder
