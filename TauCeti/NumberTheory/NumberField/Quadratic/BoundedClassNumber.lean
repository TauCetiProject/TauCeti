/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Filter.AtTopBot.Basic
public import TauCeti.NumberTheory.BinaryQuadraticForm.PrimitiveReduced
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
import TauCeti.NumberTheory.ClassNumberOne.HeegnerNumbers
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.Model
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.NumberTheory.NumberField.Quadratic.Siegel
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Imaginary quadratic fields of bounded class number

By Siegel's theorem, an imaginary quadratic field of class number at most `B` has discriminant
bounded in terms of `B` (`TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le`). This
file draws the finiteness consequences, in the three usual parametrizations of imaginary quadratic
fields:

* by negative fundamental discriminants `-n`, through the model `ℚ(√(-n))`, whose discriminant is
  `-n` (`QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr`);
* by negative squarefree radicands `-n`, through the same model, whose discriminant is `-n` or
  `-4n`;
* up to `ℚ`-algebra isomorphism: every imaginary quadratic field is isomorphic to `ℚ(√(-n))` for a
  unique squarefree `n` (`NumberField.existsUnique_neg_squarefree_algEquiv`), and isomorphic fields
  have the same class number.

Equivalently, the class number `h(-n)` of a negative fundamental discriminant `-n`, which is the
number of primitive reduced forms of discriminant `-n`
(`TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms`), tends to infinity with
`n`, and each value of the class number is taken by only finitely many fundamental discriminants.
All bounds here are ineffective, because the constant in Siegel's theorem is.

The field `ℚ(√-163)` of class number one shows how far the constants of Siegel's bounds are
constrained: a discriminant bound valid for class number one is at least `163`, and the constant
`C` of `h(K) ≥ C |disc K| ^ (1 / 2 - ε)` is at most `163 ^ (ε - 1 / 2)`.

## Main results

* `TauCeti.NumberField.finite_setOf_isFundamentalDiscr_classNumber_le`: there are finitely many
  negative fundamental discriminants `-n` with `h(ℚ(√(-n))) ≤ B`.
* `TauCeti.NumberField.finite_setOf_isFundamentalDiscr_classNumber_eq`: the same for
  `h(ℚ(√(-n))) = h`.
* `TauCeti.NumberField.finite_setOf_squarefree_classNumber_le`: there are finitely many
  squarefree `n > 0` with `h(ℚ(√(-n))) ≤ B`.
* `TauCeti.NumberField.exists_finset_nonempty_algEquiv_of_classNumber_le`: the imaginary quadratic
  fields of class number at most `B` lie in finitely many isomorphism classes.
* `TauCeti.NumberField.tendsto_card_primitiveReducedForms_atTop`: `h(-n) → ∞` as `n → ∞` through
  the fundamental discriminants `-n`.
* `TauCeti.NumberField.le_of_forall_abs_discr_le_of_classNumber_le_one`,
  `TauCeti.NumberField.le_rpow_of_forall_mul_rpow_le_classNumber`: the constraints on the
  constants imposed by `ℚ(√-163)`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
* D. A. Cox, *Primes of the Form x² + ny²*, §2 and §7.
-/

public section

open Module NumberField Filter
open scoped Finset

namespace TauCeti.NumberField

/-- For every `B` there is `N` such that the model `ℚ(√(-n))` has `|disc| ≤ N` whenever its class
number is at most `B`. -/
private theorem exists_natAbs_discr_le (B : ℕ) : ∃ N : ℕ, ∀ (n : ℕ) [NeZero n],
    classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) ≤ B →
      (discr (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)).natAbs ≤ N := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  refine ⟨⌊C⌋₊, fun n _ hB ↦ Nat.le_floor ?_⟩
  have : IsTotallyComplex (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by simpa using NeZero.pos n)
  rw [Nat.cast_natAbs, Int.cast_abs]
  exact hC _ (QuadraticAlgebra.finrank_eq_two _ _) hB

/-- **Finitely many fundamental discriminants of bounded class number.** For every `B`, only
finitely many negative fundamental discriminants `-n` have `h(ℚ(√(-n))) ≤ B`. The proof goes
through Siegel's theorem and gives no bound on the size of this set. -/
theorem finite_setOf_isFundamentalDiscr_classNumber_le (B : ℕ) :
    {n : ℕ | ∃ _ : NeZero n, Int.IsFundamentalDiscr (-n) ∧
      classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨N, hN⟩ := exists_natAbs_discr_le B
  refine (Set.finite_Iic N).subset fun n ⟨_, hD, hB⟩ ↦ ?_
  have := hN n hB
  rwa [QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr.mpr hD, Int.natAbs_neg,
    Int.natAbs_natCast] at this

/-- **Each class number is taken finitely often.** For every `h`, only finitely many negative
fundamental discriminants `-n` have `h(ℚ(√(-n))) = h`. -/
theorem finite_setOf_isFundamentalDiscr_classNumber_eq (h : ℕ) :
    {n : ℕ | ∃ _ : NeZero n, Int.IsFundamentalDiscr (-n) ∧
      classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) = h}.Finite :=
  (finite_setOf_isFundamentalDiscr_classNumber_le h).subset fun _ ⟨hn, hD, he⟩ ↦ ⟨hn, hD, he.le⟩

/-- **Finitely many squarefree radicands of bounded class number.** For every `B`, only finitely
many squarefree `n > 0` have `h(ℚ(√(-n))) ≤ B`. The discriminant of `ℚ(√(-n))` is `-n` or `-4n`,
so this follows from Siegel's discriminant bound. -/
theorem finite_setOf_squarefree_classNumber_le (B : ℕ) :
    {n : ℕ | ∃ _ : NeZero n, Squarefree n ∧
      classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) ≤ B}.Finite := by
  obtain ⟨N, hN⟩ := exists_natAbs_discr_le B
  refine (Set.finite_Iic N).subset fun n ⟨_, hsf, hB⟩ ↦ (le_trans ?_ (hN n hB))
  have hsf' : Squarefree (-(n : ℤ)) := Int.squarefree_natAbs.mp (by simpa using hsf)
  by_cases h4 : -(n : ℤ) % 4 = 1
  · rw [QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf' h4, Int.natAbs_neg, Int.natAbs_natCast]
  · rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hsf' h4, Int.natAbs_mul,
      Int.natAbs_neg, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_left n (by decide)

/-- **Finitely many imaginary quadratic fields of bounded class number.** For every `B` there is a
finite set `S` such that every imaginary quadratic field of class number at most `B` is isomorphic
to `ℚ(√(-n))` for some `n ∈ S`. -/
theorem exists_finset_nonempty_algEquiv_of_classNumber_le (B : ℕ) :
    ∃ S : Finset ℕ, ∀ (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K],
      finrank ℚ K = 2 → classNumber K ≤ B →
        ∃ n ∈ S, Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) := by
  refine ⟨(finite_setOf_squarefree_classNumber_le B).toFinset, fun K _ _ _ hK hB ↦ ?_⟩
  obtain ⟨d, ⟨hd, hsf, ⟨e⟩⟩, -⟩ := existsUnique_neg_squarefree_algEquiv hK
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hd.le
  have : NeZero n := ⟨by rintro rfl; simp at hd⟩
  refine ⟨n, ?_, ⟨e⟩⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨inferInstance, by simpa using Int.squarefree_natAbs.mpr hsf,
    (RingEquiv.classNumber_eq e.toRingEquiv).symm.trans_le hB⟩

/-- **Siegel: the class number tends to infinity.** As `n → ∞` through the negative fundamental
discriminants `-n`, the class number `h(-n)`, the number of primitive reduced forms of
discriminant `-n`, tends to infinity. For fundamental `-n` this is the class number of
`ℚ(√(-n))` (`TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms`). -/
theorem tendsto_card_primitiveReducedForms_atTop :
    Tendsto (fun n ↦ #(primitiveReducedForms n))
      (atTop ⊓ 𝓟 {n | Int.IsFundamentalDiscr (-n)}) atTop := by
  refine tendsto_atTop.mpr fun B ↦ ?_
  obtain ⟨N, hN⟩ := (finite_setOf_isFundamentalDiscr_classNumber_le B).bddAbove
  rw [eventually_inf_principal]
  filter_upwards [eventually_gt_atTop N] with n hn hD
  have : NeZero n := ⟨by omega⟩
  rw [← BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms n hD]
  by_contra! h
  exact (hN ⟨inferInstance, hD, h.le⟩).not_gt hn

/-- The model `ℚ(√-163)` is totally complex, with discriminant `-163` and class number one. -/
private theorem isTotallyComplex_and_discr_and_classNumber_neg_one_hundred_sixty_three :
    IsTotallyComplex (QuadraticAlgebra ℚ ((-(163 : ℕ) : ℤ) : ℚ) 0) ∧
      discr (QuadraticAlgebra ℚ ((-(163 : ℕ) : ℤ) : ℚ) 0) = -163 ∧
        classNumber (QuadraticAlgebra ℚ ((-(163 : ℕ) : ℤ) : ℚ) 0) = 1 :=
  have hmem : 163 ∈ heegnerDiscriminants := by simp
  ⟨QuadraticAlgebra.isTotallyComplex_iff.mpr (by norm_num),
    QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr.mpr
    (isFundamentalDiscr_neg_of_mem_heegnerDiscriminants hmem),
    classNumber_neg_eq_one_of_mem_heegnerDiscriminants hmem⟩

/-- **A discriminant bound for class number one is at least `163`.** If every imaginary quadratic
field of class number one has `|disc K| ≤ C`, as `imaginary_discr_bounded_of_classNumber_le` gives
for `B = 1`, then `163 ≤ C`, because `ℚ(√-163)` has class number one. -/
theorem le_of_forall_abs_discr_le_of_classNumber_le_one {C : ℝ}
    (h : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], finrank ℚ K = 2 →
      classNumber K ≤ 1 → |(discr K : ℝ)| ≤ C) : 163 ≤ C := by
  obtain ⟨_, hD, hh⟩ := isTotallyComplex_and_discr_and_classNumber_neg_one_hundred_sixty_three
  have := h (QuadraticAlgebra ℚ ((-(163 : ℕ) : ℤ) : ℚ) 0)
    (QuadraticAlgebra.finrank_eq_two _ _) hh.le
  rw [hD] at this
  norm_num at this
  exact this

/-- **The constant of Siegel's class-number bound is at most `163 ^ (ε - 1 / 2)`.** If every
imaginary quadratic field has `C |disc K| ^ (1 / 2 - ε) ≤ h(K)`, as
`imaginary_classNumber_lower_bound` gives, then `C ≤ 163 ^ (ε - 1 / 2)`, because `ℚ(√-163)` has
class number one. -/
theorem le_rpow_of_forall_mul_rpow_le_classNumber {ε C : ℝ}
    (h : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], finrank ℚ K = 2 →
      C * |(discr K : ℝ)| ^ (1 / 2 - ε) ≤ classNumber K) : C ≤ 163 ^ (ε - 1 / 2) := by
  obtain ⟨_, hD, hh⟩ := isTotallyComplex_and_discr_and_classNumber_neg_one_hundred_sixty_three
  have := h (QuadraticAlgebra ℚ ((-(163 : ℕ) : ℤ) : ℚ) 0)
    (QuadraticAlgebra.finrank_eq_two _ _)
  rw [hD, hh] at this
  norm_num at this
  rw [← neg_sub, Real.rpow_neg (by norm_num), ← one_div, le_div_iff₀ (by positivity)]
  exact this

end TauCeti.NumberField
