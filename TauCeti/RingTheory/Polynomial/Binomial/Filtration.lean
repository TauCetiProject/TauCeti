/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Binomial.Basis
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.CharP.Algebra

/-!
# The integral degree filtration of the binomial polynomials

The integral span of the polynomials `(X choose i)` inherits the polynomial degree
filtration. Its stage of degree at most `n` is free on exactly the first `n + 1`
binomial polynomials: no cancellation of higher integral coefficients can lower degree.
This supplies finite free order stages for the toral factors of integral enveloping
algebras, including central toral directions.

`ringChooseDegreeLE` is defined by the finite integral span, and
`mem_ringChooseDegreeLE_iff` identifies it with the intersection with the ordinary
polynomial degree filtration. `ringChooseDegreeLEBasis` gives its integral basis.
Multiplication adds the degree bounds, and the union is the full integral binomial span.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
-/

public section

namespace TauCeti

open Polynomial Submodule

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance] BinomialRing.toHasUniqueDiv

variable (K : Type*) [Ring K] [Algebra ℚ K]

/-- The integral span of the binomial polynomials of degree at most `n`. -/
noncomputable def ringChooseDegreeLE (n : ℕ) : Submodule ℤ K[X] :=
  span ℤ (Ring.choose (X : K[X]) '' Set.Iic n)

/-- The finite-span definition of the integral degree stage. -/
theorem ringChooseDegreeLE_def (n : ℕ) :
    ringChooseDegreeLE K n = span ℤ (Ring.choose (X : K[X]) '' Set.Iic n) := (rfl)

/-- Each binomial polynomial belongs to every integral degree stage above its index. -/
theorem ringChoose_X_mem_ringChooseDegreeLE {i n : ℕ} (hi : i ≤ n) :
    Ring.choose (X : K[X]) i ∈ ringChooseDegreeLE K n :=
  subset_span ⟨i, hi, rfl⟩

variable [Nontrivial K]

/-- Degree bounds on an integral binomial expansion are exactly bounds on its support. -/
theorem degree_sum_ringChoose_X_le_iff (a : ℕ →₀ ℤ) (n : ℕ) :
    (a.sum (fun i z => z • Ring.choose (X : K[X]) i)).degree ≤ n ↔
      ∀ i ∈ a.support, i ≤ n := by
  classical
  have : CharZero K := algebraRat.charZero K
  rw [← mem_degreeLE, ← span_binomialPolynomialBasis_image_Iic_eq_degreeLE K n,
    (binomialPolynomialBasis K).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    Set.mem_Iic, binomialPolynomialBasis_repr_sum_zsmul, Int.cast_ne_zero]

/-- The finite integral span is exactly the full integral binomial span intersected
with the polynomial degree bound. This also covers the zero polynomial. -/
@[simp]
theorem mem_ringChooseDegreeLE_iff (p : K[X]) (n : ℕ) :
    p ∈ ringChooseDegreeLE K n ↔ p ∈ ringChooseSpan (X : K[X]) ∧ p.degree ≤ n := by
  classical
  constructor
  · intro hp
    have hspan : ringChooseDegreeLE K n ≤ (ringChooseSpan (X : K[X])).toIntSubmodule := by
      rw [ringChooseDegreeLE_def, span_le]
      rintro _ ⟨i, _, rfl⟩
      exact ringChoose_mem_ringChooseSpan _ _
    refine ⟨hspan hp, ?_⟩
    have hdegree : ringChooseDegreeLE K n ≤ (degreeLE K n).restrictScalars ℤ := by
      rw [ringChooseDegreeLE_def, span_le]
      rintro _ ⟨i, hi, rfl⟩
      apply (mem_degreeLE).mpr
      simpa only [degree_ringChoose_X, Nat.cast_le, Set.mem_Iic] using hi
    exact (mem_degreeLE).mp (hdegree hp)
  · rintro ⟨hp, hdegree⟩
    obtain ⟨a, ha, _⟩ := (mem_ringChooseSpan_X_iff_existsUnique K p).mp hp
    rw [← ha] at hdegree ⊢
    have hs := (degree_sum_ringChoose_X_le_iff K a n).mp hdegree
    exact sum_mem fun i hi => (ringChooseDegreeLE K n).smul_mem (a i)
      (ringChoose_X_mem_ringChooseDegreeLE K (hs i hi))

omit [Nontrivial K] in
/-- The degree-zero stage consists of the integral multiples of the unit polynomial. -/
@[simp]
theorem ringChooseDegreeLE_zero : ringChooseDegreeLE K 0 = span ℤ {(1 : K[X])} := by
  have hi : Set.Iic (0 : ℕ) = {0} := by ext i; simp
  simp [ringChooseDegreeLE_def, hi]

omit [Nontrivial K] in
/-- The degree stages are increasing. -/
theorem ringChooseDegreeLE_mono : Monotone (ringChooseDegreeLE K) := by
  intro m n h
  rw [ringChooseDegreeLE_def, ringChooseDegreeLE_def]
  exact span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr h))

omit [Nontrivial K] in
/-- The range-indexed form of the finite integral span. -/
private theorem ringChooseDegreeLE_eq_span_range (n : ℕ) :
    ringChooseDegreeLE K n =
      span ℤ (Set.range fun i : Fin (n + 1) => Ring.choose (X : K[X]) i.val) := by
  rw [ringChooseDegreeLE_def]
  congr 1
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, Nat.le_of_lt_succ i.isLt, rfl⟩

/-- The first `n + 1` binomial polynomials form an integral basis of the degree stage. -/
noncomputable def ringChooseDegreeLEBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) ℤ (ringChooseDegreeLE K n) :=
  (Module.Basis.span ((linearIndependent_ringChoose_X_int K).comp
    (fun i : Fin (n + 1) => i.val) Fin.val_injective)).map
      (LinearEquiv.ofEq _ _ (ringChooseDegreeLE_eq_span_range K n).symm)

/-- The finite-stage basis has the stated binomial-polynomial values. -/
@[simp]
theorem coe_ringChooseDegreeLEBasis_apply (n : ℕ) (i : Fin (n + 1)) :
    (ringChooseDegreeLEBasis K n i : K[X]) = Ring.choose X i.val := by
  simp [ringChooseDegreeLEBasis]

/-- Every integral degree stage is a finite module over the integers. -/
instance (n : ℕ) : Module.Finite ℤ (ringChooseDegreeLE K n) :=
  Module.Finite.of_basis (ringChooseDegreeLEBasis K n)

/-- Every integral degree stage is free over the integers. -/
instance (n : ℕ) : Module.Free ℤ (ringChooseDegreeLE K n) :=
  Module.Free.of_basis (ringChooseDegreeLEBasis K n)

/-- The integral rank of the degree-`n` stage is `n + 1`. -/
@[simp]
theorem finrank_ringChooseDegreeLE (n : ℕ) :
    Module.finrank ℤ (ringChooseDegreeLE K n) = n + 1 := by
  simpa using Module.finrank_eq_card_basis (ringChooseDegreeLEBasis K n)

/-- Every element of the integral binomial span lies in a finite degree stage. -/
theorem mem_ringChooseSpan_X_iff_exists_mem_ringChooseDegreeLE (p : K[X]) :
    p ∈ ringChooseSpan (X : K[X]) ↔ ∃ n, p ∈ ringChooseDegreeLE K n := by
  constructor
  · intro hp
    exact ⟨p.natDegree, (mem_ringChooseDegreeLE_iff K p _).mpr ⟨hp, degree_le_natDegree⟩⟩
  · rintro ⟨n, hn⟩
    exact ((mem_ringChooseDegreeLE_iff K p n).mp hn).1

/-- Multiplication of integral degree stages adds their degree bounds. -/
theorem mul_mem_ringChooseDegreeLE {p q : K[X]} {m n : ℕ}
    (hp : p ∈ ringChooseDegreeLE K m) (hq : q ∈ ringChooseDegreeLE K n) :
    p * q ∈ ringChooseDegreeLE K (m + n) := by
  obtain ⟨hp, hpm⟩ := (mem_ringChooseDegreeLE_iff K p m).mp hp
  obtain ⟨hq, hqn⟩ := (mem_ringChooseDegreeLE_iff K q n).mp hq
  exact (mem_ringChooseDegreeLE_iff K _ _).mpr
    ⟨mul_mem_ringChooseSpan _ hp hq,
      (degree_mul_le p q).trans (by exact_mod_cast add_le_add hpm hqn)⟩

end TauCeti
