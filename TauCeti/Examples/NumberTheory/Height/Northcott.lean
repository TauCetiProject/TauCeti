/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Northcott
import TauCeti.NumberTheory.Height.FiniteOrder
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Concrete Northcott calibrations

Complex roots of unity of every positive order have absolute height one, giving an infinite
set if the degree bound is omitted. The bounded sets pull back unchanged along the standard
embeddings of the rationals into the reals and complexes and of the reals into the complexes.
For degree and height bounds both one, all three fields give exactly minus one, zero, and one.
-/

public section
open NumberField Height
namespace TauCeti.Examples.Northcott

private noncomputable def root (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n + 1))

private theorem primitive_root (n : ℕ) : IsPrimitiveRoot (root n) (n + 1) := by
  simpa [root] using Complex.isPrimitiveRoot_exp (n + 1) (by omega)

private theorem root_integral (n : ℕ) : IsIntegral ℚ (root n) :=
  ((primitive_root n).isIntegral (by omega)).tower_top

private theorem root_height (n : ℕ) : absMulHeight₁ (root n) = 1 :=
  (absMulHeight₁_eq_one_iff (root_integral n)).mpr
    (Or.inr ((primitive_root n).isOfFinOrder (by omega)))

private theorem root_injective : Function.Injective root := by
  intro n m h
  have ho := congrArg orderOf h
  rw [← (primitive_root n).eq_orderOf, ← (primitive_root m).eq_orderOf] at ho
  omega

/-- Omitting the degree bound leaves infinitely many algebraic elements of height one. -/
theorem infinite_height_one :
    {x : ℂ | IsAlgebraic ℚ x ∧ absMulHeight₁ x ≤ 1}.Infinite := by
  apply (Set.infinite_range_of_injective root_injective).mono
  rintro x ⟨n, rfl⟩
  exact ⟨(root_integral n).isAlgebraic, (root_height n).le⟩

/-- Compatibility of bounded sets with the standard embedding `ℚ → ℝ`. -/
example (d : ℕ) (B : ℝ) :
    (algebraMap ℚ ℝ) ⁻¹' {x : ℝ | IsAlgebraic ℚ x ∧
      (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} =
    {x : ℚ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} :=
  preimage_setOf_absMulHeight₁_le (algebraMap ℚ ℝ) d B

/-- Compatibility of bounded sets with the standard embedding `ℚ → ℂ`. -/
example (d : ℕ) (B : ℝ) :
    (algebraMap ℚ ℂ) ⁻¹' {x : ℂ | IsAlgebraic ℚ x ∧
      (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} =
    {x : ℚ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} :=
  preimage_setOf_absMulHeight₁_le (algebraMap ℚ ℂ) d B

/-- Compatibility of bounded sets with the standard embedding `ℝ → ℂ`. -/
example (d : ℕ) (B : ℝ) :
    (algebraMap ℝ ℂ) ⁻¹' {x : ℂ | IsAlgebraic ℚ x ∧
      (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} =
    {x : ℝ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} :=
  preimage_setOf_absMulHeight₁_le (algebraMap ℝ ℂ) d B

/-- The degree-one, height-one set inside `ℚ`. -/
example : {x : ℚ | IsAlgebraic ℚ x ∧
    (minpoly ℚ x).natDegree ≤ 1 ∧ absMulHeight₁ x ≤ 1} = {-1, 0, 1} :=
  setOf_degree_le_one_absMulHeight₁_le_one ℚ

/-- The degree-one, height-one set inside `ℝ`. -/
example : {x : ℝ | IsAlgebraic ℚ x ∧
    (minpoly ℚ x).natDegree ≤ 1 ∧ absMulHeight₁ x ≤ 1} = {-1, 0, 1} :=
  setOf_degree_le_one_absMulHeight₁_le_one ℝ

/-- The degree-one, height-one set inside `ℂ`. -/
example : {x : ℂ | IsAlgebraic ℚ x ∧
    (minpoly ℚ x).natDegree ≤ 1 ∧ absMulHeight₁ x ≤ 1} = {-1, 0, 1} :=
  setOf_degree_le_one_absMulHeight₁_le_one ℂ

end TauCeti.Examples.Northcott
