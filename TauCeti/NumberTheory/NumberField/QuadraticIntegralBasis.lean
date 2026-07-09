/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The `{1, x}` integral basis of a quadratic field

In a quadratic number field `K`, an algebraic integer `x` that is not rational yields the
`ℚ`-basis `{1, x}` of `K`, all of whose members are algebraic integers. This is the standard
integral power basis attached to a primitive integral generator of a quadratic field, and it is
the natural input to the trace-form discriminant machinery. It is stated here as reusable
number-field API; the effective discriminant bound and the `ℚ(i)` worked example are among its
consumers.
-/

public section

open Module

namespace TauCeti

namespace NumberField

/-- In a quadratic number field, an integral non-rational element `x` gives a `ℚ`-basis
`{1, x}` consisting of algebraic integers. -/
theorem exists_basis_eq_one_self_of_notMem_range_of_isIntegral {K : Type*} [Field K]
    [NumberField K] {x : K} (hfin : finrank ℚ K = 2)
    (hx : x ∉ (algebraMap ℚ K).range) (hxint : IsIntegral ℤ x) :
    ∃ b : Basis (Fin 2) ℚ K, ⇑b = ![1, x] ∧ ∀ i, IsIntegral ℤ (b i) := by
  classical
  -- `x ≠ 0`, else `x = algebraMap ℚ K 0` would be rational.
  have hxne : x ≠ 0 := by
    rintro rfl
    exact hx ⟨0, by rw [map_zero]⟩
  -- `{1, x}` is linearly independent over `ℚ`: `x` is nonzero and not a `ℚ`-multiple of `1`.
  have hli : LinearIndependent ℚ ![1, x] := by
    rw [linearIndependent_fin2]
    refine ⟨by simpa using hxne, ?_⟩
    intro c hc
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc
    rw [Algebra.smul_def] at hc
    refine hx ⟨c⁻¹, ?_⟩
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right hc
  -- A linearly independent family of `finrank` vectors is a basis.
  have hcard : Fintype.card (Fin 2) = finrank ℚ K := by
    rw [Fintype.card_fin]; exact hfin.symm
  set b := basisOfLinearIndependentOfCardEqFinrank' ![1, x] hli hcard with hb_def
  have hbcoe : ⇑b = ![1, x] := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ⟨b, hbcoe, ?_⟩
  intro i
  fin_cases i
  · simpa [hbcoe] using (isIntegral_one : IsIntegral ℤ (1 : K))
  · simpa [hbcoe] using hxint

end NumberField

end TauCeti
