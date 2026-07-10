/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The `{1, x}` rational basis of algebraic integers in a quadratic number field

Internal helper: in a quadratic number field `K`, an integral element `x` that is not rational
packages the pair `{1, x}` as a `ℚ`-basis of `K` whose two vectors are algebraic integers. It is
*not* claimed to be a `ℤ`-basis of the full ring of integers `𝓞 K`. This construction is shared by
the effective discriminant bound `TauCeti.NumberField.abs_discr_le_of_sq_intCast` and the
roadmap's `ℚ(i)` discriminant worked example, so it lives in the generic `NumberField.Internal`
namespace rather than being duplicated inline or exposed from either headline API file.
-/

public section

open Module

namespace TauCeti.NumberField.Internal

/-- In a quadratic number field, an integral non-rational element `x` gives the `ℚ`-basis
`{1, x}` of algebraic integers. -/
theorem exists_basis_eq_one_self_of_notMem_range_of_isIntegral {K : Type*} [Field K]
    [NumberField K] {x : K} (hfin : finrank ℚ K = 2)
    (hx : x ∉ (algebraMap ℚ K).range) (hxint : IsIntegral ℤ x) :
    ∃ b : Module.Basis (Fin 2) ℚ K, ⇑b = ![1, x] ∧ ∀ i, IsIntegral ℤ (b i) := by
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

end TauCeti.NumberField.Internal
