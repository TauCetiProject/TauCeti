/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.NegOne.Basic
public import TauCeti.NumberTheory.LocalField.Different.Eisenstein
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified

/-!
# The different of `ℚ₂(i)`

The element `1 + i` is a uniformizer of `ℚ₂(i)`: it generates the extension and is a root
of the Eisenstein polynomial `X² - 2X + 2`. Its ring of integers is therefore generated
by `1 + i` over the integer ring of `ℚ₂`. The derivative has terms of valuations two and
three, so the different exponent is two, as is the discriminant exponent.

This is a wildly ramified extension attaining the lower bound `e ≤ d`. The upper bound
`d ≤ e - 1 + v_L(e)` is strict here, in contrast to `ℚ₂(√2)`, where it is attained.
Thus neither endpoint is forced by wild ramification.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.

The construction uses the quadratic-field carrier from
`TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.NegOne.Basic` and the
Eisenstein-root and different formulas of `TauCeti.NumberTheory.LocalField.Eisenstein`
and `TauCeti.NumberTheory.LocalField.Different.Eisenstein`.
-/

public section
noncomputable section

open Polynomial ValuativeRel IsLocalRing
open scoped IntermediateField

namespace TauCeti.DyadicSqrtNegOne

private theorem integral_one_add_i : IsIntegral 𝒪[ℚ_[2]] (1 + i : DyadicSqrtNegOne) := by
  refine ⟨X ^ 2 - C 2 * X + C 2, by monicity!, ?_⟩
  simp [map_ofNat]
  have hi : i ^ 2 = -1 := by simp [i, QuadraticAlgebra.omega_pow_two_eq_add]
  linear_combination hi

/-- The uniformizer `1 + i`, viewed in the integer ring of `ℚ₂(i)`. -/
def integerOneAddI : 𝒪[DyadicSqrtNegOne] :=
  ⟨1 + i, (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation ℚ_[2])) _).1 integral_one_add_i⟩

@[simp]
theorem coe_integerOneAddI : (integerOneAddI : DyadicSqrtNegOne) = 1 + i := (rfl)

/-- `1 + i` generates `ℚ₂(i)` over `ℚ₂`. -/
theorem adjoin_one_add_i_eq_top : ℚ_[2]⟮(1 + i : DyadicSqrtNegOne)⟯ = ⊤ := by
  have hi : ℚ_[2]⟮i⟯ = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic i)]
    exact QuadraticAlgebra.adjoin_omega_eq_top
  simpa only [map_one, add_comm] using
    (IntermediateField.adjoin_simple_add_algebraMap i (1 : ℚ_[2])).trans hi

/-- The polynomial `X² - 2X + 2` is Eisenstein at the maximal ideal of `𝒪[ℚ₂]`. -/
theorem isEisensteinAt_X_sq_sub_two_mul_X_add_two :
    (X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).IsEisensteinAt 𝓂[ℚ_[2]] := by
  have htwo := Padic.irreducible_natCast_self 2
  have hv : IsDiscreteValuationRing.addVal 𝒪[ℚ_[2]] (2 : 𝒪[ℚ_[2]]) = 1 := by
    simpa using IsDiscreteValuationRing.addVal_uniformizer htwo
  have hdeg : (X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).natDegree = 2 := by
    compute_degree!
  refine ⟨?_, ?_, ?_⟩
  · rw [(by monicity! : (X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).Monic).leadingCoeff]
    exact Ideal.one_notMem _
  · intro n hn
    rw [hdeg] at hn
    interval_cases n <;> simpa [coeff_mul_X] using htwo.not_isUnit
  · have hc : (X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).coeff 0 = 2 := by simp
    rw [hc, TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, hv]
    norm_num

/-- The integral element `1 + i` is a root of `X² - 2X + 2`. -/
theorem isRoot_integerOneAddI :
    ((X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).map
      (algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtNegOne])).IsRoot integerOneAddI := by
  apply Subtype.ext
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_mul, map_C, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
    Subring.coe_add, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_integerOneAddI,
    Subring.coe_mul, Valuation.HasExtension.val_algebraMap, ZeroMemClass.coe_zero]
  have htwo : ((2 : 𝒪[ℚ_[2]]) : ℚ_[2]) = 2 :=
    map_ofNat (Subring.subtype 𝒪[ℚ_[2]]) 2
  rw [htwo, map_ofNat]
  have hi : i ^ 2 = -1 := by simp [i, QuadraticAlgebra.omega_pow_two_eq_add]
  linear_combination hi

/-- The element `1 + i` is a uniformizer of `ℚ₂(i)`. -/
theorem irreducible_integerOneAddI : Irreducible integerOneAddI :=
  irreducible_of_eisenstein_adjoin_eq_top _ isEisensteinAt_X_sq_sub_two_mul_X_add_two
    _ isRoot_integerOneAddI adjoin_one_add_i_eq_top

/-- The ramification index of `ℚ₂(i)/ℚ₂` is two. -/
@[simp]
theorem ramificationIndex_eq_two : ramificationIndex ℚ_[2] DyadicSqrtNegOne = 2 := by
  have h := ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top
    _ isEisensteinAt_X_sq_sub_two_mul_X_add_two _ isRoot_integerOneAddI
    adjoin_one_add_i_eq_top
  have hdeg : (X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).natDegree = 2 := by
    compute_degree!
  exact h.trans hdeg

/-- The residue degree of `ℚ₂(i)/ℚ₂` is one. -/
@[simp]
theorem inertiaDegree_eq_one : inertiaDegree ℚ_[2] DyadicSqrtNegOne = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _
    isEisensteinAt_X_sq_sub_two_mul_X_add_two _ isRoot_integerOneAddI
    adjoin_one_add_i_eq_top

/-- The ring of integers of `ℚ₂(i)` is generated by `1 + i` over `𝒪[ℚ₂]`. -/
theorem adjoin_integerOneAddI_eq_top :
    Algebra.adjoin 𝒪[ℚ_[2]] {integerOneAddI} = ⊤ :=
  algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top
    isEisensteinAt_X_sq_sub_two_mul_X_add_two isRoot_integerOneAddI
    adjoin_one_add_i_eq_top

/-- The different exponent of `ℚ₂(i)/ℚ₂` is two. -/
@[simp]
theorem differentExponent_eq_two : differentExponent ℚ_[2] DyadicSqrtNegOne = 2 := by
  have hdeg : (X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).natDegree = 2 := by
    compute_degree!
  have hv : IsDiscreteValuationRing.addVal 𝒪[ℚ_[2]] (2 : 𝒪[ℚ_[2]]) = 1 := by
    simpa using IsDiscreteValuationRing.addVal_uniformizer (Padic.irreducible_natCast_self 2)
  have h := natCast_differentExponent_eq_iInf_of_eisenstein_adjoin_eq_top
    _ isEisensteinAt_X_sq_sub_two_mul_X_add_two _ isRoot_integerOneAddI
    adjoin_one_add_i_eq_top
  rw [hdeg, ramificationIndex_eq_two] at h
  have hinf : (⨅ j : Fin 2,
      2 • IsDiscreteValuationRing.addVal 𝒪[ℚ_[2]]
        ((X ^ 2 - C 2 * X + C 2 : 𝒪[ℚ_[2]][X]).coeff (j + 1) * (j + 1)) + (j : ℕ)) =
        (2 : ℕ∞) := by
    apply le_antisymm
    · exact (iInf_le _ (0 : Fin 2)).trans_eq (by norm_num [coeff_mul_X, hv])
    · apply le_iInf
      intro j
      fin_cases j <;> norm_num [coeff_mul_X, hv]
  rw [hinf] at h
  exact_mod_cast h

/-- The discriminant exponent of `ℚ₂(i)/ℚ₂` is two. -/
@[simp]
theorem discriminantExponent_eq_two : discriminantExponent ℚ_[2] DyadicSqrtNegOne = 2 := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    inertiaDegree_eq_one, differentExponent_eq_two, one_mul]

/-- The dyadic quadratic extension `ℚ₂(i)/ℚ₂` is wildly ramified. -/
theorem isWildlyRamified : IsWildlyRamified ℚ_[2] DyadicSqrtNegOne := by
  rw [isWildlyRamified_iff, ramificationIndex_eq_two]
  simp [Padic.ringChar_residueField 2]

/-- The wild upper bound is strict for `ℚ₂(i)/ℚ₂`: `d = 2 < 3 = e - 1 + v_L(e)`. -/
theorem differentExponent_lt_ramificationIndex_sub_one_add_natCastValuation :
    differentExponent ℚ_[2] DyadicSqrtNegOne <
      ramificationIndex ℚ_[2] DyadicSqrtNegOne - 1 +
        natCastValuation DyadicSqrtNegOne (ramificationIndex ℚ_[2] DyadicSqrtNegOne)
          (by simp) := by
  have hv : natCastValuation DyadicSqrtNegOne 2 (by norm_num) = 2 := by
    rw [natCastValuation_eq_ramificationIndex_mul (K := ℚ_[2]) 2 (by norm_num),
      ramificationIndex_eq_two, Padic.natCastValuation_self, mul_one]
  simp [hv]

end TauCeti.DyadicSqrtNegOne
