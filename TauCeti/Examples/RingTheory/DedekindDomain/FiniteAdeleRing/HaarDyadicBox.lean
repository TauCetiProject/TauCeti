/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ResidueField
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
import TauCeti.RingTheory.DedekindDomain.Countable

/-!
# The dyadic box in the finite adeles of `ℚ`

A check of the additive Haar measure `μ_f` on the finite adeles of `ℚ`, normalized to give
`∏_p ℤ_p` mass one: the box with factor `2ℤ₂` at the place `2` and `ℤ_p` at every odd prime `p`
has mass `1/2`. It is the translate of `∏_p ℤ_p` by the finite idele concentrated at `2` with
component `2`, a uniformizer at `2`, which scales `μ_f` by `|2|_2 = 2⁻¹`.
-/

public section

open MeasureTheory Measure IsDedekindDomain HeightOneSpectrum FiniteAdeleRing RestrictedProduct
  ValuativeRel
open scoped ENNReal Pointwise

namespace TauCeti.Examples

/-- For the place `v = (2)` of `ℚ`, the box with factor `2ℤ₂` at `v` and the local integers
elsewhere has mass `1/2` for the Haar measure on the finite adeles giving `∏_p ℤ_p` mass one. -/
example (v : HeightOneSpectrum ℤ) (hv : v.asIdeal = Ideal.span {2}) :
    addHaarMeasure (integralAdelesPositiveCompacts ℤ ℚ)
        (box fun w : HeightOneSpectrum ℤ ↦ open Classical in if w = v then
          (2 : w.adicCompletion ℚ) • (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))
          else (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) =
      2⁻¹ := by
  classical
  have h2 : (2 : v.adicCompletion ℚ) ≠ 0 := two_ne_zero
  let a := unitsOfAdicCompletion ℚ v (Units.mk0 2 h2)
  -- The box is the translate of the integral finite adeles by the idele `a`.
  have hbox : (box fun w : HeightOneSpectrum ℤ ↦ if w = v then
        (2 : w.adicCompletion ℚ) • (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))
        else (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) =
      a • (integralAdeles ℤ ℚ : Set (FiniteAdeleRing ℤ ℚ)) := by
    rw [smul_integralAdeles]
    congr 1
    funext w
    split_ifs with h
    · subst h
      simp [a, coe_unitsOfAdicCompletion_apply, ofAdicCompletion_apply_self]
    · simp [a, coe_unitsOfAdicCompletion_apply, ofAdicCompletion_apply_of_ne ℚ h]
  -- `2` is a uniformizer at `v`: it lies in `(2)` but not in `(2) ^ 2 = (4)`.
  have hπ : IsUniformizer (v.adicCompletion ℚ) (Units.mk0 2 h2) := by
    rw [isUniformizer_iff_valued_eq_exp_neg_one, Units.val_mk0]
    have h := v.intValuation_eq_exp_neg_one_of_mem_of_notMem_sq (r := 2)
      (hv ▸ Ideal.mem_span_singleton_self 2) (by
        rw [hv, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        decide)
    rw [← h, ← v.valuation_of_algebraMap (K := ℚ)]
    convert v.valuedAdicCompletion_eq_valuation (K := ℚ) 2 using 2
    exact (map_ofNat _ 2).symm
  have hcard : Nat.card 𝓀[v.adicCompletion ℚ] = 2 := by
    rw [natCard_residueField_adicCompletion_eq_absNorm, hv, Ideal.absNorm_span_singleton,
      Algebra.norm_self]
    rfl
  rw [hbox, ← distribHaarChar_mul, distribHaarChar_unitsOfAdicCompletion,
    distribHaarChar_of_isUniformizer hπ, hcard, ← coe_integralAdelesPositiveCompacts,
    addHaarMeasure_self, mul_one]
  simp

end TauCeti.Examples
