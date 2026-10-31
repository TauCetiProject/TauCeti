/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
public import Mathlib.FieldTheory.Separable

/-!
# Almost every Eisenstein polynomial is separable

Over a nonarchimedean local field, the nonseparable Eisenstein polynomials form a null set
for additive Haar measure on coefficient space. An Eisenstein polynomial is irreducible;
when its linear coefficient is nonzero, its derivative is nonzero and it is separable.
The exceptional coordinate hyperplane is null inside the integer box, since boxes with one
coordinate in deeper powers of the maximal ideal have volumes tending to zero.

The linear case is separable everywhere. The result also applies in equal characteristic,
where inseparable Eisenstein polynomials do exist and must be discarded in root counting.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, equation (3).
* The linear-coefficient separability argument is adapted from `separable_toPoly` and
  `ae_separable` in `MassFormula/First.lean` of
  [0stellensatz/MassFormula](https://github.com/0stellensatz/MassFormula), Apache-2.0.
-/

public section
noncomputable section

open Polynomial MeasureTheory ValuativeRel TauCeti.Polynomial
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

/-- An Eisenstein polynomial with nonzero linear coefficient is separable, including in
positive characteristic. -/
theorem separable_monicOfCoeff_of_mem_eisensteinSet_of_coeff_one_ne_zero {n : ℕ}
    [IsDiscreteValuationRing 𝒪[K]]
    (hn : 1 < n) {a : Fin n → K} (ha : a ∈ eisensteinSet K n)
    (h1 : a ⟨1, hn⟩ ≠ 0) : (monicOfCoeff a).Separable := by
  rw [separable_iff_derivative_ne_zero (irreducible_monicOfCoeff_of_mem_eisensteinSet
    (by omega) ha)]
  intro h
  apply h1
  have hcoeff := congrArg (fun p : K[X] ↦ p.coeff 0) h
  simpa only [coeff_derivative, zero_add, coeff_monicOfCoeff a ⟨1, hn⟩,
    Nat.cast_zero, zero_add, Nat.cast_one, mul_one, coeff_zero] using hcoeff

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Almost every Eisenstein polynomial of positive degree is separable. No normalization
of the additive Haar measure is needed. -/
theorem ae_separable_monicOfCoeff_restrict_eisensteinSet {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    ∀ᵐ a ∂μ.restrict (eisensteinSet K n), (monicOfCoeff a).Separable := by
  rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr hn) with h | h
  · subst n
    filter_upwards [] with a
    rw [(monic_monicOfCoeff a).eq_X_add_C (natDegree_monicOfCoeff a)]
    exact separable_X_add_C _
  · have hnull := μ.measure_integerBox_inter_coord_eq_zero
      (isCompact_integerBox.measure_lt_top.ne) (⟨1, h⟩ : Fin n)
    have hae : ∀ᵐ a ∂μ.restrict (eisensteinSet K n), a ⟨1, h⟩ ≠ 0 := by
      rw [ae_iff]
      rw [Measure.restrict_apply' measurableSet_eisensteinSet]
      apply measure_mono_null (t := integerBox K (Fin n) ∩ {a | a ⟨1, h⟩ = 0}) ?_ hnull
      intro a ha
      exact ⟨eisensteinSet_subset_integerBox n ha.2, Classical.not_not.mp ha.1⟩
    filter_upwards [ae_restrict_mem measurableSet_eisensteinSet, hae] with a ha ha1
    exact separable_monicOfCoeff_of_mem_eisensteinSet_of_coeff_one_ne_zero h ha ha1

end TauCeti
