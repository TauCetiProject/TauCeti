/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.RingTheory.LaurentSeries.Derivative

/-!
# Differentiating local Laurent expansions

At a rational place with a separating uniformizer `t`, Laurent expansion identifies
function-field differentiation `dz/dt` with formal differentiation of the expansion of `z`.
In particular, derivatives have residue zero. Differentiation lowers the order filtration
by at most one; this formulation includes zero derivatives in positive characteristic.

This comparison identifies the derivative factor in the change-of-uniformizer formula with
the Kähler differential coordinate `ds/dt`. Separability is explicit: no perfectness
assumption on the constant field is required.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section IV.2.
-/

public section

open scoped IntermediateField

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
variable (htsep : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

/-- **Laurent expansion commutes with differentiation** with respect to a separating
uniformizer. This identifies the formal derivative factor in a change of local parameter
with the expansion of the function-field derivative `dz/dt`. -/
@[simp]
theorem laurentSeriesExpansion_derivativeOfSeparating (z : F) :
    P.laurentSeriesExpansion hP ht (derivativeOfSeparating htsep z) =
      _root_.LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht z) := by
  let e := P.laurentSeriesExpansion hP ht
  let : Algebra F (LaurentSeries k) := e.toRingHom.toAlgebra
  have he (w : F) : algebraMap F (LaurentSeries k) w = e w := rfl
  have : @IsScalarTower k F (LaurentSeries k) _ _ Algebra.toSMul :=
    .of_algebraMap_eq fun c ↦ (e.commutes c).symm
  -- Derivations use the coefficientwise `k`-action on the target, not its algebra action.
  have : IsScalarTower k F (LaurentSeries k) :=
    .of_algebraMap_smul fun c z ↦ by
      rw [Algebra.smul_def, he, e.commutes, laurentSeries_algebraMap_mul_eq_smul]
  let δ : Derivation k F (LaurentSeries k) :=
    (laurentSeriesDerivativeDerivation k).compAlgebraMap F
  have hδ (w : F) : δ w = _root_.LaurentSeries.derivative k (e w) := by
    rw [Derivation.compAlgebraMap_apply, laurentSeriesDerivativeDerivation_apply, he]
  have hδt : δ t = 1 := by
    rw [hδ, laurentSeriesExpansion_uniformizer]
    simp [_root_.LaurentSeries.derivative_apply]
  have h := congrArg δ.liftKaehlerDifferential (derivativeOfSeparating_smul_D htsep z)
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, hδt, hδ] at h
  rw [Algebra.smul_def, he, mul_one] at h
  exact h

/-- The coefficient formula for function-field differentiation in a separating uniformizer.
The integer multiplier is interpreted in the constant field, so it can vanish in positive
characteristic. -/
theorem coeff_laurentSeriesExpansion_derivativeOfSeparating (z : F) (n : ℤ) :
    (P.laurentSeriesExpansion hP ht (derivativeOfSeparating htsep z)).coeff n =
      ((n + 1 : ℤ) : k) * (P.laurentSeriesExpansion hP ht z).coeff (n + 1) := by
  simp [laurentSeriesExpansion_derivativeOfSeparating, _root_.LaurentSeries.derivative_apply]

include hP ht in
/-- Differentiation lowers the order filtration by at most one. Using the filtration rather
than the additive order includes functions whose derivative is zero. -/
theorem derivativeOfSeparating_mem_filtration {m : ℤ} {z : F} (hz : z ∈ P.filtration m) :
    derivativeOfSeparating htsep z ∈ P.filtration (m - 1) := by
  rw [mem_filtration_iff, ← P.valuation_laurentSeriesExpansion hP ht,
    _root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k]
  intro n hn
  rw [coeff_laurentSeriesExpansion_derivativeOfSeparating]
  rw [P.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration hP ht hz (by omega), mul_zero]

/-- A function-field derivative has residue zero with respect to the separating uniformizer. -/
@[simp]
theorem residue_derivativeOfSeparating (z : F) :
    P.residue hP ht (derivativeOfSeparating htsep z) = 0 := by
  rw [residue_apply, coeff_laurentSeriesExpansion_derivativeOfSeparating]
  simp

end TauCeti.Place
