/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.MeasureTheory.Measure.Haar.MatrixUnits

import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Haar measure of the invertible matrices: the boundary cases

Two instances of the Haar measure of `GL_n(O)` inside `M_n(O)` for a local ring `O` with residue
field of `q` elements, `∏_{i=1}^n (1 - q^{-i})` (`Matrix.measureReal_setOf_isUnit`):

* for `n = 0` the product is empty, so the invertible `0 × 0` matrices have full measure
  (`TauCeti.measureReal_setOf_isUnit_matrix_fin_zero`);
* for `O = ℤ_p`, the units `ℤ_p^×` have additive Haar probability `1 - p⁻¹`
  (`TauCeti.measureReal_setOf_isUnit_padicInt`). This is the case `n = 1`, `q = p`, through
  `IsLocalRing.measureReal_setOf_isUnit`.
-/

public section

open MeasureTheory Set IsLocalRing

namespace TauCeti

/-- The invertible `0 × 0` matrices over a local ring with finite residue field and measurable
maximal ideal have full measure for every left-invariant probability measure: the product
`∏_{i=1}^0 (1 - q^{-i})` is empty. -/
theorem measureReal_setOf_isUnit_matrix_fin_zero {R : Type*} [CommRing R] [IsLocalRing R]
    [MeasurableSpace R] [MeasurableAdd R] [Finite (ResidueField R)]
    (hm : MeasurableSet (maximalIdeal R : Set R)) (μ : Measure (Matrix (Fin 0) (Fin 0) R))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    μ.real {M | IsUnit M} = 1 := by
  rw [Matrix.measureReal_setOf_isUnit 0 hm μ, qPochhammer_zero]

/-- **The Haar measure of `ℤ_p^×`.** For every translation-invariant probability measure on the
`p`-adic integers, such as their additive Haar probability, the units have measure `1 - p⁻¹`. -/
theorem measureReal_setOf_isUnit_padicInt (p : ℕ) [Fact p.Prime] [MeasurableSpace ℤ_[p]]
    [BorelSpace ℤ_[p]] (μ : Measure ℤ_[p]) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    μ.real {x | IsUnit x} = 1 - (p : ℝ)⁻¹ := by
  have : Finite (ResidueField ℤ_[p]) := .of_equiv _ PadicInt.residueField.symm.toEquiv
  have hk : Nat.card (ResidueField ℤ_[p]) = p := by
    rw [Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]
  rw [IsLocalRing.measureReal_setOf_isUnit (isOpen_maximalIdeal ℤ_[p]).measurableSet μ, hk]

end TauCeti
