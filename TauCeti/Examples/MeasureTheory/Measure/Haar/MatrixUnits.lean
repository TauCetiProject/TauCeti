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
  (`TauCeti.measureReal_setOf_isUnit_padicInt`). They are the preimage of the units of the
  residue field `𝔽_p`, and each of the `p` residue classes has measure `p⁻¹`.
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
  let k := ResidueField ℤ_[p]
  let φ : ℤ_[p] →+ k := (residue ℤ_[p]).toAddMonoidHom
  have hk : Nat.card k = p := by
    rw [Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]
  have hker : MeasurableSet (φ.ker : Set ℤ_[p]) := by
    have : (φ.ker : Set ℤ_[p]) = maximalIdeal ℤ_[p] := by
      ext x
      exact residue_eq_zero_iff x
    rw [this]
    exact (isOpen_maximalIdeal ℤ_[p]).measurableSet
  have hset : {x : ℤ_[p] | IsUnit x} = φ ⁻¹' {y | IsUnit y} := by
    ext x
    exact (isUnit_map_iff (residue ℤ_[p]) x).symm
  have hunits : Nat.card {y : k | IsUnit y} = p - 1 := by
    have e : kˣ ≃ {y : k | IsUnit y} :=
      Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans <|
        Equiv.subtypeEquivRight fun y ↦ IsUnit.mem_submonoid_iff y
    rw [← Nat.card_congr e, Nat.card_units, hk]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [measureReal_def, hset, measure_preimage_addMonoidHom μ φ (residue_surjective) hker,
    hunits, hk, measure_univ, mul_one, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one, sub_div,
    div_self hp, one_div]

end TauCeti
