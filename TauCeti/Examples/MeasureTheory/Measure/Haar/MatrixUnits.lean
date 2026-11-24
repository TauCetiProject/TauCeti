/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.MeasureTheory.Measure.Haar.MatrixUnits

import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Haar measure of the invertible matrices: the boundary cases

Two instances of the Haar measure of `GL_n(O)` inside `M_n(O)` for a local ring `O` with residue
field of `q` elements, `∏_{i=1}^n (1 - q^{-i})` (`Matrix.measureReal_setOf_isUnit`):

* for `n = 0` the product is empty, so the invertible `0 × 0` matrices have full measure
  (`TauCeti.measureReal_setOf_isUnit_matrix_fin_zero`);
* for `O = ℤ_p`, the units `ℤ_p^×` have additive Haar probability `1 - p⁻¹`
  (`TauCeti.measureReal_setOf_isUnit_padicInt`). This is the case `n = 1`, `q = p`, transported
  along `ℤ_p ≃ M_1(ℤ_p)`.
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
  let e : ℤ_[p] ≃ᵐ Matrix (Fin 1) (Fin 1) ℤ_[p] :=
    ⟨Matrix.uniqueEquiv.symm,
      (Matrix.measurable_of _ _ _).comp <| .of_eval fun _ ↦ .of_eval fun _ ↦ measurable_id,
      (measurable_pi_apply default).comp (measurable_pi_apply default)⟩
  let f : ℤ_[p] →ₙ+ Matrix (Fin 1) (Fin 1) ℤ_[p] :=
    { toFun := e
      map_add' := fun _ _ ↦ rfl }
  have : (μ.map e).IsAddLeftInvariant := isAddLeftInvariant_map f e.measurable e.surjective
  have : Finite (ResidueField ℤ_[p]) := .of_equiv _ PadicInt.residueField.symm.toEquiv
  have hk : Nat.card (ResidueField ℤ_[p]) = p := by
    rw [Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]
  have hset : e ⁻¹' {M | IsUnit M} = {x | IsUnit x} := by
    ext x
    simp [e, ← MeasurableEquiv.coe_toEquiv, Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
  have h := Matrix.measureReal_setOf_isUnit 1 (isOpen_maximalIdeal ℤ_[p]).measurableSet (μ.map e)
  rwa [measureReal_def, e.map_apply, hset, ← measureReal_def, qPochhammer_one, hk] at h

end TauCeti
