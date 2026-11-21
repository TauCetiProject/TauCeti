/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Coordinatewise mixed-space scaling on Euclidean Minkowski space

Let `K` be a number field and `ι` an index type. Coordinatewise multiplication by an element
`c : mixedSpace K` defines an `ℝ`-linear endomorphism
`TauCeti.NumberField.mixedEmbedding.mulMixedAmbient c` on the ambient Euclidean Minkowski space
`PiLp 2 fun _ : ι ↦ NumberField.mixedEmbedding.euclidean.mixedSpace K`, transported through
`NumberField.mixedEmbedding.euclidean.toMixed K`.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient c`: coordinatewise multiplication by
  `c : mixedSpace K` on `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient_apply`: coordinatewise evaluation formula.
* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient_one`: multiplying by `1` is the identity.
* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient_mul`: `mulMixedAmbient` is multiplicative in
  the scaling element `c : mixedSpace K`.
-/

public section

noncomputable section

open NumberField NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

open Classical in
/-- Coordinatewise multiplication by `c : mixedSpace K` on the ambient Euclidean Minkowski space. -/
def mulMixedAmbient (c : mixedSpace K) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ]
      (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) where
  toFun x := WithLp.toLp 2 fun i ↦ (euclidean.toMixed K).symm (c * euclidean.toMixed K (x i))
  map_add' x y := by
    ext1 i
    apply (euclidean.toMixed K).injective
    simp [mul_add]
  map_smul' r x := by
    ext1 i
    apply (euclidean.toMixed K).injective
    simp [Algebra.mul_smul_comm]

/-- Coordinatewise formula for `mulMixedAmbient`. -/
@[simp]
theorem mulMixedAmbient_apply (c : mixedSpace K)
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    mulMixedAmbient c x i = (euclidean.toMixed K).symm (c * euclidean.toMixed K (x i)) := by
  simp [mulMixedAmbient]

/-- Multiplying by `1 : mixedSpace K` acts as the identity on the ambient Euclidean Minkowski
space. -/
@[simp]
theorem mulMixedAmbient_one :
    (mulMixedAmbient (1 : mixedSpace K) :
        (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] _) = LinearMap.id := by
  ext1 x
  ext1 i
  apply (euclidean.toMixed K).injective
  simp

/-- `mulMixedAmbient` is multiplicative in the scaling element of `mixedSpace K`. -/
theorem mulMixedAmbient_mul (c₁ c₂ : mixedSpace K)
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :
    mulMixedAmbient (c₁ * c₂) x = mulMixedAmbient c₁ (mulMixedAmbient c₂ x) := by
  ext1 i
  apply (euclidean.toMixed K).injective
  simp [mul_assoc]

end TauCeti.NumberField.mixedEmbedding

end
