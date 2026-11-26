/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Jacobson.Ideal

import Mathlib.Algebra.BigOperators.Fin

/-!
# The monoid `Σ₀(I)` of `2 × 2` matrices with lower left entry in `I`

Let `O` be a commutative ring and `I` an ideal of `O` inside its Jacobson radical (for instance
the integers `𝒪_v` of a local field and a power `𝔭_vᵗ` of its maximal ideal). The matrices
`!![a, b; c, d]` over `O` with `c ∈ I` and `d` a unit form a monoid `Σ₀(I)`: in a product, the new
lower right entry `c b' + d d'` is a unit because `c b'` lies in the Jacobson radical. Over `ℤ_p`
with `I = pᵗ ℤ_p`, its matrices of nonzero determinant form Jacobs's monoid `Σ_t`.

## Main definitions

* `TauCeti.Matrix.sigma0Submonoid I hI`: the monoid `Σ₀(I)`.
* `TauCeti.Matrix.sigma0LowerRightUnit`: the lower right entry of an element of `Σ₀(I)`, as a unit.

## References

* D. Jacobs, *Slopes of compact Hecke operators*, PhD thesis, Imperial College London (2003),
  §1.5.
-/

public section

namespace TauCeti.Matrix

variable {O : Type*} [CommRing O]

/-- The monoid **`Σ₀(I)`** of `2 × 2` matrices `!![a, b; c, d]` over `O` with `c ∈ I` and `d` a
unit, for an ideal `I` in the Jacobson radical of `O`. For `O = 𝒪_v` and `I = 𝔭_v` these are
exactly the matrices over `𝒪_v` whose denominator `c z + d` is a unit for every `z ∈ 𝒪_v`, so that
their Möbius transformations preserve `𝒪_v`; for `I = 𝔭_vᵗ` one additionally has
`c ≡ 0 mod 𝔭_vᵗ`. -/
def sigma0Submonoid (I : Ideal O) (hI : I ≤ Ring.jacobson O) :
    Submonoid (Matrix (Fin 2) (Fin 2) O) where
  carrier := {γ | γ 1 0 ∈ I ∧ IsUnit (γ 1 1)}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {γ δ} hγ hδ := by
    obtain ⟨hc, hd⟩ := hγ
    obtain ⟨hc', hd'⟩ := hδ
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨I.add_mem (I.mul_mem_right _ hc) (I.mul_mem_left _ hc'), ?_⟩
    -- `c b' + d d' = (c b' (d d')⁻¹ + 1) d d'`, and `c b' (d d')⁻¹` is in the Jacobson radical
    obtain ⟨u, hu⟩ := hd.mul hd'
    convert (Ring.mem_jacobson_iff.mp (hI (I.mul_mem_right (δ 0 1) hc)) ↑u⁻¹).mul u.isUnit
      using 1
    rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu]

variable {I : Ideal O} {hI : I ≤ Ring.jacobson O} {γ : Matrix (Fin 2) (Fin 2) O}

@[simp]
theorem mem_sigma0Submonoid_iff : γ ∈ sigma0Submonoid I hI ↔ γ 1 0 ∈ I ∧ IsUnit (γ 1 1) :=
  Iff.rfl

/-- The lower left entry of an element of `Σ₀(I)` lies in `I`. -/
theorem lowerLeft_mem_of_mem_sigma0Submonoid (hγ : γ ∈ sigma0Submonoid I hI) : γ 1 0 ∈ I :=
  hγ.1

/-- The lower right entry of an element of `Σ₀(I)` is a unit. -/
theorem isUnit_lowerRight_of_mem_sigma0Submonoid (hγ : γ ∈ sigma0Submonoid I hI) :
    IsUnit (γ 1 1) :=
  hγ.2

/-- The lower right entry `d` of an element of `Σ₀(I)`, as a unit of `O`. -/
noncomputable def sigma0LowerRightUnit (γ : sigma0Submonoid I hI) : Oˣ :=
  (isUnit_lowerRight_of_mem_sigma0Submonoid γ.property).unit

@[simp]
theorem coe_sigma0LowerRightUnit (γ : sigma0Submonoid I hI) :
    (sigma0LowerRightUnit γ : O) = (γ : Matrix (Fin 2) (Fin 2) O) 1 1 :=
  IsUnit.unit_spec _

@[simp]
theorem sigma0LowerRightUnit_one : sigma0LowerRightUnit (1 : sigma0Submonoid I hI) = 1 :=
  Units.ext (by simp)

/-- The lower right entry of a product `γ δ` in `Σ₀(I)` is `c b' + d d'`. -/
theorem coe_sigma0LowerRightUnit_mul (γ δ : sigma0Submonoid I hI) :
    (sigma0LowerRightUnit (γ * δ) : O) =
      (γ : Matrix (Fin 2) (Fin 2) O) 1 0 * (δ : Matrix (Fin 2) (Fin 2) O) 0 1 +
        (γ : Matrix (Fin 2) (Fin 2) O) 1 1 * (δ : Matrix (Fin 2) (Fin 2) O) 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end TauCeti.Matrix
