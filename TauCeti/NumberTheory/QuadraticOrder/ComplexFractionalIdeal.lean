/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticOrder.ComplexEmbedding
public import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Complex lattices of fractional ideals of imaginary quadratic orders

Let `D ≤ 0` with `D ≡ 0, 1 mod 4` and `D` not a square, let `K = ℚ(√D)`, let `O` be the quadratic
order of discriminant `D` and let `ι : K → ℂ` be the complex embedding
`QuadraticAlgebra.complexEmbedding`. A fractional ideal `𝔞` of `O` gives the `ℤ`-submodule `ι(𝔞)`
of `ℂ` (`TauCeti.QuadraticOrder.complexFractionalIdeal`). The unit ideal goes to the complex order
`complexOrder D` (`complexFractionalIdeal_one`), the map is multiplicative
(`complexFractionalIdeal_mul`), and it turns multiplication by `x ∈ K` into multiplication by
`ι(x)` (`complexFractionalIdeal_spanSingleton_mul`).

## Main definitions

* `TauCeti.QuadraticOrder.complexFractionalIdeal`: the image `ι(𝔞) ⊆ ℂ` of a fractional ideal.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §10.
-/

public section
noncomputable section

open QuadraticAlgebra FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti.QuadraticOrder

variable {D : ℤ} {hD : D % 4 = 0 ∨ D % 4 = 1} [Fact (¬ IsSquare D)]

/-- **The complex lattice of a fractional ideal.** For `D ≤ 0`, the image in `ℂ` of a fractional
ideal `𝔞` of the quadratic order of discriminant `D` under `QuadraticAlgebra.complexEmbedding`, as
a `ℤ`-submodule. For invertible `𝔞` and `D < 0` it is a period lattice
(`TauCeti.BinaryQuadraticForm.exists_periodPair_lattice_eq_complexFractionalIdeal`). -/
def complexFractionalIdeal (hD0 : D ≤ 0)
    (I : FractionalIdeal (numberFieldOrder D hD).toSubalgebra⁰ (QuadraticAlgebra ℚ (D : ℚ) 0)) :
    Submodule ℤ ℂ :=
  ((I : Submodule (numberFieldOrder D hD).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0)).restrictScalars ℤ).map
    ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ).toLinearMap

/-- Definitional expansion of `complexFractionalIdeal`. -/
theorem complexFractionalIdeal_def (hD0 : D ≤ 0)
    (I : FractionalIdeal (numberFieldOrder D hD).toSubalgebra⁰ (QuadraticAlgebra ℚ (D : ℚ) 0)) :
    complexFractionalIdeal hD0 I =
      ((I : Submodule (numberFieldOrder D hD).toSubalgebra
          (QuadraticAlgebra ℚ (D : ℚ) 0)).restrictScalars ℤ).map
        ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ).toLinearMap :=
  (rfl)

/-- The members of `complexFractionalIdeal hD0 I` are the images of the members of `I`. -/
theorem mem_complexFractionalIdeal_iff (hD0 : D ≤ 0)
    {I : FractionalIdeal (numberFieldOrder D hD).toSubalgebra⁰ (QuadraticAlgebra ℚ (D : ℚ) 0)}
    {z : ℂ} :
    z ∈ complexFractionalIdeal hD0 I ↔
      ∃ x ∈ I, complexEmbedding (Int.cast_nonpos.mpr hD0) x = z := by
  simp [complexFractionalIdeal]

/-- The complex lattice of the unit ideal is the complex order `complexOrder D`. -/
@[simp] theorem complexFractionalIdeal_one (hD0 : D ≤ 0) :
    complexFractionalIdeal hD0
        (1 : FractionalIdeal (numberFieldOrder D hD).toSubalgebra⁰ (QuadraticAlgebra ℚ (D : ℚ) 0)) =
      Subalgebra.toSubmodule (complexOrder D hD0 hD) := by
  ext z
  simp only [mem_complexFractionalIdeal_iff, FractionalIdeal.mem_one_iff, complexOrder_def,
    Subalgebra.mem_toSubmodule, Subalgebra.mem_map]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, numberFieldOrder_toSubalgebra D hD ▸ w.property, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, ⟨⟨w, (numberFieldOrder_toSubalgebra D hD).symm ▸ hw⟩, rfl⟩, rfl⟩

/-- The complex lattice of a product of fractional ideals is the product of their lattices. -/
@[simp] theorem complexFractionalIdeal_mul (hD0 : D ≤ 0)
    (I J : FractionalIdeal (numberFieldOrder D hD).toSubalgebra⁰ (QuadraticAlgebra ℚ (D : ℚ) 0)) :
    complexFractionalIdeal hD0 (I * J) =
      complexFractionalIdeal hD0 I * complexFractionalIdeal hD0 J := by
  rw [complexFractionalIdeal, coeToSubmodule_mul, Submodule.restrictScalars_mul]
  exact Submodule.map_mul _ _ _

/-- Multiplying a fractional ideal by `x ∈ K` multiplies its complex lattice by the image of `x`. -/
theorem complexFractionalIdeal_spanSingleton_mul (hD0 : D ≤ 0) (x : QuadraticAlgebra ℚ (D : ℚ) 0)
    (I : FractionalIdeal (numberFieldOrder D hD).toSubalgebra⁰ (QuadraticAlgebra ℚ (D : ℚ) 0)) :
    complexFractionalIdeal hD0 (spanSingleton _ x * I) =
      (complexFractionalIdeal hD0 I).map
        (LinearMap.mulLeft ℤ (complexEmbedding (Int.cast_nonpos.mpr hD0) x)) := by
  ext z
  simp only [mem_complexFractionalIdeal_iff, mem_singleton_mul, Submodule.mem_map,
    LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, (map_mul _ _ _).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, map_mul _ _ _⟩

end TauCeti.QuadraticOrder
