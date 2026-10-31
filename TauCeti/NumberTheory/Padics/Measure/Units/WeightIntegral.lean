/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.CompactGroup
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
public import TauCeti.NumberTheory.Padics.Measure.Units.Moments
public import TauCeti.NumberTheory.Padics.WeightSpace
import Mathlib.NumberTheory.Padics.Complex

/-!
# Integrating weights against integral measures on `ℤ_pˣ`

Let `K` be a complete normed field over `ℚ_p`, such as `ℂ_p`. An integral measure
`ν ∈ D(ℤ_pˣ, ℤ_p)` extends to a `K`-valued measure of norm at most one, and integrating a weight
`κ : ℤ_pˣ → Kˣ` against it gives the *measure function*

`TauCeti.measureFun K ν κ = ∫ κ(x) dν(x)`.

It is a bounded function on the set of `K`-valued weights; this is how an integral measure on
`ℤ_pˣ`, such as a `p`-adic `L`-function, is evaluated at weights. No topology on the set of
weights or on measures is involved.

A field-valued weight takes values of norm one, because `ℤ_pˣ` is compact, so
`|measureFun K ν κ|` is at most the norm of the extended measure, which is at most one
(`TauCeti.norm_measureFun_le`, `TauCeti.norm_measureFun_le_one`). Every Dirac measure attains this
bound. Integration against a character is multiplicative for convolution, so `measureFun K` is a
ring homomorphism from the convolution ring of integral measures to the ring of `K`-valued
functions on weights.

The weights separate integral measures (`TauCeti.measureFun_injective`). The power weights
`x ↦ x ^ k` already suffice: their integrals are the images of the positive moments `ν(x ↦ x ^ k)`,
and a measure on `ℤ_pˣ` whose positive moments vanish is zero
(`AbstractMeasure.units_eq_zero_of_positive_moments`).

## Main definitions

* `TauCeti.WeightSpace.weightTest κ`: a weight `κ`, viewed as a scalar-valued continuous character
  `x ↦ (κ x : R)` of `ℤ_pˣ`; its underlying continuous function is the test function integrated
  against measures.
* `TauCeti.padicIntAlgebraMap p K`: the structure map `ℤ_p → K` of a normed `ℚ_p`-algebra.
* `TauCeti.WeightSpace.inclusion K`: the weight `x ↦ x` of `ℤ_pˣ` with values in `K`.
* `TauCeti.measureFun K`: the ring homomorphism `ν ↦ (κ ↦ ∫ κ dν)`.

## Main results

* `TauCeti.measureFun_dirac`: `measureFun K δ_x κ = κ(x)`.
* `TauCeti.measureFun_inclusion_pow`: the integral of the power weight `x ↦ x ^ k` is the
  image in `K` of the moment `ν(x ↦ x ^ k)`.
* `TauCeti.norm_measureFun_le`, `TauCeti.norm_measureFun_le_one`: the bound
  `|measureFun K ν κ| ≤ ‖ν_K‖ ≤ 1`, attained by Dirac measures (`TauCeti.norm_measureFun_dirac`).
* `TauCeti.measureFun_injective`: weights separate integral measures.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3.6 and 4,
  Definition 3.34, Lemma 3.36 and Proposition 3.16.
-/

public section

open AbstractMeasure ContinuousMonoidHom
open scoped AbstractMeasure

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

namespace WeightSpace

variable {R : Type*} [Monoid R] [TopologicalSpace R]

/-- A weight `κ : ℤ_pˣ → Rˣ`, viewed as the `R`-valued continuous character `x ↦ (κ x : R)`.
Its underlying continuous function is the test function integrated against measures. -/
noncomputable def weightTest (κ : WeightSpace p R) : ℤ_[p]ˣ →ₜ* R where
  toMonoidHom := (Units.coeHom R).comp κ.toMonoidHom
  continuous_toFun := Units.continuous_val.comp κ.continuous

@[simp]
theorem weightTest_apply (κ : WeightSpace p R) (x : ℤ_[p]ˣ) : κ.weightTest x = (κ x : R) :=
  (rfl)

/-- A weight is determined by its scalar-valued character. -/
theorem weightTest_injective : Function.Injective (weightTest (p := p) (R := R)) :=
  fun κ κ' h ↦ ContinuousMonoidHom.ext fun x ↦ Units.ext (by simpa using congr($h x))

@[simp]
theorem weightTest_inj {κ κ' : WeightSpace p R} : κ.weightTest = κ'.weightTest ↔ κ = κ' :=
  weightTest_injective.eq_iff

end WeightSpace

section Algebra

variable (p) (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]

/-- The structure map `ℤ_p → K` of a normed `ℚ_p`-algebra `K`, through `ℚ_p`. It is an isometry
onto its image (`TauCeti.norm_padicIntAlgebraMap`). -/
noncomputable def padicIntAlgebraMap : ℤ_[p] →+* K :=
  (algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom

variable {p K}

@[simp]
theorem padicIntAlgebraMap_apply (a : ℤ_[p]) :
    padicIntAlgebraMap p K a = algebraMap ℚ_[p] K a :=
  (rfl)

theorem norm_padicIntAlgebraMap (a : ℤ_[p]) : ‖padicIntAlgebraMap p K a‖ = ‖a‖ := by
  simp [norm_algebraMap']

theorem norm_padicIntAlgebraMap_le_one (a : ℤ_[p]) : ‖padicIntAlgebraMap p K a‖ ≤ 1 :=
  (norm_padicIntAlgebraMap a).trans_le a.norm_le_one

theorem padicIntAlgebraMap_injective : Function.Injective (padicIntAlgebraMap p K) :=
  (algebraMap ℚ_[p] K).injective.comp PadicInt.isEmbedding_coe_ringHom.injective

theorem continuous_padicIntAlgebraMap : Continuous (padicIntAlgebraMap p K) :=
  (continuous_algebraMap ℚ_[p] K).comp PadicInt.isEmbedding_coe_ringHom.continuous

namespace WeightSpace

variable (K) in
/-- The weight `x ↦ x` of `ℤ_pˣ` with values in a normed `ℚ_p`-algebra `K`. Its powers are the
algebraic weights `x ↦ x ^ k`. -/
noncomputable def inclusion : WeightSpace p K where
  toMonoidHom := Units.map (padicIntAlgebraMap p K).toMonoidHom
  continuous_toFun := Continuous.units_map _ continuous_padicIntAlgebraMap

@[simp]
theorem coe_inclusion_apply (x : ℤ_[p]ˣ) :
    (inclusion K x : K) = padicIntAlgebraMap p K x :=
  (rfl)

end WeightSpace

end Algebra

section MeasureFun

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- The *measure function* of integral measures on `ℤ_pˣ` with values in a complete normed
`ℚ_p`-algebra `K`: a measure `ν ∈ D(ℤ_pˣ, ℤ_p)` goes to the function `κ ↦ ∫ κ dν_K` on
`K`-valued weights, where `ν_K` is the coefficient extension of `ν` to `K`. It is a ring
homomorphism for the convolution product of measures. -/
noncomputable def measureFun : D(ℤ_[p]ˣ, ℤ_[p]) →+* (WeightSpace p K → K) :=
  RingHom.pi fun κ ↦
    κ.weightTest.extendedCharacterRingHom (padicIntAlgebraMap p K) norm_padicIntAlgebraMap_le_one

variable {K}

/-- The measure function integrates the weight against the coefficient extension of the
measure. -/
theorem measureFun_apply (ν : D(ℤ_[p]ˣ, ℤ_[p])) (κ : WeightSpace p K) :
    measureFun K ν κ =
      extendCoefficients (padicIntAlgebraMap p K) norm_padicIntAlgebraMap_le_one ν κ.weightTest :=
  extendedCharacterRingHom_apply _ _ _ ν

/-- The measure function of a Dirac measure is evaluation of the weight. -/
@[simp]
theorem measureFun_dirac (x : ℤ_[p]ˣ) (κ : WeightSpace p K) :
    measureFun K (dirac ℤ_[p] x) κ = κ x :=
  extendedCharacterRingHom_dirac _ _ _ x

/-- The integral of the power weight `x ↦ x ^ k` is the image in `K` of the moment
`ν(x ↦ x ^ k)`. -/
theorem measureFun_inclusion_pow (ν : D(ℤ_[p]ˣ, ℤ_[p])) (k : ℕ) :
    measureFun K ν (WeightSpace.inclusion K ^ k) =
      padicIntAlgebraMap p K (ν (PadicInt.unitsPowCharacter p k)) := by
  rw [← characterIntegralAlgHom_apply]
  exact extendedCharacterRingHom_apply_eq_characterIntegralAlgHom _ _ _
    continuous_padicIntAlgebraMap _ (fun x ↦ by simp [ContinuousMonoidHom.pow_apply]) ν

/-- Dirac measures attain the bound `norm_measureFun_le_one` at every weight. -/
theorem norm_measureFun_dirac (x : ℤ_[p]ˣ) (κ : WeightSpace p K) :
    ‖measureFun K (dirac ℤ_[p] x) κ‖ = 1 := by
  simpa using norm_apply_eq_one_of_compactSpace κ x

variable (K) in
/-- **Weights separate integral measures**: an integral measure on `ℤ_pˣ` is determined by its
integrals against the `K`-valued weights. The power weights `x ↦ x ^ k` already suffice. -/
theorem measureFun_injective : Function.Injective (measureFun (p := p) K) :=
  (injective_iff_map_eq_zero _).2 fun ν hν ↦ units_eq_zero_of_positive_moments ν fun k _ ↦
    padicIntAlgebraMap_injective (K := K) <| by
      rw [map_zero, ← measureFun_inclusion_pow, hν, Pi.zero_apply]

end MeasureFun

section Norm

variable {K : Type*} [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- The measure function is bounded by the norm of the coefficient extension of the measure. -/
theorem norm_measureFun_le (ν : D(ℤ_[p]ˣ, ℤ_[p])) (κ : WeightSpace p K) :
    ‖measureFun K ν κ‖ ≤ ‖toCLMEquiv
      (extendCoefficients (padicIntAlgebraMap p K) norm_padicIntAlgebraMap_le_one ν)‖ := by
  -- The weight takes values of norm one, so its test function has norm at most one.
  have hκ : ‖(κ.weightTest : C(ℤ_[p]ˣ, K))‖ ≤ 1 :=
    (ContinuousMap.norm_le _ zero_le_one).2 fun x ↦
      (norm_apply_eq_one_of_compactSpace κ x).le
  rw [measureFun_apply, ← coe_toCLMEquiv]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hκ)

/-- The measure function of an integral measure takes values in the closed unit ball. -/
theorem norm_measureFun_le_one (ν : D(ℤ_[p]ˣ, ℤ_[p])) (κ : WeightSpace p K) :
    ‖measureFun K ν κ‖ ≤ 1 :=
  (norm_measureFun_le ν κ).trans
    (norm_toCLMEquiv_extendCoefficients_le _ norm_padicIntAlgebraMap_le_one ν)

end Norm

/-! The measure function is additive on sums and multiplicative on convolutions of Dirac
measures, and `δ_a - δ_b` vanishes at the trivial weight but not at the weight `x ↦ x`. -/

section Examples

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

example (a b : ℤ_[p]ˣ) (κ : WeightSpace p K) :
    measureFun K (dirac ℤ_[p] a + dirac ℤ_[p] b) κ = κ a + κ b := by
  simp

example (a b : ℤ_[p]ˣ) (κ : WeightSpace p K) :
    measureFun K (dirac ℤ_[p] a * dirac ℤ_[p] b) κ = κ a * κ b := by
  simp [dirac_mul_dirac]

example (a b : ℤ_[p]ˣ) : measureFun K (dirac ℤ_[p] a - dirac ℤ_[p] b) 1 = 0 := by
  simp

example {a b : ℤ_[p]ˣ} (hab : a ≠ b) :
    measureFun K (dirac ℤ_[p] a - dirac ℤ_[p] b) (WeightSpace.inclusion K) ≠ 0 := by
  simpa [sub_eq_zero, PadicInt.coe_inj, Units.val_inj] using hab

/-- Over `ℂ_p`, the measure function of an integral measure is bounded by one. -/
example (ν : D(ℤ_[p]ˣ, ℤ_[p])) (κ : WeightSpace p ℂ_[p]) : ‖measureFun ℂ_[p] ν κ‖ ≤ 1 :=
  norm_measureFun_le_one ν κ

end Examples

end TauCeti
