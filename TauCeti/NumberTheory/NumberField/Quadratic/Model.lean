/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
public import Mathlib.RingTheory.QuadraticAlgebra
public import TauCeti.NumberTheory.NumberField.Quadratic.ComplexEmbedding
public import TauCeti.NumberTheory.NumberField.IntegralSqrt

/-!
# The ring of integers of the model `ℚ(√d)`

For a squarefree nonsquare integer `d`, the model `QuadraticAlgebra ℚ d 0` of `ℚ(√d)` is a number
field (`QuadraticAlgebra.instNumberField`). This file identifies its ring of integers with an
explicit integral quadratic algebra:

* if `d ≢ 1 (mod 4)`, then `𝓞 ℚ(√d) ≃ₐ[ℤ] QuadraticAlgebra ℤ d 0`, the ring `ℤ[√d]`; the
  element `z` of the integral model is sent to `z.re + z.im • ω`, so the coordinates of an
  algebraic integer are its rational coordinates in `ℚ(√d)`;
* if `d ≡ 1 (mod 4)`, then `𝓞 ℚ(√d) ≃ₐ[ℤ] QuadraticAlgebra ℤ ((d - 1) / 4) 1`, the ring
  `ℤ[(1 + √d)/2]`, whose generator squares to `(d - 1)/4 + ω`; the element `z` is sent to
  `z.re + z.im • (1 + ω)/2`.

These are the intrinsic results `NumberField.adjoin_gen_eq_top_of_mod_four_ne_one` and
`NumberField.adjoin_halfGen_eq_top_of_mod_four_eq_one`, applied to the generator `ω` of the model.
Through the equivalences, the field norm and trace of an algebraic integer become the norm and trace
forms of the integral models, an element of `ℚ(√d)` is integral exactly when its coordinates pass
an explicit integrality test, and the field discriminant is `4d`, respectively `d`. For `d < 0` the
distinguished complex embedding `QuadraticAlgebra.complexEmbedding` maps the ring of integers onto
the lattice `ℤ + ℤ √(-d) i`, respectively `ℤ + ℤ (1 + √(-d) i)/2`.

## Main definitions and results

* `QuadraticAlgebra.ringOfIntegersEquiv`: `𝓞 ℚ(√d) ≃ₐ[ℤ] ℤ[√d]` for `d ≢ 1 (mod 4)`.
* `QuadraticAlgebra.ringOfIntegersEquivHalf`: `𝓞 ℚ(√d) ≃ₐ[ℤ] ℤ[(1 + √d)/2]` for `d ≡ 1 (mod 4)`.
* `QuadraticAlgebra.isIntegral_iff_of_mod_four_ne_one`, `isIntegral_iff_of_mod_four_eq_one`: the
  coordinate tests for integrality.
* `QuadraticAlgebra.norm_ringOfIntegersEquiv_symm`, `norm_ringOfIntegersEquivHalf_symm` and the
  matching `trace_*`: the norm and trace of an algebraic integer in its integral coordinates.
* `QuadraticAlgebra.complexEmbedding_ringOfIntegersEquiv_symm`,
  `complexEmbedding_ringOfIntegersEquivHalf_symm`: the complex image of an algebraic integer.
* `QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one`, `discr_eq_of_mod_four_eq_one`: the
  discriminant of the model.
* `QuadraticAlgebra.minpoly_integralSqrt_omega`, `adjoin_integralSqrt_omega`: the generator `ω`
  of the model satisfies the hypotheses of the intrinsic quadratic API, and
  `ringOfIntegersEquiv_symm_omega`, `ringOfIntegersEquivHalf_symm_omega` identify the generators
  of the integral models with `NumberField.integralSqrt` and `NumberField.halfGen`.

## References

* D. A. Marcus, *Number Fields*, Chapter 2.
-/

public section

open Polynomial NumberField

namespace QuadraticAlgebra

variable {d : ℤ} [Fact (¬ IsSquare d)]

/-- The generator `ω` of the model `ℚ(√d)` squares to the integer `d`. -/
theorem omega_sq_eq_algebraMap_int :
    (ω : QuadraticAlgebra ℚ (d : ℚ) 0) ^ 2 = algebraMap ℤ (QuadraticAlgebra ℚ (d : ℚ) 0) d := by
  rw [sq, omega_mul_omega_eq_mk]
  ext <;> simp

private theorem integralSqrt_mul_self :
    (integralSqrt (omega_sq_eq_algebraMap_int (d := d)) *
        integralSqrt (omega_sq_eq_algebraMap_int (d := d)) : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) =
      d • 1 + (0 : ℤ) • integralSqrt (omega_sq_eq_algebraMap_int (d := d)) := by
  rw [← sq, integralSqrt_sq]
  simp

/-- The generator `ω` of the model, as an algebraic integer, has minimal polynomial `X ^ 2 - d`
over `ℤ`. This is the hypothesis `minpoly ℤ θ = X ^ 2 - C d` of the intrinsic quadratic API in
`TauCeti.NumberTheory.NumberField.Quadratic`. -/
theorem minpoly_integralSqrt_omega :
    minpoly ℤ (integralSqrt (omega_sq_eq_algebraMap_int (d := d))) = X ^ 2 - C d :=
  minpoly_integralSqrt omega_sq_eq_algebraMap_int Fact.out

/-- The generator `ω` of the model, as an algebraic integer, generates `ℚ(√d)` over `ℚ`. -/
theorem adjoin_integralSqrt_omega :
    Algebra.adjoin ℚ {((integralSqrt (omega_sq_eq_algebraMap_int (d := d)) :
      𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) : QuadraticAlgebra ℚ (d : ℚ) 0)} = ⊤ := by
  rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_integralSqrt]
  exact adjoin_omega_eq_top

/-! ### The case `d ≢ 1 (mod 4)`: `𝓞 ℚ(√d) = ℤ[√d]` -/

section ModFourNeOne

/-- The integral model `ℤ[√d]` maps into the ring of integers by `ω ↦ √d`. -/
private noncomputable def toRingOfIntegers :
    QuadraticAlgebra ℤ d 0 →ₐ[ℤ] 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) :=
  lift ⟨integralSqrt (omega_sq_eq_algebraMap_int (d := d)), integralSqrt_mul_self⟩

private theorem coe_toRingOfIntegers (z : QuadraticAlgebra ℤ d 0) :
    (toRingOfIntegers z : QuadraticAlgebra ℚ (d : ℚ) 0) = ⟨z.re, z.im⟩ := by
  ext <;> simp [toRingOfIntegers, zsmul_eq_mul]

private theorem toRingOfIntegers_bijective (hsf : Squarefree d) (hd4 : d % 4 ≠ 1) :
    Function.Bijective (toRingOfIntegers (d := d)) := by
  refine ⟨fun z w h => ?_, ?_⟩
  · have h' := congrArg (fun x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) =>
      (x : QuadraticAlgebra ℚ (d : ℚ) 0)) h
    simp only [coe_toRingOfIntegers, QuadraticAlgebra.mk.injEq, Int.cast_inj] at h'
    exact QuadraticAlgebra.ext h'.1 h'.2
  · rw [toRingOfIntegers, lift_surjective_iff]
    exact adjoin_gen_eq_top_of_mod_four_ne_one minpoly_integralSqrt_omega
      adjoin_integralSqrt_omega hsf hd4

/-- **The ring of integers of `ℚ(√d)` for `d ≢ 1 (mod 4)`.** For squarefree `d` with
`d % 4 ≠ 1`, the ring of integers of the model `QuadraticAlgebra ℚ d 0` is the integral model
`QuadraticAlgebra ℤ d 0 = ℤ[√d]`, with the same coordinates (`ringOfIntegersEquiv_symm_apply_coe`,
`ringOfIntegersEquiv_apply_re`, `ringOfIntegersEquiv_apply_im`). -/
noncomputable def ringOfIntegersEquiv (hsf : Squarefree d) (hd4 : d % 4 ≠ 1) :
    𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) ≃ₐ[ℤ] QuadraticAlgebra ℤ d 0 :=
  (AlgEquiv.ofBijective toRingOfIntegers (toRingOfIntegers_bijective hsf hd4)).symm

variable (hsf : Squarefree d) (hd4 : d % 4 ≠ 1)

/-- The inverse of `ringOfIntegersEquiv` is the inclusion of `ℤ[√d]` into `ℚ(√d)`. -/
@[simp] theorem ringOfIntegersEquiv_symm_apply_coe (z : QuadraticAlgebra ℤ d 0) :
    ((ringOfIntegersEquiv hsf hd4).symm z : QuadraticAlgebra ℚ (d : ℚ) 0) = ⟨z.re, z.im⟩ :=
  coe_toRingOfIntegers z

/-- The generator `√d` of `ℤ[√d]` corresponds to the intrinsic square root `ω` of `ℚ(√d)`. -/
theorem ringOfIntegersEquiv_symm_omega :
    (ringOfIntegersEquiv hsf hd4).symm ω = integralSqrt (omega_sq_eq_algebraMap_int (d := d)) := by
  ext <;> simp

/-- The generator of `ℤ[√d]` has minimal polynomial `X ^ 2 - d` in the ring of integers. -/
theorem minpoly_ringOfIntegersEquiv_symm_omega :
    minpoly ℤ ((ringOfIntegersEquiv hsf hd4).symm ω) = X ^ 2 - C d := by
  rw [ringOfIntegersEquiv_symm_omega, minpoly_integralSqrt_omega]

/-- The rational coordinate of an algebraic integer of `ℚ(√d)`, `d ≢ 1 (mod 4)`, is its
integral coordinate. -/
@[simp] theorem ringOfIntegersEquiv_apply_re (x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) :
    ((ringOfIntegersEquiv hsf hd4 x).re : ℚ) = (x : QuadraticAlgebra ℚ (d : ℚ) 0).re := by
  conv_rhs => rw [← (ringOfIntegersEquiv hsf hd4).symm_apply_apply x,
    ringOfIntegersEquiv_symm_apply_coe]

/-- The `√d`-coordinate of an algebraic integer of `ℚ(√d)`, `d ≢ 1 (mod 4)`, is its integral
coordinate. -/
@[simp] theorem ringOfIntegersEquiv_apply_im (x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) :
    ((ringOfIntegersEquiv hsf hd4 x).im : ℚ) = (x : QuadraticAlgebra ℚ (d : ℚ) 0).im := by
  conv_rhs => rw [← (ringOfIntegersEquiv hsf hd4).symm_apply_apply x,
    ringOfIntegersEquiv_symm_apply_coe]

include hsf hd4 in
/-- **The integrality test for `d ≢ 1 (mod 4)`.** An element of `ℚ(√d)` is an algebraic integer
exactly when both of its coordinates are integers. -/
theorem isIntegral_iff_of_mod_four_ne_one (x : QuadraticAlgebra ℚ (d : ℚ) 0) :
    IsIntegral ℤ x ↔ (∃ m : ℤ, x.re = m) ∧ ∃ n : ℤ, x.im = n := by
  constructor
  · intro hx
    exact ⟨⟨_, (ringOfIntegersEquiv_apply_re hsf hd4 ⟨x, hx⟩).symm⟩,
      ⟨_, (ringOfIntegersEquiv_apply_im hsf hd4 ⟨x, hx⟩).symm⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    have hx : x = ((ringOfIntegersEquiv hsf hd4).symm ⟨m, n⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) := by
      ext <;> simp [hm, hn]
    rw [hx]
    exact RingOfIntegers.isIntegral_coe _

/-- **The norm form of `ℤ[√d]`.** For `d ≢ 1 (mod 4)` the norm of the algebraic integer
`a + b √d` is `a² - d b²`. -/
theorem norm_ringOfIntegersEquiv_symm (z : QuadraticAlgebra ℤ d 0) :
    Algebra.norm ℤ ((ringOfIntegersEquiv hsf hd4).symm z) = z.re ^ 2 - d * z.im ^ 2 := by
  rw [Algebra.norm_eq_of_algEquiv, Algebra.norm_quadraticAlgebra_apply, norm_def]
  ring

/-- For `d ≢ 1 (mod 4)` the trace of the algebraic integer `a + b √d` is `2a`. -/
theorem trace_ringOfIntegersEquiv_symm (z : QuadraticAlgebra ℤ d 0) :
    Algebra.trace ℤ _ ((ringOfIntegersEquiv hsf hd4).symm z) = 2 * z.re := by
  rw [Algebra.trace_eq_of_algEquiv, Algebra.trace_quadraticAlgebra_apply, trace_def]
  ring

/-- For `d < 0`, the distinguished complex embedding sends the algebraic integer `a + b √d` to
`a + b √(-d) i`, so the image of the ring of integers is the lattice `ℤ + ℤ √(-d) i` in `ℂ`. -/
theorem complexEmbedding_ringOfIntegersEquiv_symm (hd : (d : ℚ) ≤ 0) (z : QuadraticAlgebra ℤ d 0) :
    complexEmbedding hd ((ringOfIntegersEquiv hsf hd4).symm z) =
      z.re + z.im * ((√(-(d : ℝ)) : ℂ) * Complex.I) := by
  simp [complexEmbedding_apply]

include hsf hd4 in
/-- **The discriminant of `ℚ(√d)` for `d ≢ 1 (mod 4)`** is `4d`. -/
theorem discr_eq_four_mul_of_mod_four_ne_one :
    NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = 4 * d :=
  NumberField.discr_eq_four_mul_of_mod_four_ne_one minpoly_integralSqrt_omega
    adjoin_integralSqrt_omega hsf hd4

end ModFourNeOne

/-! ### The case `d ≡ 1 (mod 4)`: `𝓞 ℚ(√d) = ℤ[(1 + √d)/2]` -/

section ModFourEqOne

variable (hsf : Squarefree d) (hd4 : d % 4 = 1)

private theorem coe_halfGen_sqrt : algebraMap (𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))
    (QuadraticAlgebra ℚ (d : ℚ) 0) (halfGen minpoly_integralSqrt_omega hd4) =
      ⟨1 / 2, 1 / 2⟩ := by
  rw [← RingOfIntegers.coe_eq_algebraMap, coe_halfGen, div_eq_iff two_ne_zero]
  ext <;> simp

private theorem halfGen_mul_self :
    (halfGen minpoly_integralSqrt_omega hd4 * halfGen minpoly_integralSqrt_omega hd4 :
      𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) =
      ((d - 1) / 4) • 1 + (1 : ℤ) • halfGen minpoly_integralSqrt_omega hd4 := by
  have h := TauCeti.sq_one_add_div_two_sub_self (coe_gen_sq minpoly_integralSqrt_omega) hd4
  rw [← coe_halfGen minpoly_integralSqrt_omega hd4, show d / 4 = (d - 1) / 4 by omega] at h
  apply FaithfulSMul.algebraMap_injective (𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))
    (QuadraticAlgebra ℚ (d : ℚ) 0)
  rw [eq_intCast] at h
  rw [map_mul, map_add, map_zsmul, map_zsmul, map_one, one_smul,
    ← RingOfIntegers.coe_eq_algebraMap, ← sq, zsmul_one]
  linear_combination h

/-- The integral model `ℤ[(1 + √d)/2]` maps into the ring of integers by `ω ↦ (1 + √d)/2`. -/
private noncomputable def toRingOfIntegersHalf :
    QuadraticAlgebra ℤ ((d - 1) / 4) 1 →ₐ[ℤ] 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) :=
  lift ⟨halfGen minpoly_integralSqrt_omega hd4, halfGen_mul_self hd4⟩

private theorem coe_toRingOfIntegersHalf (z : QuadraticAlgebra ℤ ((d - 1) / 4) 1) :
    (toRingOfIntegersHalf hd4 z : QuadraticAlgebra ℚ (d : ℚ) 0) =
      ⟨z.re + z.im / 2, z.im / 2⟩ := by
  rw [RingOfIntegers.coe_eq_algebraMap, toRingOfIntegersHalf, lift_apply_apply, map_add,
    map_zsmul, map_zsmul, map_one, coe_halfGen_sqrt hd4]
  ext <;> simp [zsmul_eq_mul, div_eq_mul_inv]

include hsf in
private theorem toRingOfIntegersHalf_bijective :
    Function.Bijective (toRingOfIntegersHalf hd4) := by
  refine ⟨fun z w h => ?_, ?_⟩
  · have h' := congrArg (fun x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) =>
      (x : QuadraticAlgebra ℚ (d : ℚ) 0)) h
    simp only [coe_toRingOfIntegersHalf] at h'
    have hre := congrArg QuadraticAlgebra.re h'
    have him := congrArg QuadraticAlgebra.im h'
    dsimp only at hre him
    have him' : (z.im : ℚ) = w.im := by linarith
    have hre' : (z.re : ℚ) = w.re := by linarith
    exact QuadraticAlgebra.ext (by exact_mod_cast hre') (by exact_mod_cast him')
  · rw [toRingOfIntegersHalf, lift_surjective_iff]
    exact adjoin_halfGen_eq_top_of_mod_four_eq_one minpoly_integralSqrt_omega
      adjoin_integralSqrt_omega hsf hd4

/-- **The ring of integers of `ℚ(√d)` for `d ≡ 1 (mod 4)`.** For squarefree `d` with
`d % 4 = 1`, the ring of integers of the model `QuadraticAlgebra ℚ d 0` is the integral model
`QuadraticAlgebra ℤ ((d - 1) / 4) 1 = ℤ[(1 + √d)/2]`, whose generator `ω` corresponds to
`(1 + √d)/2` (`ringOfIntegersEquivHalf_symm_apply_coe`, `ringOfIntegersEquivHalf_apply_re`,
`ringOfIntegersEquivHalf_apply_im`). -/
noncomputable def ringOfIntegersEquivHalf :
    𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) ≃ₐ[ℤ] QuadraticAlgebra ℤ ((d - 1) / 4) 1 :=
  (AlgEquiv.ofBijective (toRingOfIntegersHalf hd4) (toRingOfIntegersHalf_bijective hsf hd4)).symm

/-- The inverse of `ringOfIntegersEquivHalf` sends `a + b ω` to `a + b (1 + √d)/2`. -/
@[simp] theorem ringOfIntegersEquivHalf_symm_apply_coe (z : QuadraticAlgebra ℤ ((d - 1) / 4) 1) :
    ((ringOfIntegersEquivHalf hsf hd4).symm z : QuadraticAlgebra ℚ (d : ℚ) 0) =
      ⟨z.re + z.im / 2, z.im / 2⟩ :=
  coe_toRingOfIntegersHalf hd4 z

/-- The generator of `ℤ[(1 + √d)/2]` corresponds to `(1 + √d)/2`. -/
theorem ringOfIntegersEquivHalf_symm_omega_coe :
    ((ringOfIntegersEquivHalf hsf hd4).symm ω : QuadraticAlgebra ℚ (d : ℚ) 0) = ⟨1 / 2, 1 / 2⟩ := by
  ext <;> simp

/-- The generator of `ℤ[(1 + √d)/2]` corresponds to the intrinsic half-generator
`NumberField.halfGen` of `ℚ(√d)`. -/
theorem ringOfIntegersEquivHalf_symm_omega :
    (ringOfIntegersEquivHalf hsf hd4).symm ω = halfGen minpoly_integralSqrt_omega hd4 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))
    (QuadraticAlgebra ℚ (d : ℚ) 0)
  rw [coe_halfGen_sqrt, ← RingOfIntegers.coe_eq_algebraMap, ringOfIntegersEquivHalf_symm_omega_coe]

/-- The generator of `ℤ[(1 + √d)/2]` has minimal polynomial `X ^ 2 - X - (d - 1)/4` in the ring
of integers. -/
theorem minpoly_ringOfIntegersEquivHalf_symm_omega :
    minpoly ℤ ((ringOfIntegersEquivHalf hsf hd4).symm ω) = X ^ 2 - X - C ((d - 1) / 4) := by
  rw [ringOfIntegersEquivHalf_symm_omega, minpoly_halfGen, show (1 - d) / 4 = -((d - 1) / 4) by
    omega, map_neg, ← sub_eq_add_neg]

/-- The first integral coordinate of an algebraic integer `x` of `ℚ(√d)`, `d ≡ 1 (mod 4)`, in the
basis `1, (1 + √d)/2` is `x.re - x.im`. -/
@[simp] theorem ringOfIntegersEquivHalf_apply_re (x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) :
    ((ringOfIntegersEquivHalf hsf hd4 x).re : ℚ) =
      (x : QuadraticAlgebra ℚ (d : ℚ) 0).re - (x : QuadraticAlgebra ℚ (d : ℚ) 0).im := by
  conv_rhs => rw [← (ringOfIntegersEquivHalf hsf hd4).symm_apply_apply x,
    ringOfIntegersEquivHalf_symm_apply_coe]
  ring

/-- The second integral coordinate of an algebraic integer `x` of `ℚ(√d)`, `d ≡ 1 (mod 4)`, in
the basis `1, (1 + √d)/2` is `2 x.im`. -/
@[simp] theorem ringOfIntegersEquivHalf_apply_im (x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) :
    ((ringOfIntegersEquivHalf hsf hd4 x).im : ℚ) = 2 * (x : QuadraticAlgebra ℚ (d : ℚ) 0).im := by
  conv_rhs => rw [← (ringOfIntegersEquivHalf hsf hd4).symm_apply_apply x,
    ringOfIntegersEquivHalf_symm_apply_coe]
  ring

include hsf hd4 in
/-- **The integrality test for `d ≡ 1 (mod 4)`.** An element `x` of `ℚ(√d)` is an algebraic
integer exactly when `x.re - x.im` and `2 x.im` are integers, that is, when `2 x.re` and `2 x.im`
are integers of the same parity. -/
theorem isIntegral_iff_of_mod_four_eq_one (x : QuadraticAlgebra ℚ (d : ℚ) 0) :
    IsIntegral ℤ x ↔ (∃ m : ℤ, x.re - x.im = m) ∧ ∃ n : ℤ, 2 * x.im = n := by
  constructor
  · intro hx
    exact ⟨⟨_, (ringOfIntegersEquivHalf_apply_re hsf hd4 ⟨x, hx⟩).symm⟩,
      ⟨_, (ringOfIntegersEquivHalf_apply_im hsf hd4 ⟨x, hx⟩).symm⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    have hx : x =
        ((ringOfIntegersEquivHalf hsf hd4).symm ⟨m, n⟩ : QuadraticAlgebra ℚ (d : ℚ) 0) := by
      rw [ringOfIntegersEquivHalf_symm_apply_coe]
      ext
      · simp only [← hm, ← hn]; ring
      · simp only [← hn]; ring
    rw [hx]
    exact RingOfIntegers.isIntegral_coe _

/-- **The norm form of `ℤ[(1 + √d)/2]`.** For `d ≡ 1 (mod 4)` the norm of the algebraic integer
`a + b (1 + √d)/2` is `a² + a b - (d - 1)/4 · b²`. -/
theorem norm_ringOfIntegersEquivHalf_symm (z : QuadraticAlgebra ℤ ((d - 1) / 4) 1) :
    Algebra.norm ℤ ((ringOfIntegersEquivHalf hsf hd4).symm z) =
      z.re ^ 2 + z.re * z.im - (d - 1) / 4 * z.im ^ 2 := by
  rw [Algebra.norm_eq_of_algEquiv, Algebra.norm_quadraticAlgebra_apply, norm_def]
  ring

/-- For `d ≡ 1 (mod 4)` the trace of the algebraic integer `a + b (1 + √d)/2` is `2a + b`. -/
theorem trace_ringOfIntegersEquivHalf_symm (z : QuadraticAlgebra ℤ ((d - 1) / 4) 1) :
    Algebra.trace ℤ _ ((ringOfIntegersEquivHalf hsf hd4).symm z) = 2 * z.re + z.im := by
  rw [Algebra.trace_eq_of_algEquiv, Algebra.trace_quadraticAlgebra_apply, trace_def]
  ring

/-- For `d < 0`, the distinguished complex embedding sends the algebraic integer
`a + b (1 + √d)/2` to `a + b (1 + √(-d) i)/2`, so the image of the ring of integers is the lattice
`ℤ + ℤ (1 + √(-d) i)/2` in `ℂ`. -/
theorem complexEmbedding_ringOfIntegersEquivHalf_symm (hd : (d : ℚ) ≤ 0)
    (z : QuadraticAlgebra ℤ ((d - 1) / 4) 1) :
    complexEmbedding hd ((ringOfIntegersEquivHalf hsf hd4).symm z) =
      z.re + z.im * ((1 + (√(-(d : ℝ)) : ℂ) * Complex.I) / 2) := by
  simp [complexEmbedding_apply]
  ring

include hsf hd4 in
/-- **The discriminant of `ℚ(√d)` for `d ≡ 1 (mod 4)`** is `d`. -/
theorem discr_eq_of_mod_four_eq_one : NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = d :=
  NumberField.discr_eq_of_squarefree_of_mod_four_eq_one minpoly_integralSqrt_omega
    adjoin_integralSqrt_omega hsf hd4

end ModFourEqOne

end QuadraticAlgebra
