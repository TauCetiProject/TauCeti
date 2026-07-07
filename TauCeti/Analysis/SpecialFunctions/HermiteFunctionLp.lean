module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.Analysis.SpecialFunctions.HermiteFunctionMemLp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Hermite functions as `L²` vectors

This file packages the pointwise Hermite functions `TauCeti.hermiteFunction n` as elements of
`Lp 𝕜 2 volume`, for any `RCLike` scalar field `𝕜`.  This is the `hermiteFunctionLp` family
named in the `OrthogonalL2Bases` roadmap's Part A3: the later orthonormality and Hilbert-basis
theorems use these `Lp` vectors, while the analytic `L²` membership is supplied by
`TauCeti.memLp_two_hermiteFunction`.

The a.e. representative lemmas are the anti-vacuity pins for downstream consumers: they expose
that the bundled `Lp` vectors are exactly the scalar casts of the explicit pointwise functions.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Scalar-cast `L²` membership -/

/-- The `𝕜`-valued scalar cast of a Hermite function lies in `L²(volume)`. -/
theorem memLp_two_algebraMap_hermiteFunction (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (hermiteFunction n x)) 2 volume := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_two_hermiteFunction n).ofReal (K := 𝕜)

/-- The scalar-cast zeroth Hermite function lies in `L²(volume)`. -/
theorem memLp_two_algebraMap_hermiteFunction_zero :
    MemLp (fun x : ℝ =>
      (algebraMap ℝ 𝕜) (Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi))) 2 volume := by
  simpa only [hermiteFunction_zero] using
    (memLp_two_algebraMap_hermiteFunction (𝕜 := 𝕜) 0)

/-- The scalar-cast first Hermite function lies in `L²(volume)`. -/
theorem memLp_two_algebraMap_hermiteFunction_one :
    MemLp (fun x : ℝ =>
      (algebraMap ℝ 𝕜)
        (Real.sqrt 2 * x * Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi))) 2
      volume := by
  simpa only [hermiteFunction_one_eq] using
    (memLp_two_algebraMap_hermiteFunction (𝕜 := 𝕜) 1)

/-! ## `Lp` packaging -/

/-- The `n`th Hermite function as a vector of `L²(ℝ, volume; 𝕜)`, with the real pointwise
function cast through `algebraMap ℝ 𝕜`. -/
noncomputable def hermiteFunctionLp (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Lp 𝕜 2 (volume : Measure ℝ) :=
  (memLp_two_algebraMap_hermiteFunction (𝕜 := 𝕜) n).toLp _

/-- The `Lp` representative of `hermiteFunctionLp` is the scalar cast of the pointwise
Hermite function. -/
lemma coeFn_hermiteFunctionLp (n : ℕ) :
    ⇑(hermiteFunctionLp 𝕜 n) =ᵐ[volume]
      fun x : ℝ => (algebraMap ℝ 𝕜) (hermiteFunction n x) :=
  MemLp.coeFn_toLp _

/-- In real scalars, `hermiteFunctionLp` has the original pointwise Hermite function as an
a.e. representative. -/
lemma coeFn_hermiteFunctionLp_real (n : ℕ) :
    ⇑(hermiteFunctionLp ℝ n) =ᵐ[volume] hermiteFunction n := by
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := ℝ) n] with x hx
  simpa using hx

/-- The zeroth `Lp` Hermite function is represented by the Gaussian envelope with its
normalization. -/
lemma coeFn_hermiteFunctionLp_zero :
    ⇑(hermiteFunctionLp 𝕜 0) =ᵐ[volume]
      fun x : ℝ =>
        (algebraMap ℝ 𝕜) (Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi)) := by
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) 0] with x hx
  simpa only [hermiteFunction_zero] using hx

/-- The first `Lp` Hermite function is represented by `sqrt 2 * x` times the zeroth
pointwise Hermite function. -/
lemma coeFn_hermiteFunctionLp_one :
    ⇑(hermiteFunctionLp 𝕜 1) =ᵐ[volume]
      fun x : ℝ => (algebraMap ℝ 𝕜) (Real.sqrt 2 * x * hermiteFunction 0 x) := by
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) 1] with x hx
  simpa only [hermiteFunction_one] using hx

/-- The first `Lp` Hermite function in fully expanded pointwise form. -/
lemma coeFn_hermiteFunctionLp_one_eq :
    ⇑(hermiteFunctionLp 𝕜 1) =ᵐ[volume]
      fun x : ℝ =>
        (algebraMap ℝ 𝕜)
          (Real.sqrt 2 * x * Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi)) := by
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) 1] with x hx
  simpa only [hermiteFunction_one_eq] using hx

/-- The second `Lp` Hermite function in pointwise form. -/
lemma coeFn_hermiteFunctionLp_two :
    ⇑(hermiteFunctionLp 𝕜 2) =ᵐ[volume]
      fun x : ℝ =>
        (algebraMap ℝ 𝕜)
          (((x * Real.sqrt 2) ^ 2 - 1) * Real.exp (-(x ^ 2 / 2)) /
            Real.sqrt ((2 : ℝ) * Real.sqrt Real.pi)) := by
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) 2] with x hx
  simpa only [hermiteFunction_two] using hx

/-! ## Zeroth-mode normalization -/

/-- The zeroth Hermite function has square integral one. This is the `n = 0` boundary case of
the roadmap's Hermite-function orthonormality target, using Mathlib's Gaussian integral. -/
@[simp]
lemma integral_hermiteFunction_zero_mul_self :
    ∫ x : ℝ, hermiteFunction 0 x * hermiteFunction 0 x = 1 := by
  have hsqrt_sqrt_pi_sq :
      Real.sqrt (Real.sqrt Real.pi) ^ 2 = Real.sqrt Real.pi := by
    rw [Real.sq_sqrt (Real.sqrt_nonneg Real.pi)]
  calc
    ∫ x : ℝ, hermiteFunction 0 x * hermiteFunction 0 x
        = ∫ x : ℝ,
            Real.exp (-x ^ 2) / Real.sqrt (Real.sqrt Real.pi) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [hermiteFunction_zero x]
          have henv : Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) =
              Real.exp (-x ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [div_mul_div_comm, henv]
          ring_nf
    _ = (Real.sqrt (Real.sqrt Real.pi) ^ 2)⁻¹ * ∫ x : ℝ, Real.exp (-x ^ 2) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
    _ = 1 := by
          have hgauss : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
            convert integral_gaussian (1 : ℝ) using 1
            · ring_nf
            · ring_nf
          rw [hgauss, hsqrt_sqrt_pi_sq]
          field_simp [Real.sqrt_ne_zero'.mpr (Real.sqrt_pos.2 Real.pi_pos)]

/-- The zeroth `Lp` Hermite function has inner product one with itself, over any `RCLike`
scalar field. -/
@[simp]
lemma inner_hermiteFunctionLp_zero_zero :
    inner 𝕜 (hermiteFunctionLp 𝕜 0) (hermiteFunctionLp 𝕜 0) = 1 := by
  have hinner : ∀ a b : ℝ,
      inner 𝕜 ((algebraMap ℝ 𝕜) a) ((algebraMap ℝ 𝕜) b) =
        (algebraMap ℝ 𝕜) (a * b) := by
    intro a b
    simp [RCLike.inner_apply, RCLike.conj_ofReal, map_mul, mul_comm]
  rw [MeasureTheory.L2.inner_def]
  calc
    ∫ x : ℝ, inner 𝕜 ((hermiteFunctionLp 𝕜 0) x) ((hermiteFunctionLp 𝕜 0) x) ∂volume
        = ∫ x : ℝ, (algebraMap ℝ 𝕜) (hermiteFunction 0 x * hermiteFunction 0 x) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) 0] with x hx
          rw [hx]
          exact hinner (hermiteFunction 0 x) (hermiteFunction 0 x)
    _ = 1 := by
          rw [integral_ofReal, integral_hermiteFunction_zero_mul_self]
          simp

end TauCeti
