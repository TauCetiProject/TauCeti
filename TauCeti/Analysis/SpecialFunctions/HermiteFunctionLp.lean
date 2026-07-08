module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.Analysis.SpecialFunctions.HermiteFunctionMemLp
import TauCeti.Analysis.InnerProductSpace.RCLike

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

/-! ## Zeroth-mode normalization -/

/-- The zeroth `Lp` Hermite function has inner product one with itself, over any `RCLike`
scalar field. -/
@[simp] lemma inner_hermiteFunctionLp_zero_zero :
    inner 𝕜 (hermiteFunctionLp 𝕜 0) (hermiteFunctionLp 𝕜 0) = 1 := by
  calc
    inner 𝕜 (hermiteFunctionLp 𝕜 0) (hermiteFunctionLp 𝕜 0)
      = ∫ x : ℝ, (algebraMap ℝ 𝕜) (hermiteFunction 0 x * hermiteFunction 0 x) := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) 0] with x hx
        rw [hx]
        exact inner_algebraMap_algebraMap (𝕜 := 𝕜)
          (hermiteFunction 0 x) (hermiteFunction 0 x)
    _ = 1 := by
        rw [integral_ofReal]
        simpa only [map_one] using
          congrArg (algebraMap ℝ 𝕜) integral_hermiteFunction_zero_mul_self

end TauCeti
