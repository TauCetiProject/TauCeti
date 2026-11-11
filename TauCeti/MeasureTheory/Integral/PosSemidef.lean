/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals of positive-semidefinite matrices

An entrywise integral of an almost everywhere positive-semidefinite family of real or complex
matrices is positive semidefinite: its quadratic form is the integral of the pointwise quadratic
forms.  This is how positive semidefiniteness passes from a pointwise identity to a matrix of
moments, such as the connection matrices of a homomorphism density.

## Main results

* `TauCeti.posSemidef_integral` — the entrywise integral of an a.e. positive-semidefinite family of
  finite matrices over an `RCLike` field with integrable entries is positive semidefinite.
-/

public section

namespace TauCeti

open Matrix MeasureTheory
open scoped ComplexOrder

/-- The **entrywise integral of positive-semidefinite matrices** is positive semidefinite: if
`M x` is positive semidefinite for almost every `x` and every entry of `M` is integrable, then the
matrix of entrywise integrals is positive semidefinite. -/
theorem posSemidef_integral {α ι 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [Finite ι]
    [RCLike 𝕜] {M : α → Matrix ι ι 𝕜} (hM : ∀ᵐ x ∂μ, (M x).PosSemidef)
    (hint : ∀ i j, Integrable (fun x => M x i j) μ) :
    (Matrix.of fun i j => ∫ x, M x i j ∂μ).PosSemidef := by
  have := Fintype.ofFinite ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply, RCLike.star_def, ← integral_conj]
    exact integral_congr_ae (hM.mono fun x hx => hx.isHermitian.apply i j)
  · have hquad : star c ⬝ᵥ ((Matrix.of fun i j => ∫ x, M x i j ∂μ) *ᵥ c) =
        ∫ x, star c ⬝ᵥ (M x *ᵥ c) ∂μ := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      rw [integral_finsetSum _ fun i _ =>
        (integrable_finsetSum _ fun j _ => (hint i j).mul_const (c j)).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const (c j)]
      simp only [integral_mul_const]
    rw [hquad]
    exact integral_nonneg_of_ae (hM.mono fun x hx => hx.dotProduct_mulVec_nonneg c)

end TauCeti
