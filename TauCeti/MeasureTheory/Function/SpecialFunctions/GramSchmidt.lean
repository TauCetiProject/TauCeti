/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurability of Gram–Schmidt orthogonalization

Gram–Schmidt orthogonalization and normalization preserve measurable families, including
linearly dependent families. Unlike continuity, measurability needs no independence
hypothesis: scalar inversion is Borel measurable even at zero. This permits measurable
orthogonal projections onto spans of families whose rank varies.

The constructions are Mathlib's `InnerProductSpace.gramSchmidt` and
`InnerProductSpace.gramSchmidtNormed`, with their existing zero-vector convention.
-/

public section

open Finset InnerProductSpace

variable {𝕜 E X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace X]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] {v : ι → X → E}

attribute [local instance] IsWellOrder.toHasWellFounded

/-- Gram–Schmidt orthogonalization preserves measurable families, without an independence
hypothesis. -/
@[fun_prop]
theorem Measurable.gramSchmidt (hv : ∀ i, Measurable (v i)) (n : ι) :
    Measurable fun x ↦ InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i x) n := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    have hformula (x : X) : InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i x) n =
        v n x - ∑ i ∈ Iio n,
          (Inner.inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j x) i) (v n x) /
            (‖InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j x) i‖ : 𝕜) ^ 2) •
              InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j x) i :=
      eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 (fun i ↦ v i x) n).symm
    simp only [hformula]
    refine (hv n).sub <| Finset.measurable_sum _ fun i hi ↦ ?_
    have hg := ih i (mem_Iio.mp hi)
    exact ((hg.inner (hv n)).div
      ((RCLike.continuous_ofReal.measurable.comp hg.norm).pow_const 2)).smul hg

/-- Normalized Gram–Schmidt orthogonalization preserves measurable families; vectors
that vanish during orthogonalization remain zero. -/
@[fun_prop]
theorem Measurable.gramSchmidtNormed (hv : ∀ i, Measurable (v i)) (n : ι) :
    Measurable fun x ↦ gramSchmidtNormed 𝕜 (fun i ↦ v i x) n := by
  have hg := Measurable.gramSchmidt (𝕜 := 𝕜) hv n
  exact ((RCLike.continuous_ofReal.measurable.comp hg.norm).inv).smul hg
