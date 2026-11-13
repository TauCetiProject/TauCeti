/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Birkhoff averages of the `Lᵖ` composition operator

The Birkhoff sums and averages of the composition (Koopman) operator of a measure-preserving map
`T` on `Lᵖ` are elements of `Lᵖ`, while the ergodic theorems a probabilist states are about the
pointwise Birkhoff averages `birkhoffAverage 𝕜 T f n` of an observable. This file records that the
two agree: an `Lᵖ` Birkhoff average of `g` is represented by the pointwise Birkhoff average of the
coercion `⇑g`. For another representative `f =ᵐ[μ] ⇑g`, compose with Mathlib's
`QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq`.

## Main results

* `MeasureTheory.Lp.coeFn_iterate_compMeasurePreserving` — iterating the composition operator
  composes with the iterated transformation;
* `MeasureTheory.Lp.coeFn_birkhoffSum_compMeasurePreserving` and
  `MeasureTheory.Lp.coeFn_birkhoffAverage_compMeasurePreserving` — the Birkhoff sums and averages
  of the composition operator are represented by the pointwise Birkhoff sums and averages of the
  coercion of the argument; the averages may be taken over any normed division ring acting
  boundedly on the target.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω} {p : ℝ≥0∞}
  {T : Ω → Ω}

/-- Iterating the `Lᵖ` composition operator composes with the iterated transformation. -/
theorem coeFn_iterate_compMeasurePreserving (g : Lp E p μ) (hT : MeasurePreserving T μ μ)
    (n : ℕ) : ⇑((compMeasurePreserving T hT)^[n] g) =ᵐ[μ] ⇑g ∘ T^[n] := by
  rw [compMeasurePreserving_iterate hT n]
  exact coeFn_compMeasurePreserving g (hT.iterate n)

/-- The Birkhoff sums of the `Lᵖ` composition operator are represented by the pointwise Birkhoff
sums of the coercion of `g`. -/
theorem coeFn_birkhoffSum_compMeasurePreserving (g : Lp E p μ) (hT : MeasurePreserving T μ μ)
    (n : ℕ) : ⇑(birkhoffSum (compMeasurePreserving T hT) id n g) =ᵐ[μ] birkhoffSum T (⇑g) n := by
  have hsum : birkhoffSum T (⇑g) n = ∑ k ∈ Finset.range n, ⇑g ∘ T^[k] := by
    ext ω
    simp [birkhoffSum]
  rw [hsum, birkhoffSum]
  exact (coeFn_finsetSum _ _).trans
    (eventuallyEq_sum fun k _ => coeFn_iterate_compMeasurePreserving g hT k)

/-- The Birkhoff averages of the `Lᵖ` composition operator are represented by the pointwise
Birkhoff averages of the coercion of `g`. -/
theorem coeFn_birkhoffAverage_compMeasurePreserving (𝕜 : Type*) [NormedDivisionRing 𝕜]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (g : Lp E p μ) (hT : MeasurePreserving T μ μ) (n : ℕ) :
    ⇑(birkhoffAverage 𝕜 (compMeasurePreserving T hT) id n g) =ᵐ[μ] birkhoffAverage 𝕜 T (⇑g) n := by
  filter_upwards [coeFn_birkhoffSum_compMeasurePreserving g hT n,
    coeFn_smul ((n : 𝕜)⁻¹) (birkhoffSum (compMeasurePreserving T hT) id n g)] with ω hsum hsmul
  rw [birkhoffAverage, hsmul, Pi.smul_apply, hsum, birkhoffAverage]

end MeasureTheory.Lp
