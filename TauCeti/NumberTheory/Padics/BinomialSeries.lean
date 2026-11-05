/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The `p`-adic binomial series depends continuously on its exponent

For a `p`-adic integer `u`, the binomial series `(1 + X) ^ u = ∑ₖ (u choose k) Xᵏ` is a power
series over `ℤ_[p]`. Its coefficients `u ↦ (u choose k)` are continuous functions of `u`
(`PadicInt.continuous_choose`), so for the product topology on `ℤ_[p]⟦X⟧` the series itself depends
continuously on `u`. This is the continuity that lets an identity between `(1 + X) ^ u` and a
`p`-adic power, valid for natural exponents, be extended to all `p`-adic exponents by density of
`ℕ` in `ℤ_[p]`.

## Main results

* `PadicInt.continuous_binomialSeries`: `u ↦ binomialSeries ℤ_[p] u` is continuous for the product
  topology on `ℤ_[p]⟦X⟧`.
* `Continuous.powerSeries_subst_binomialSeries_sub_one`: binomial substitution depends
  continuously on both the exponent and the outer series, in any topological p-adic algebra
  with continuous scalar action. This permits dilation identities to extend from natural to
  p-adic parameters.
-/

public section

open PowerSeries.WithPiTopology

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **The binomial series `(1 + X) ^ u` is a continuous function of the exponent `u ∈ ℤ_[p]`**, for
the product topology on `ℤ_[p]⟦X⟧`: each coefficient `u ↦ (u choose k)` is continuous. -/
theorem continuous_binomialSeries :
    Continuous fun u : ℤ_[p] ↦ PowerSeries.binomialSeries ℤ_[p] u := by
  refine continuous_iff_continuousAt.mpr fun u ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  exact (continuous_choose n).continuousAt

end PadicInt

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Binomial substitution depends continuously on both the exponent and an independently
varying outer series, for the coefficientwise topologies. -/
theorem Continuous.powerSeries_subst_binomialSeries_sub_one {p : ℕ} [Fact p.Prime]
    {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [ContinuousSMul ℤ_[p] R] [TopologicalSpace A]
    {F : A → R⟦X⟧} {a : A → ℤ_[p]} (hF : Continuous F) (ha : Continuous a) :
    Continuous fun s ↦ (F s).subst (binomialSeries R (a s) - 1) := by
  have hb : Continuous fun s ↦ binomialSeries R (a s) := by
    refine continuous_iff_continuousAt.mpr fun s ↦
      (WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_
    simp only [binomialSeries_coeff]
    exact (((PadicInt.continuous_choose n).comp ha).smul continuous_const).continuousAt
  exact hF.powerSeries_subst (hb.sub continuous_const) (fun s ↦ by simp)
