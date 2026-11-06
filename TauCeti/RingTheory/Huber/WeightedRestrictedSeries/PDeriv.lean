/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Partial derivatives of restricted power series

A power series over a topological ring is restricted, for the trivial weight family `Tᵢ = {1}`,
when its coefficients tend to zero along the cofinite filter. The formal partial derivative
`MvPowerSeries.pderiv j` multiplies the coefficient of `X^(ν + eⱼ)` by the integer `νⱼ + 1` and
moves it to `X^ν`, so it preserves this condition. This is what makes the Jacobian matrix of a
family of restricted series a matrix of restricted series, which can be evaluated at
power-bounded points.

For a general weight family the statement fails: the weight `T^(ν + eⱼ)` controlling the old
coefficient need not be contained in the weight `T^ν` controlling the new one.

## Main results

* `TauCeti.Huber.IsWeightedRestricted.pderiv_one_weight`: partial derivatives of restricted
  series are restricted.
-/

public section

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Partial derivatives of restricted series are restricted**, for the trivial weight family:
if the coefficients of `f` tend to zero, so do those of `∂f/∂Xⱼ`. -/
theorem IsWeightedRestricted.pderiv_one_weight {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f) (j : Fin k) :
    IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) (MvPowerSeries.pderiv j f) := by
  rw [isWeightedRestricted_iff] at hf ⊢
  intro U
  filter_upwards [(add_left_injective (Finsupp.single j 1)).tendsto_cofinite.eventually (hf U)]
    with ν hν
  rw [weightMul_one_weight] at hν ⊢
  rw [MvPowerSeries.coeff_pderiv, ← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
  exact nsmul_mem hν _

end TauCeti.Huber
