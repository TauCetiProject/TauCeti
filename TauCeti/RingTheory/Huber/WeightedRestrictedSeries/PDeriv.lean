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
when for every open additive subgroup `U` almost all of its coefficients lie in `U`. When open
additive subgroups form a neighbourhood basis of zero, as over a `NonarchimedeanAddGroup`, this
says that the coefficients tend to zero along the cofinite filter; over `ℝ` it is vacuous. The
formal partial derivative `MvPowerSeries.pderiv j` multiplies the coefficient of `X^(ν + eⱼ)` by
the integer `νⱼ + 1` and moves it to `X^ν`. Since `U` is closed under integer multiples, this
preserves the condition. Over a complete nonarchimedean ring this is what makes the Jacobian
matrix of a family of restricted series a matrix of restricted series, which can be evaluated at
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
if almost all coefficients of `f` lie in each open additive subgroup, then so do those of
`∂f/∂Xⱼ`. Over a nonarchimedean ring this says that if the coefficients of `f` tend to zero, so do
those of `∂f/∂Xⱼ`. -/
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
