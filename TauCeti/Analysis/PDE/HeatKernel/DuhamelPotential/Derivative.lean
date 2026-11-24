/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Holder
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The Duhamel heat potential commutes with spatial derivatives of the forcing

For a forcing term `f : ℝ → E → F`, the Duhamel heat potential
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` is built from convolutions in space, so it commutes
with the spatial derivatives of the forcing: if for `0 ≤ s ≤ t` every `f(s, ·)` has a continuous
derivative `f'(s, ·)`, and `f`, `f'` are jointly measurable and bounded there, then at the time
`t ≥ 0` the potential `w(t, ·)` is differentiable with derivative the potential of `f'`
(`TauCeti.hasFDerivAt_heatDuhamelPotential`).

The derivative is taken under the time integral of the Cauchy form
`w(t, x) = ∫₀ᵗ u_{f(s, ·)}(t - s, x) ds` of the potential
(`TauCeti.heatDuhamelPotential_eq_integral_heatCauchyPotential`), where the Cauchy potential
`u_g(τ, x) = ∫ K_1(y) g(x - √τ • y) dy` of a function with bounded continuous derivative has the
Cauchy potential of the derivative as its derivative
(`TauCeti.hasFDerivAt_heatCauchyPotential`), with the supremum of `‖f'‖` as a uniform bound.
Unlike the derivatives of the potential computed through derivatives of the heat kernel, this
needs no Hölder continuity of the forcing and no positivity of `t`, and it applies to every order
of differentiability of the forcing. It is how spatial regularity of the forcing passes to the
potential in the parabolic Hölder spaces of every order.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Set Filter Topology
open scoped Convolution Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Spatial derivatives of the Duhamel potential.** Let `0 ≤ t`, let `f` and `f'` be jointly
strongly measurable, and for `0 ≤ s ≤ t` let `f(s, ·)` and `f'(s, ·)` be bounded by `M` and `M'`,
with `f'(s, ·)` continuous and `f'(s, y)` the derivative of `f(s, ·)` at every `y`. Then the Duhamel
potential `w(t, ·)` of `f` is differentiable, with derivative the Duhamel potential of `f'`. -/
theorem hasFDerivAt_heatDuhamelPotential {f : ℝ → E → F} {f' : ℝ → E → E →L[ℝ] F} {M M' t : ℝ}
    (hf : StronglyMeasurable (Function.uncurry f)) (hf' : StronglyMeasurable (Function.uncurry f'))
    (hM : ∀ s ∈ Icc 0 t, ∀ y, ‖f s y‖ ≤ M) (hM' : ∀ s ∈ Icc 0 t, ∀ y, ‖f' s y‖ ≤ M')
    (hd : ∀ s ∈ Icc 0 t, ∀ y, HasFDerivAt (f s) (f' s y) y)
    (hc : ∀ s ∈ Icc 0 t, Continuous (f' s)) (ht : 0 ≤ t) (x : E) :
    HasFDerivAt (heatDuhamelPotential f t) (heatDuhamelPotential f' t x) x := by
  have hw : heatDuhamelPotential f t = fun y ↦ ∫ r in 0..t, heatCauchyPotential (f r) (t - r) y :=
    funext (heatDuhamelPotential_eq_integral_heatCauchyPotential ht)
  rw [hw, heatDuhamelPotential_eq_integral_heatCauchyPotential ht]
  have hmem : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  have hIcc : ∀ r ∈ Ι 0 t, r ∈ Icc 0 t := fun r hr ↦ by
    rw [uIoc_of_le ht] at hr
    exact ⟨hr.1.le, hr.2⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ M')
    univ_mem (Eventually.of_forall fun y ↦ ?_)
    (intervalIntegrable_heatDuhamelPotential_integrand hf hM hmem t x)
    (intervalIntegrable_heatDuhamelPotential_integrand hf' hM' hmem t x).def'.aestronglyMeasurable
    (ae_of_all _ fun r hr y _ ↦ norm_heatCauchyPotential_le (hM' r (hIcc r hr)) (t - r) y)
    intervalIntegrable_const
    (ae_of_all _ fun r hr y _ ↦ hasFDerivAt_heatCauchyPotential (hd r (hIcc r hr))
      (hc r (hIcc r hr)) (hM' r (hIcc r hr)) (t - r) y)
  exact (intervalIntegrable_heatDuhamelPotential_integrand hf hM hmem t y).def'.aestronglyMeasurable

end TauCeti
