/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import TauCeti.Analysis.Calculus.Taylor.Integral

/-!
# Directional Taylor remainders in iterated-gradient form

Combining `TauCeti.sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv` with the unconditional
contraction identity `TauCeti.fullContractL_iteratedGradientChain` expresses the degree-`m` Taylor
remainder of a real-valued function `f` at `x` expanded about `y` on a complete real inner product
space as an integral over `s ∈ (0, 1)` of `IteratedGradient.fullContractL m (x - y)` applied to
`iteratedGradientChain f m (x + s • (y - x))` weighted by `s ^ m`: the basepoint `x` of the
homothety `y ↦ x + s • (y - x)` is fixed as `y` varies, preparing the spatial ray change of
variables used in potential and averaged Taylor estimates.

## Main declarations

* `TauCeti.sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL`: the scalar inner-product Taylor
  integral remainder in terms of `IteratedGradient.fullContractL` and `iteratedGradientChain`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Nat

namespace TauCeti

section InnerProductRemainder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Taylor's integral remainder in iterated-gradient form.** For a real-valued function `f` on a
complete real inner product space that is `C^{m+1}` along the segment between `x` and `y`, the
degree-`m` Taylor remainder of `f x` about `y` is `(m !)⁻¹` times the integral over `s ∈ (0, 1)` of
`s ^ m` against the full contraction of `iteratedGradientChain f m (x + s • (y - x))` in direction
`x - y`. -/
theorem sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL (f : E → ℝ) (m : ℕ) (x y : E)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (m + 1) f (x + s • (y - x))) :
    f x - ∑ j ∈ Finset.range (m + 1),
        (j ! : ℝ)⁻¹ * iteratedFDeriv ℝ j f y (fun _ ↦ x - y) =
      (m ! : ℝ)⁻¹ * ∫ s in Ioo (0 : ℝ) 1,
        s ^ m * IteratedGradient.fullContractL m (x - y)
          (iteratedGradientChain f m (x + s • (y - x))) := by
  simpa only [smul_eq_mul, fullContractL_iteratedGradientChain] using
    sub_sum_iteratedFDeriv_eq_setIntegral_iteratedFDeriv f m x y hf

end InnerProductRemainder

-- Concrete checks: degree-2 expansion of a linear map `t ↦ 2 * t` leaves zero remainder, while
-- degree-0 expansion from `y = 1` to `x = 4` leaves `8 - 2 = 6 = ∫₀¹ 2 * 3 ds`.
example :
    (2 * (4 : ℝ)) - ∑ j ∈ Finset.range 3,
        (j ! : ℝ)⁻¹ * iteratedFDeriv ℝ j (fun t : ℝ ↦ 2 * t) 1 (fun _ ↦ (4 : ℝ) - 1) = 0 := by
  let L : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hclm : (fun t : ℝ ↦ 2 * t) = ⇑L := by ext t; simp [L]
  rw [sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL (fun t : ℝ ↦ 2 * t) 2 4 1
    (fun s _ ↦ by rw [hclm]; exact L.contDiff.contDiffAt)]
  have hgrad : gradient (fun t : ℝ ↦ 2 * t) = Function.const ℝ (2 : ℝ) := by
    ext t
    apply ext_inner_right ℝ fun v ↦ ?_
    rw [gradient, InnerProductSpace.toDual_symm_apply, hclm, L.fderiv]
    simp [L, RCLike.inner_apply, mul_comm]
  have hzero : ∀ z : ℝ, iteratedGradientChain (fun t : ℝ ↦ 2 * t) 2 z = 0 := fun z ↦ by
    rw [iteratedGradientChain_succ, iteratedGradientChain_succ, iteratedGradientChain_zero,
      hgrad, fderiv_const, Pi.zero_def, fderiv_const_apply]
  simp only [hzero, map_zero, mul_zero, integral_zero]

example :
    (2 * (4 : ℝ)) - ∑ j ∈ Finset.range 1,
        (j ! : ℝ)⁻¹ * iteratedFDeriv ℝ j (fun t : ℝ ↦ 2 * t) 1 (fun _ ↦ (4 : ℝ) - 1) = 6 := by
  rw [Finset.sum_range_one, iteratedFDeriv_zero_apply]
  norm_num

end TauCeti
