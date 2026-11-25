/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.CharacteristicFunction
public import TauCeti.MeasureTheory.Integral.InvNondegenerateZero
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integrability of `1 / P_w` for liquid weights

For liquid type weights `w`, the characteristic function
`P_w(θ, φ) = w₃ + w₂ e^{iθ} + w₁ e^{−iφ}` vanishes at two points modulo `2π`, and at each of them
its real Jacobian is invertible (`TauCeti.linearIndependent_deriv_lozengeCharFun`). Near a zero,
`|P_w|` is therefore bounded below by a multiple of the distance to the zero, and `1 / |x|` is
integrable near `0` in the plane. This file proves:

* `TauCeti.hasFDerivAt_lozengeCharFun`: the real derivative of `P_w` at `(θ, φ)` sends `(a, b)` to
  `a (i w₂ e^{iθ}) + b (−i w₁ e^{−iφ})`;
* `TauCeti.IsLiquidWeights.locallyIntegrable_inv_lozengeCharFun`: `1 / P_w` is locally integrable
  on `ℝ²`, by `TauCeti.locallyIntegrable_inv_of_hasFDerivAt`;
* `TauCeti.IsLiquidWeights.integrableOn_inv_lozengeCharFun`: `1 / P_w` is integrable on the
  torus `(0, 2π]²`;
* `TauCeti.IsLiquidWeights.integrableOn_lozengeKernel_integrand`: so is the integrand
  `e^{i(d₁θ + d₂φ)} / P_w(θ, φ)` of the kernel `G_w(d)`, which is therefore a genuine Lebesgue
  integral.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009),
  Section 6.1.
* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  Theorem 4.3.
-/

public section

noncomputable section

open Complex Set MeasureTheory

namespace TauCeti

variable {w₁ w₂ w₃ : ℝ}

/-- **The real derivative of `P_w`.** At `x = (θ, φ)`, the derivative of
`(θ, φ) ↦ P_w(θ, φ)` sends `(a, b)` to `a (i w₂ e^{iθ}) + b (−i w₁ e^{−iφ})`. -/
theorem hasFDerivAt_lozengeCharFun (w₁ w₂ w₃ : ℝ) (x : ℝ × ℝ) :
    ∃ L : ℝ × ℝ →L[ℝ] ℂ, HasFDerivAt (fun p : ℝ × ℝ => lozengeCharFun w₁ w₂ w₃ p.1 p.2) L x ∧
      ∀ h : ℝ × ℝ, L h = h.1 • (I * w₂ * exp (x.1 * I)) + h.2 • (-(I * w₁ * exp (-(x.2 * I)))) := by
  set A : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I
  set B : ℝ × ℝ →L[ℝ] ℂ := -(ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight I
  have hA : HasFDerivAt (fun p : ℝ × ℝ => (p.1 : ℂ) * I) A x := by
    convert A.hasFDerivAt using 1
    funext p
    simp [A, real_smul]
  have hB : HasFDerivAt (fun p : ℝ × ℝ => -((p.2 : ℂ) * I)) B x := by
    convert B.hasFDerivAt using 1
    funext p
    simp [B, real_smul]
  have h := ((hA.cexp.const_mul (w₂ : ℂ)).const_add (w₃ : ℂ)).add (hB.cexp.const_mul (w₁ : ℂ))
  refine ⟨(w₂ : ℂ) • exp (x.1 * I) • A + (w₁ : ℂ) • exp (-(x.2 * I)) • B, ?_, fun h => ?_⟩
  · convert h using 1
    funext p
    simp only [lozengeCharFun_def, Pi.add_apply]
  · simp [A, B, real_smul]
    ring

/-- At a zero of `P_w`, for liquid weights, the real derivative of `P_w` is injective. -/
theorem IsLiquidWeights.exists_hasFDerivAt_injective (hw : IsLiquidWeights w₁ w₂ w₃)
    {x : ℝ × ℝ} (hx : lozengeCharFun w₁ w₂ w₃ x.1 x.2 = 0) :
    ∃ L : ℝ × ℝ →L[ℝ] ℂ, HasFDerivAt (fun p : ℝ × ℝ => lozengeCharFun w₁ w₂ w₃ p.1 p.2) L x ∧
      Function.Injective L := by
  obtain ⟨L, hL, hLapp⟩ := hasFDerivAt_lozengeCharFun w₁ w₂ w₃ x
  refine ⟨L, hL, (injective_iff_map_eq_zero L).2 fun h hh => ?_⟩
  rw [hLapp] at hh
  have := (LinearIndependent.pair_iff.1 (linearIndependent_deriv_lozengeCharFun hw hx)) h.1 h.2 hh
  exact Prod.ext this.1 this.2

/-- The characteristic function `P_w` is continuous on `ℝ²`. -/
theorem continuous_lozengeCharFun (w₁ w₂ w₃ : ℝ) :
    Continuous fun p : ℝ × ℝ => lozengeCharFun w₁ w₂ w₃ p.1 p.2 := by
  simp only [lozengeCharFun_def]
  fun_prop

/-- **`1 / P_w` is locally integrable** on `ℝ²` for liquid weights. -/
theorem IsLiquidWeights.locallyIntegrable_inv_lozengeCharFun (hw : IsLiquidWeights w₁ w₂ w₃) :
    LocallyIntegrable fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹ :=
  haveI : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  locallyIntegrable_inv_of_hasFDerivAt (by simp) (continuous_lozengeCharFun w₁ w₂ w₃)
    fun _ hx => hw.exists_hasFDerivAt_injective hx

/-- **`1 / P_w` is integrable on the torus** `(0, 2π]²` for liquid weights. -/
theorem IsLiquidWeights.integrableOn_inv_lozengeCharFun (hw : IsLiquidWeights w₁ w₂ w₃) :
    IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)) := by
  refine (hw.locallyIntegrable_inv_lozengeCharFun.integrableOn_isCompact
    ((isCompact_Icc (a := 0) (b := 2 * Real.pi)).prod
      (isCompact_Icc (a := 0) (b := 2 * Real.pi)))).mono_set ?_
  exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self

/-- **The kernel integrand is integrable.** For liquid weights and `d ∈ ℤ²`, the integrand
`e^{i(d₁θ + d₂φ)} / P_w(θ, φ)` of `G_w(d)` is integrable on the torus `(0, 2π]²`. -/
theorem IsLiquidWeights.integrableOn_lozengeKernel_integrand (hw : IsLiquidWeights w₁ w₂ w₃)
    (d : ℤ × ℤ) :
    IntegrableOn (fun p : ℝ × ℝ =>
        exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)) := by
  simp_rw [div_eq_mul_inv]
  refine hw.integrableOn_inv_lozengeCharFun.bdd_mul (c := 1) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun p => by
    rw [norm_exp_ofReal_mul_I]

end TauCeti
