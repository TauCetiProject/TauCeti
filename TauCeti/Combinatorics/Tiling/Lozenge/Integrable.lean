/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.CharacteristicFunction
public import TauCeti.MeasureTheory.Integral.InvNondegenerateZero
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integrability of `1 / P_w` for liquid weights

For liquid type weights `w`, the characteristic function
`P_w(θ, φ) = w₃ + w₂ e^{iθ} + w₁ e^{−iφ}` vanishes at two points modulo `2π`, and at each of them
its real derivative is injective (`TauCeti.IsLiquidWeights.exists_hasFDerivAt_injective`). Near a
zero, `|P_w|` is therefore bounded below by a multiple of the distance to the zero, and `1 / |x|`
is integrable near `0` in the plane. This file proves:

* `TauCeti.IsLiquidWeights.locallyIntegrable_inv_lozengeCharFun`: `1 / P_w` is locally integrable
  on `ℝ²`, by `TauCeti.locallyIntegrable_inv_of_hasFDerivAt`;
* `TauCeti.IsLiquidWeights.integrableOn_inv_lozengeCharFun`: `1 / P_w` is integrable on the
  torus `(0, 2π]²`;
* `TauCeti.IsLiquidWeights.integrableOn_lozengeKernel_integrand`: so is the integrand
  `e^{i(d₁θ + d₂φ)} / P_w(θ, φ)` of the kernel `G_w(d)`, which is therefore a genuine Lebesgue
  integral; for any weights, the integrand is integrable on the torus whenever `1 / P_w` is
  (`TauCeti.integrableOn_lozengeKernel_integrand_of_integrableOn`).

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

/-- **The kernel integrand is integrable** whenever `1 / P_w` is: for `d ∈ ℤ²`, the integrand
`e^{i(d₁θ + d₂φ)} / P_w(θ, φ)` of `G_w(d)` is then integrable on the torus `(0, 2π]²`. -/
theorem integrableOn_lozengeKernel_integrand_of_integrableOn
    (hP : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun w₁ w₂ w₃ p.1 p.2)⁻¹)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)))
    (d : ℤ × ℤ) :
    IntegrableOn (fun p : ℝ × ℝ =>
        exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)) := by
  simp_rw [div_eq_mul_inv]
  refine hP.bdd_mul (c := 1) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun p => by
    rw [norm_exp_ofReal_mul_I]

/-- **The kernel integrand is integrable.** For liquid weights and `d ∈ ℤ²`, the integrand
`e^{i(d₁θ + d₂φ)} / P_w(θ, φ)` of `G_w(d)` is integrable on the torus `(0, 2π]²`. -/
theorem IsLiquidWeights.integrableOn_lozengeKernel_integrand (hw : IsLiquidWeights w₁ w₂ w₃)
    (d : ℤ × ℤ) :
    IntegrableOn (fun p : ℝ × ℝ =>
        exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) / lozengeCharFun w₁ w₂ w₃ p.1 p.2)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)) :=
  integrableOn_lozengeKernel_integrand_of_integrableOn hw.integrableOn_inv_lozengeCharFun d

end TauCeti
