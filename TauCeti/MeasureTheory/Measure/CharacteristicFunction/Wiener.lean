/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.AtomicMass
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Wiener's lemma for characteristic functions

Applying atomic-mass inversion (`MeasureTheory.tendsto_average_exp_mul_charFun` from
`TauCeti.MeasureTheory.Measure.CharacteristicFunction.AtomicMass`) at `ω = 0` to the difference
convolution `μ ∗ ν.map (-·)` yields the bilinear Wiener identity for two finite Borel measures `μ`
and `ν`, and setting `μ = ν` gives Wiener's lemma on the real line:

`T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2 → ∑' ξ : ℝ, σ.real {ξ} ^ 2` as `T → ∞`.

In particular, the mean-square time average of `charFun σ` vanishes if and only if `σ` assigns zero
mass to every singleton.

## Main results

* `MeasureTheory.tendsto_average_charFun_mul_conj`: bilinear Wiener lemma for two finite Borel
  measures on `ℝ`.
* `MeasureTheory.tendsto_average_norm_charFun_sq`: **Wiener's lemma** on `ℝ`.
* `MeasureTheory.tendsto_average_norm_charFun_sq_zero_iff`: vanishing of the mean-square average
  of `charFun σ` if and only if every singleton is `σ`-null.

## References

* N. Wiener, *The Fourier Integral and Certain of Its Applications*, Cambridge University Press
  (1933).
* Y. Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University Press
  (2004), Section I.7.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate Topology

namespace MeasureTheory

/-- **Bilinear Wiener lemma on `ℝ`.** For finite Borel measures `μ` and `ν` on `ℝ`, the time
averages `(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, charFun μ t * conj (charFun ν t)` converge to the
common-atom sum `∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ}` as `T → ∞`. -/
theorem tendsto_average_charFun_mul_conj (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, charFun μ t * conj (charFun ν t))
      atTop (𝓝 ((∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ} : ℝ) : ℂ)) := by
  let νneg : Measure ℝ := ν.map fun x : ℝ ↦ -x
  let τ : Measure ℝ := μ ∗ νneg
  have hchar : ∀ t : ℝ, charFun τ t = charFun μ t * conj (charFun ν t) := fun t ↦ by
    rw [charFun_conv, ← charFun_neg]
    congr 1
    have hneg : (fun x : ℝ ↦ -x) = ((-1 : ℝ) * ·) := by
      funext x
      ring
    have hν : νneg = ν.map ((-1 : ℝ) * ·) := congrArg (ν.map ·) hneg
    rw [hν, charFun_map_mul, neg_one_mul]
  have hτ_eq : τ = (μ.prod ν).map fun p : ℝ × ℝ ↦ p.1 - p.2 := by
    dsimp only [τ, νneg]
    rw [Measure.conv, ← Measure.map_id (μ := μ),
      Measure.map_prod_map _ _ measurable_id measurable_neg,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1 with p
    simp
  have hmass : τ.real {0} = ∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ} := by
    rw [hτ_eq, map_measureReal_apply (by fun_prop) (measurableSet_singleton 0)]
    have hpre : (fun p : ℝ × ℝ ↦ p.1 - p.2) ⁻¹' {0} = Set.diagonal ℝ := by
      ext ⟨x, y⟩
      simp [sub_eq_zero]
    rw [hpre, Measure.prod_real_diagonal]
  simpa [hchar, hmass] using tendsto_average_exp_mul_charFun τ 0

/-- **Wiener's lemma on `ℝ`.** For a finite Borel measure `σ` on `ℝ`, the mean-square time averages
`T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2` converge as `T → ∞` to the sum
`∑' ξ : ℝ, σ.real {ξ} ^ 2` of the squared masses of its atoms. -/
theorem tendsto_average_norm_charFun_sq (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2)
      atTop (𝓝 (∑' ξ : ℝ, σ.real {ξ} ^ 2)) := by
  have h := (Complex.continuous_re.continuousAt.tendsto).comp
    (tendsto_average_charFun_mul_conj σ σ)
  have hterm (t : ℝ) : charFun σ t * conj (charFun σ t) = ((‖charFun σ t‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hfun : (fun T : ℝ ↦
      ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, charFun σ t * conj (charFun σ t)).re) =
      fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2 := by
    funext T
    simp_rw [hterm, intervalIntegral.integral_ofReal]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Function.comp_def, hfun, Complex.ofReal_re] at h
  simpa only [sq] using h

/-- For a finite Borel measure `σ` on `ℝ`, the mean-square time averages of `charFun σ` vanish as
`T → ∞` if and only if `σ` assigns zero mass to every singleton. -/
theorem tendsto_average_norm_charFun_sq_zero_iff (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2) atTop (𝓝 0) ↔
      ∀ ξ : ℝ, σ {ξ} = 0 := by
  constructor
  · intro h0 ξ
    have htsum : ∑' x : ℝ, σ.real {x} ^ 2 = 0 :=
      tendsto_nhds_unique (tendsto_average_norm_charFun_sq σ) h0
    have hsum : Summable fun x : ℝ ↦ σ.real {x} ^ 2 := by
      simpa only [sq] using (Measure.hasSum_prod_real_diagonal σ σ).summable
    have hzero : σ.real {ξ} ^ 2 = 0 :=
      le_antisymm (htsum ▸ hsum.le_tsum ξ fun _ _ ↦ sq_nonneg _) (sq_nonneg _)
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      ((pow_eq_zero_iff (by norm_num)).mp hzero)
  · intro hnull
    have htsum : ∑' ξ : ℝ, σ.real {ξ} ^ 2 = 0 := by
      simp [measureReal_def, hnull]
    simpa only [htsum] using tendsto_average_norm_charFun_sq σ

end MeasureTheory

end
