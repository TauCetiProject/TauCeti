/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.LineDeriv
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moment
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The space `H^{1,2}(ℝ)`: Gaussians and indicators of intervals

Two computations on the real line test the identification of Mathlib's Bessel-potential space
`H^{1,2}(ℝ)` with the weak-derivative space `W^{1,2}(ℝ)`.

**The factor `2π`.** Mathlib's Bessel potential is the multiplier `(1 + ξ²)^{s/2}`, while the
derivative has the symbol `2πi ξ`, so by the Plancherel identity
(`BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`, here in its
Schwartz form `SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖u'‖²_{L²}`.

For the Gaussian `g(x) = exp(-b x²)`, `0 < Re b`, the squared `L²` norms of `g` and `g'` are
`√(π / (2 Re b))` and `√(π / (2 Re b)) |b|² / Re b` (`TauCeti.norm_toLp_gaussian_sq`,
`TauCeti.norm_toLp_lineDerivOp_one_gaussian_sq`), so `‖g‖²_{H^{1,2}}` is
`√(π / (2 Re b)) (1 + |b|² / (4π² Re b))`
(`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`), whereas the sum of the squared `L²`
norms of `g` and `g'` is `√(π / (2 Re b)) (1 + |b|² / Re b)`
(`TauCeti.norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq`). The two norms are
equivalent, with constants `1` and `(2π)²` on the derivative term, but not equal.

**A jump is not in `H^s`, `s > 1/2`.** For `a < b`, the indicator `1_{[a,b]}` lies in every
`Lᵖ(ℝ)` but not in `H^s(ℝ)` for any `s > 1/2`
(`TauCeti.not_memSobolev_of_ae_eq_indicator_Icc`). By the Sobolev embedding
(`TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`) an element of `H^s(ℝ)`,
`2s > 1`, agrees almost everywhere with a continuous function, which would have to be `1` on
`[a, b]` and `0` on `[b, b + 1]`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, Section 1.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Set
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Real

namespace TauCeti

/-- **The `L²` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{L²} = ∫ |exp(-b x²)|² dx = √(π / (2 Re b))`. -/
theorem norm_toLp_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 = √(π / (2 * b.re)) := by
  have h (x : ℝ) : ‖SchwartzMap.gaussian (V := ℝ) hb x‖ ^ 2 = Real.exp (-(2 * b.re) * x ^ 2) := by
    rw [SchwartzMap.norm_gaussian, Real.norm_eq_abs, sq_abs, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  simp only [SchwartzMap.norm_toLp_sq, h, integral_gaussian]

/-- **The `L²` norm of the derivative of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`,
`0 < Re b`, `‖g'‖²_{L²} = ∫ |∂ₓ exp(-b x²)|² dx = √(π / (2 Re b)) |b|² / Re b`. -/
theorem norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (‖b‖ ^ 2 / b.re) := by
  rw [SchwartzMap.norm_toLp_sq]
  have h (x : ℝ) : ‖∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ)) x‖ ^ 2 =
      4 * ‖b‖ ^ 2 * (x ^ 2 * Real.exp (-(2 * b.re) * x ^ 2)) := by
    rw [SchwartzMap.lineDerivOp_gaussian_apply, norm_mul, norm_mul, norm_mul,
      SchwartzMap.norm_gaussian, Real.norm_eq_abs, sq_abs, Complex.norm_real, Real.norm_eq_abs]
    simp only [mul_pow, sq_abs, RCLike.inner_apply, conj_trivial, sq (Real.exp _),
      ← Real.exp_add]
    norm_num
    ring_nf
  have h2b : 0 < 2 * b.re := by positivity
  simp only [h, integral_const_mul, integral_sq_mul_exp_neg_mul_sq h2b,
    Real.sqrt_div' π h2b.le]
  have : 0 < √(2 * b.re) := Real.sqrt_pos.mpr h2b
  field_simp
  ring

/-- **The `H^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{H^{1,2}} = ‖g‖²_{L²} + (2π)⁻² ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / (4π² Re b))`.
Mathlib's Bessel potential has the symbol `(1 + ξ²)^{1/2}`, not `(1 + 4π² ξ²)^{1/2}`. -/
theorem norm_toBesselPotentialSpaceCLM_one_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (1 : ℝ) 2 (SchwartzMap.gaussian (V := ℝ) hb)‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / (4 * π ^ 2 * b.re)) := by
  simp only [SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq
      (OrthonormalBasis.singleton (Fin 1) ℝ), OrthonormalBasis.singleton_apply,
    Finset.univ_unique, Finset.sum_singleton, ← SchwartzMap.norm_toLp_sq, norm_toLp_gaussian_sq,
    norm_toLp_lineDerivOp_one_gaussian_sq]
  have : 0 < b.re := hb
  field_simp
  ring

/-- **The `W^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{L²} + ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / Re b)`. Compared with
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`, the derivative term carries the factor
`(2π)²`. -/
theorem norm_toLp_gaussian_sq_add_norm_toLp_lineDerivOp_one_gaussian_sq {b : ℂ}
    (hb : 0 < b.re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb : 𝓢(ℝ, ℂ))).toLp 2‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / b.re) := by
  rw [norm_toLp_gaussian_sq, norm_toLp_lineDerivOp_one_gaussian_sq]
  ring

/-- **The indicator of an interval is not in `H^s(ℝ)` for `s > 1/2`.** For `a < b`, an `Lᵖ`
function equal almost everywhere to `1_{[a,b]}` does not lie in Mathlib's Bessel-potential space
of order `s > 1/2`: by the Sobolev embedding it would agree almost everywhere with a continuous
function, which cannot jump at `b`. -/
theorem not_memSobolev_of_ae_eq_indicator_Icc {q : ℝ≥0∞} [Fact (1 ≤ q)] {s a b : ℝ}
    (hs : 1 / 2 < s) (hab : a < b) {u : Lp ℂ q (volume : Measure ℝ)}
    (hu : u =ᵐ[volume] (Icc a b).indicator 1) : ¬ MemSobolev s 2 (u : 𝓢'(ℝ, ℂ)) := by
  intro h
  -- The `L²` class of `1_{[a,b]}` has the same tempered distribution as `u`.
  have hmem : MemLp ((Icc a b).indicator (1 : ℝ → ℂ)) 2 volume :=
    memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet (1 : ℂ)
      (Or.inr (measure_Icc_lt_top (a := a) (b := b)).ne)
  have hv : (hmem.toLp : 𝓢'(ℝ, ℂ)) = (u : 𝓢'(ℝ, ℂ)) := by
    ext φ
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae ((hmem.coeFn_toLp.trans hu.symm).mono fun x hx ↦ by simp only [hx])
  obtain ⟨g, hg⟩ := (hv ▸ h).exists_zeroAtInftyContinuousMap_ae_eq
    (by rw [Module.finrank_self]; push_cast; linarith)
  have hind : (Icc a b).indicator (1 : ℝ → ℂ) =ᵐ[volume] g := hmem.coeFn_toLp.symm.trans hg
  -- `g = 1` on `[a, b]`.
  have h₁ : g b = 1 := by
    have hae : (fun _ ↦ (1 : ℂ)) =ᵐ[volume.restrict (Icc a b)] g := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hind] with x hx hx'
      rw [← hx', indicator_of_mem hx, Pi.one_apply]
    exact (Measure.eqOn_Icc_of_ae_eq volume hab.ne hae continuousOn_const
      g.continuous.continuousOn (right_mem_Icc.2 hab.le)).symm
  -- `g = 0` on `[b, b + 1]`.
  have h₀ : g b = 0 := by
    have hae : (fun _ ↦ (0 : ℂ)) =ᵐ[volume.restrict (Icc b (b + 1))] g := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hind] with x hx hx'
      rw [← hx', indicator_of_notMem fun hx'' : x ∈ Icc a b ↦ (hx''.2.trans_lt hx.1).false]
    exact (Measure.eqOn_Icc_of_ae_eq volume (by linarith : b ≠ b + 1).symm.symm hae
      continuousOn_const g.continuous.continuousOn (left_mem_Icc.2 (by linarith))).symm
  exact one_ne_zero (h₁.symm.trans h₀)

end TauCeti
