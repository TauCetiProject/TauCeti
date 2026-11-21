/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
public import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
import TauCeti.Analysis.Sobolev.TestFunctionLp.Representation
import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Mean-zero functions on a ball are divergences

Let `B = B(x₀, t)` be a ball in a finite-dimensional real inner product space `E` of dimension
`n ≥ 1`, with an additive Haar measure `μ`, and let `1 < r ≤ p < ∞` with `δ = 1/r - 1/p < 1/n`.
This file proves that every `h ∈ Lʳ` vanishing off `B` with `∫ h = 0` is the divergence of a field
in `Lᵖ`: there is `H ∈ Lᵖ(E; E)` with

`∫ h φ = ∫ ⟪H, ∇φ⟫` for every test function `φ`, and `‖H‖_{Lᵖ} ≤ C t μ(B)^(-δ) ‖h‖_{Lʳ}`,

with `C` depending only on `n`, `r` and `p`
(`TauCeti.exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero`).
So `-div H = h` in the sense of distributions, and `H` gains integrability over `h` when `p > r`.
This is how a scalar right-hand side `h` of a divergence-form equation `-div(a ∇u) = -div G + h`
is absorbed into the divergence datum, as in the localization of `W^{1,p}` estimates: a cutoff of a
local solution solves such an equation with a scalar term of mean zero.

The proof is by duality. Since `h` has mean zero on `B`, `∫ h φ = ∫_B h (φ - φ_B)`, and Hölder's
inequality with the Sobolev–Poincaré inequality on the ball
(`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_ball_subset`, in norms rather than averages) bound
it by `C t μ(B)^(-δ) ‖h‖_{Lʳ} ‖∇φ‖_{L^q}`, `q` the exponent conjugate to `p`. A functional on test
functions bounded by the `L^q` norm of the gradient extends by Hahn–Banach, through the partial
derivatives along an orthonormal basis, to `(L^q)ⁿ`, and the integral representation of the dual of
`L^q` (`MeasureTheory.Lp.dualEquiv`) represents it by a field `H ∈ Lᵖ`
(`TauCeti.exists_memLp_forall_eq_integral_inner_gradient_of_abs_le`). Some condition on the mean of
`h` is needed: a function with nonzero integral, such as the indicator of `B`, is not the divergence
of a field in `Lᵖ` once `p ≤ n / (n - 1)`, since such fields have vanishing flux at infinity.

## Main declarations

* `TauCeti.exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero`:
  mean-zero functions on a ball are divergences of `Lᵖ` fields, with the scale-invariant bound.

## References

* G. P. Galdi, *An Introduction to the Mathematical Theory of the Navier–Stokes Equations*, 2nd ed.,
  Springer, 2011, Section III.3 (the equation `div H = h` for `h` of mean zero).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.16 (the Sobolev–Poincaré inequality).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Gradient InnerProductSpace

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

/-- The Sobolev–Poincaré inequality on a ball for test functions, in norms. -/
private theorem eLpNorm_sub_setAverage_le_of_testFunction {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {s : ℝ≥0} (hqs : q ≤ s) {δ : ℝ} (hδ : q.toReal⁻¹ - (s : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {x₀ : E} {t : ℝ} (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    eLpNorm (fun x => (φ : E → ℝ) x - ⨍ y in ball x₀ t, (φ : E → ℝ) y ∂μ) s
        (μ.restrict (ball x₀ t)) ≤
      ENNReal.ofReal (sobolevPoincareConst (finrank ℝ E) δ * t) *
        μ (ball x₀ t) ^ (-δ) * eLpNorm (∇ (φ : E → ℝ)) q (μ.restrict (ball x₀ t)) := by
  set v := W1p.ofTestFunctionₗ μ ⊤ q φ
  have hv : W1p.value v =ᵐ[μ] (φ : E → ℝ) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.value_ofTestFunctionₗ_ae (p := q) φ
  have hg : W1p.gradient v =ᵐ[μ] ∇ (φ : E → ℝ) := by
    have h := gradientTestFunctionLp_apply_ae (mu := μ) q φ
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  exact W1p.eLpNorm_sub_setAverage_le_of_ae_eq hq le_rfl hqs hδ hδn ht (by simp) v
    (ae_restrict_of_ae hv.symm) (ae_restrict_of_ae hg.symm)

/-- The pairing of a mean-zero `h ∈ Lʳ` supported in a ball `B = B(x₀, t)` with a test function
`φ` is bounded by `K t μ(B)^(-δ) ‖h‖_{Lʳ} ‖∇φ‖_{L^q}`, `q` the exponent conjugate to `p`. This is
the Sobolev–Poincaré inequality for `φ` on `B` read through Hölder's inequality. -/
private theorem abs_integral_mul_le_of_integral_eq_zero {p r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hr : 1 < r) (hrp : r ≤ p) (hp : p ≠ ⊤) {δ : ℝ} (hδ : r.toReal⁻¹ - p.toReal⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {x₀ : E} {t : ℝ} (ht : 0 < t) {h : E → ℝ}
    (hh : MemLp h r μ) (hsupp : ∀ᵐ x ∂μ, x ∉ ball x₀ t → h x = 0) (hmean : ∫ x, h x ∂μ = 0)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    |∫ x, h x * (φ : E → ℝ) x ∂μ| ≤
      (ENNReal.ofReal (sobolevPoincareConst (finrank ℝ E) δ * t) *
        μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ).toReal *
      (eLpNorm (∇ (φ : E → ℝ)) p.conjExponent μ).toReal := by
  set q := p.conjExponent
  set s := r.conjExponent
  set K : ℝ := sobolevPoincareConst (finrank ℝ E) δ
  set B := ball x₀ t
  have hq_top : q ≠ ⊤ := ENNReal.conjExponent_ne_top (hr.trans_le hrp)
  have hs_top : s ≠ ⊤ := ENNReal.conjExponent_ne_top hr
  have hB0 : μ B ≠ 0 := (measure_ball_pos μ x₀ ht).ne'
  have hBt : μ B ≠ ⊤ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hBt
  have hr1 : (1 : ℝ≥0∞) ≤ r := Fact.out
  have hsN : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) = s := ENNReal.coe_toNNReal hs_top
  have hδ' : q.toReal⁻¹ - ((s.toNNReal : ℝ≥0) : ℝ)⁻¹ = δ := by
    rw [← hδ, ENNReal.coe_toNNReal_eq_toReal, ENNReal.inv_toReal_conjExponent (hr.trans_le hrp) hp,
      ENNReal.inv_toReal_conjExponent hr (ne_top_of_le_ne_top hp hrp)]
    ring
  have hs : s.HolderConjugate r := inferInstance
  have : Fact (1 ≤ q) := ⟨(ENNReal.one_lt_conjExponent hp).le⟩
  set c := ⨍ y in B, (φ : E → ℝ) y ∂μ
  -- Sobolev–Poincaré for `φ` on `B`.
  have hSP := eLpNorm_sub_setAverage_le_of_testFunction (μ := μ) hq_top
    (by rw [hsN]; exact ENNReal.conjExponent_le_conjExponent hrp) hδ' hδn (x₀ := x₀) ht φ
  rw [hsN] at hSP
  have hgrad : eLpNorm (∇ (φ : E → ℝ)) q μ ≠ ⊤ :=
    (φ.hasCompactSupport.memLp_gradient (φ.contDiff.of_le (by simp))).eLpNorm_ne_top
  have hφs : MemLp (fun x => (φ : E → ℝ) x - c) s (μ.restrict B) :=
    hSP.trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) ?_
      · exact (ENNReal.rpow_ne_top_of_ne_zero hB0 hBt).lt_top
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt hgrad.lt_top)
  have hhB : MemLp h r (μ.restrict B) := hh.restrict B
  have hint1 : Integrable (fun x => ((φ : E → ℝ) x - c) * h x) (μ.restrict B) :=
    hφs.integrable_mul hhB
  have heq := integral_mul_eq_setIntegral_sub_smul (hhB.integrable hr1) hsupp hmean c hint1
  have hHolder := enorm_integral_smul_le (μ := μ.restrict B) (p := s) (q := r)
    (a := fun x => (φ : E → ℝ) x - c) (f := h)
  have hfin : ENNReal.ofReal (K * t) * μ B ^ (-δ) * eLpNorm h r μ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hh.eLpNorm_ne_top
    exact ENNReal.rpow_ne_top_of_ne_zero hB0 hBt
  rw [heq, ← Real.norm_eq_abs, ← toReal_eNorm, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hgrad) (hHolder.trans ?_)
  calc eLpNorm (fun x => (φ : E → ℝ) x - c) s (μ.restrict B) * eLpNorm h r (μ.restrict B)
      ≤ ENNReal.ofReal (K * t) * μ B ^ (-δ) *
          eLpNorm (∇ (φ : E → ℝ)) q (μ.restrict B) * eLpNorm h r μ :=
        mul_le_mul' hSP (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ ≤ ENNReal.ofReal (K * t) * μ B ^ (-δ) * eLpNorm (∇ (φ : E → ℝ)) q μ * eLpNorm h r μ := by
        gcongr
        exact Measure.restrict_le_self
    _ = _ := by ring

/-- **Mean-zero functions on a ball are divergences.** Let `n ≥ 1` be the dimension, let
`1 < r ≤ p < ∞` with `δ = 1/r - 1/p < 1/n`. There is a constant `C`, depending only on `n`, `r`
and `p`, such that every `h ∈ Lʳ(ℝⁿ)` vanishing off a ball `B = B(x₀, t)` with `∫ h = 0` is the
divergence of a field `H ∈ Lᵖ(ℝⁿ; ℝⁿ)`, in the sense that

`∫ h φ = ∫ ⟪H, ∇φ⟫` for every test function `φ`, with `‖H‖_{Lᵖ} ≤ C t μ(B)^(-δ) ‖h‖_{Lʳ}`.

So `-div H = h` in the sense of distributions. The factor `t μ(B)^(-δ)` is the scaling of the
estimate: it is `t` when `p = r`, and for `p > r` the field gains integrability. Some condition on
the mean is needed: a nonzero constant times the indicator of `B` is no divergence of an `Lᵖ`
field once `p ≤ n / (n - 1)`. -/
theorem exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hr : 1 < r) (hrp : r ≤ p) (hp : p ≠ ⊤) {δ : ℝ}
    (hδ : r.toReal⁻¹ - p.toReal⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {x₀ : E} {t : ℝ}, 0 < t → ∀ {h : E → ℝ}, MemLp h r μ →
      (∀ᵐ x ∂μ, x ∉ ball x₀ t → h x = 0) → ∫ x, h x ∂μ = 0 →
      ∃ H : E → E, MemLp H p μ ∧
        eLpNorm H p μ ≤ C * ENNReal.ofReal t * μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ ∧
        ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, h x * φ x ∂μ = ∫ x, ⟪H x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ := by
  have hq1 : 1 < p.conjExponent := ENNReal.one_lt_conjExponent hp
  have hq_top := ENNReal.conjExponent_ne_top (hr.trans_le hrp)
  set q := p.conjExponent
  set K : ℝ := sobolevPoincareConst (finrank ℝ E) δ
  refine ⟨(finrank ℝ E : ℝ≥0) ^ 2 * K.toNNReal, fun {x₀ t} ht {h} hh hsupp hmean => ?_⟩
  have hK : 0 ≤ K := sobolevPoincareConst_nonneg hδn
  have hfin : ENNReal.ofReal (K * t) * μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_ne_zero
      (measure_ball_pos μ x₀ ht).ne' measure_ball_lt_top.ne)) hh.eLpNorm_ne_top
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  -- The pairing with `h` is bounded by the `L^q` norm of the gradient.
  set M : ℝ := (ENNReal.ofReal (K * t) * μ (ball x₀ t) ^ (-δ) * eLpNorm h r μ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hloc : LocallyIntegrableOn h (⊤ : Opens E) μ :=
    (hh.locallyIntegrable Fact.out).locallyIntegrableOn _
  let ℓ : 𝓓((⊤ : Opens E), ℝ) →ₗ[ℝ] ℝ :=
    (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ) μ h).toLinearMap
  have hℓ (φ : 𝓓((⊤ : Opens E), ℝ)) : ℓ φ = ∫ x, h x * (φ : E → ℝ) x ∂μ := by
    simp only [ℓ, ContinuousLinearMap.coe_coe,
      TestFunction.integralAgainstBilinCLM_eq_integral hloc, ContinuousLinearMap.mul_apply',
      mul_comm]
  have hbound (φ : 𝓓((⊤ : Opens E), ℝ)) :
      |ℓ φ| ≤ M * (eLpNorm (∇ (φ : E → ℝ)) q μ).toReal := by
    rw [hℓ]
    exact abs_integral_mul_le_of_integral_eq_zero hr hrp hp hδ hδn ht hh hsupp hmean φ
  obtain ⟨H, hH, hHnorm, hHφ⟩ := exists_memLp_forall_eq_integral_inner_gradient_of_abs_le
    (μ := μ) (p := p) hq1 hq_top ℓ hM hbound
  simp only [Opens.coe_top, Measure.restrict_univ] at hH hHnorm hHφ
  refine ⟨H, hH, hHnorm.trans (le_of_eq ?_), fun φ => (hℓ φ).symm.trans (hHφ φ)⟩
  rw [ENNReal.ofReal_toReal hfin, ENNReal.ofReal_mul hK, ENNReal.coe_mul,
    ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.ofNNReal_toNNReal]
  ring

end Ball

end TauCeti
