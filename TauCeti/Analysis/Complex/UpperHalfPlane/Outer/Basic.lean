/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Fatou.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Function

/-!
# Outer functions on the upper half-plane

For a real function `h` integrable for the Poisson measure `Π = dx / (1 + x ^ 2)`, the **outer
function** with boundary log-modulus `h` is `O_h = exp (S[h])`, where
`S[h](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) h(x) dx` is the Schwarz integral
(`TauCeti.upperHalfPlaneSchwarzIntegralFun`). A holomorphic function on `ℂ₊` is outer when it is
`c O_h` with `|c| = 1`.

## Main results

* `TauCeti.differentiableOn_upperHalfPlaneOuter`, `TauCeti.upperHalfPlaneOuter_ne_zero`: `O_h` is
  holomorphic and zero-free on `ℂ₊`.
* `TauCeti.norm_upperHalfPlaneOuter`: `|O_h| = exp P[h]`.
* `TauCeti.ae_tendsto_nontangentialFilter_norm_upperHalfPlaneOuter`: by Fatou's theorem,
  `|O_h(z)| → e^{h(x)}` as `z → x` nontangentially, for almost every `x`.
* `TauCeti.upperHalfPlaneOuter_add`, `TauCeti.upperHalfPlaneOuter_zero`: `O_{h + k} = O_h O_k`
  and `O_0 = 1`.
* `TauCeti.norm_upperHalfPlaneOuter_le`: if `h ≤ M` almost everywhere then `|O_h| ≤ e^M`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter II, §4.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286
  (2022), Lemma 8.
* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. **200**
  (2024), Section 2.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped Real ENNReal NNReal
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

variable {h k : ℝ → ℝ}

/-! ### Outer functions -/

/-- The **outer function** `O_h = exp (S[h])` on the upper half-plane with boundary log-modulus a
real function `h`, meaningful for `h` integrable for the Poisson measure `dx / (1 + x ^ 2)`. -/
def upperHalfPlaneOuter (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  exp (upperHalfPlaneSchwarzIntegralFun (fun x ↦ (h x : ℂ)) z)

/-- The defining formula of `TauCeti.upperHalfPlaneOuter`. -/
theorem upperHalfPlaneOuter_def (h : ℝ → ℝ) (z : ℂ) :
    upperHalfPlaneOuter h z = exp (upperHalfPlaneSchwarzIntegralFun (fun x ↦ (h x : ℂ)) z) :=
  (rfl)

/-- **Outer functions are zero-free.** -/
@[simp]
theorem upperHalfPlaneOuter_ne_zero (h : ℝ → ℝ) (z : ℂ) : upperHalfPlaneOuter h z ≠ 0 :=
  exp_ne_zero _

/-- **Outer functions are holomorphic** on `ℂ₊`. -/
theorem differentiableOn_upperHalfPlaneOuter (hh : Integrable h upperHalfPlanePoissonMeasure) :
    DifferentiableOn ℂ (upperHalfPlaneOuter h) upperHalfPlaneSet :=
  (differentiableOn_upperHalfPlaneSchwarzIntegralFun hh.ofReal).cexp

/-- **The modulus of an outer function**: `|O_h(z)| = exp P[h](z) = exp ∫ P(z, x) h(x) dx`. -/
theorem norm_upperHalfPlaneOuter (hh : Integrable h upperHalfPlanePoissonMeasure) (z : ℂ) :
    ‖upperHalfPlaneOuter h z‖ = Real.exp (∫ x, upperHalfPlanePoissonKernel z x * h x) := by
  rw [upperHalfPlaneOuter_def, norm_exp, re_upperHalfPlaneSchwarzIntegralFun hh,
    re_upperHalfPlanePoissonIntegralFun (h := fun x ↦ (h x : ℂ)) hh.ofReal]
  simp only [ofReal_re]

/-- **Boundary modulus of an outer function.** For almost every `x ∈ ℝ`, `|O_h(z)| → e^{h(x)}` as
`z → x` nontangentially, through cones of every aperture (Mauth, Lemma 8). -/
theorem ae_tendsto_nontangentialFilter_norm_upperHalfPlaneOuter
    (hh : Integrable h upperHalfPlanePoissonMeasure) :
    ∀ᵐ x, ∀ α : ℝ, Tendsto (fun z ↦ ‖upperHalfPlaneOuter h z‖) (nontangentialFilter α x)
      (𝓝 (Real.exp (h x))) := by
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun
    (h := fun x ↦ (h x : ℂ)) hh.ofReal] with x hx α
  have hre := (Real.continuous_exp.tendsto _).comp ((continuous_re.tendsto _).comp (hx α))
  rw [ofReal_re] at hre
  refine hre.congr fun z ↦ ?_
  simp only [Function.comp_apply, norm_upperHalfPlaneOuter hh,
    re_upperHalfPlanePoissonIntegralFun (h := fun x ↦ (h x : ℂ)) hh.ofReal, ofReal_re]

/-- **Outer functions are multiplicative**: `O_{h + k} = O_h O_k` off the real axis. -/
theorem upperHalfPlaneOuter_add (hh : Integrable h upperHalfPlanePoissonMeasure)
    (hk : Integrable k upperHalfPlanePoissonMeasure) {z : ℂ} (hz : z.im ≠ 0) :
    upperHalfPlaneOuter (h + k) z = upperHalfPlaneOuter h z * upperHalfPlaneOuter k z := by
  simp only [upperHalfPlaneOuter_def, Pi.add_apply, ofReal_add,
    upperHalfPlaneSchwarzIntegralFun_add (h := fun x ↦ (h x : ℂ)) (g := fun x ↦ (k x : ℂ))
      hh.ofReal hk.ofReal hz, exp_add]

/-- The outer function of `0` is `1`. -/
@[simp]
theorem upperHalfPlaneOuter_zero : upperHalfPlaneOuter 0 = 1 := by
  funext z
  simp [upperHalfPlaneOuter_def]

/-- **Bounded outer functions.** If `h ≤ M` almost everywhere, then `|O_h| ≤ e^M` on `ℂ₊`. -/
theorem norm_upperHalfPlaneOuter_le (hh : Integrable h upperHalfPlanePoissonMeasure) {M : ℝ}
    (hM : ∀ᵐ x, h x ≤ M) {z : ℂ} (hz : 0 < z.im) :
    ‖upperHalfPlaneOuter h z‖ ≤ Real.exp M := by
  rw [norm_upperHalfPlaneOuter hh, Real.exp_le_exp]
  have hP := integrable_upperHalfPlanePoissonKernel_smul hh z
  simp only [smul_eq_mul] at hP
  calc ∫ x, upperHalfPlanePoissonKernel z x * h x
      ≤ ∫ x, upperHalfPlanePoissonKernel z x * M := by
        refine integral_mono_ae hP ?_ (hM.mono fun x hx ↦ ?_)
        · exact (isPoissonFinite_volume.integrable_upperHalfPlanePoissonKernel z).mul_const M
        · exact mul_le_mul_of_nonneg_left hx (upperHalfPlanePoissonKernel_nonneg hz.le x)
    _ = M := by rw [integral_mul_const, integral_upperHalfPlanePoissonKernel hz, one_mul]

end TauCeti
