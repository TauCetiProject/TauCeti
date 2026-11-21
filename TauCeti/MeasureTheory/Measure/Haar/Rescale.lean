/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Almost-everywhere equalities under rescaling

For an additive Haar measure `μ` on a finite-dimensional real normed space, a rescaling
`x ↦ c • x` with `c ≠ 0` is quasi-measure-preserving (Mathlib's
`MeasureTheory.Measure.quasiMeasurePreserving_smul`), so it transports `μ`-almost everywhere
equalities. With the factor `c` in front, `x ↦ c • f (c • x)` (the rescaling of a density) depends
on `f` only up to `μ`-null sets for every `c`, the zero scale included, where both sides vanish.

## Main results

* `TauCeti.smul_comp_smul_ae_eq`: if `f =ᵐ[μ] g`, then
  `(fun x ↦ c • f (c • x)) =ᵐ[μ] fun x ↦ c • g (c • x)` for every real `c`.
* `TauCeti.inv_mul_comp_div_ae_eq`: the real-line form for the rescaling `t ↦ h⁻¹ f(t / h)` of a
  density by a bandwidth `h`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [AddCommMonoid F] [Module ℝ F]

/-- If `f` and `g` agree almost everywhere for an additive Haar measure `μ`, then so do their
rescalings `x ↦ c • f (c • x)` and `x ↦ c • g (c • x)`, for every real `c`. For `c = 0` both
rescalings are zero. -/
theorem smul_comp_smul_ae_eq (μ : Measure E) [μ.IsAddHaarMeasure] {f g : E → F}
    (hfg : f =ᵐ[μ] g) (c : ℝ) : (fun x ↦ c • f (c • x)) =ᵐ[μ] fun x ↦ c • g (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  filter_upwards [(Measure.quasiMeasurePreserving_smul μ hc).ae_eq_comp hfg] with x hx
  rw [Function.comp_apply, Function.comp_apply] at hx
  rw [hx]

/-- If two real functions agree Lebesgue-almost everywhere, so do their rescalings
`t ↦ h⁻¹ f(t / h)`, for every real `h`. For `h = 0` both rescalings are zero. -/
theorem inv_mul_comp_div_ae_eq {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (h : ℝ) :
    (fun t ↦ h⁻¹ * f (t / h)) =ᵐ[volume] fun t ↦ h⁻¹ * g (t / h) := by
  filter_upwards [smul_comp_smul_ae_eq volume hfg h⁻¹] with t ht
  simpa only [smul_eq_mul, div_eq_inv_mul] using ht

end TauCeti
