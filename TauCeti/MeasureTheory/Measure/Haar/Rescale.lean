/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Rescaling and additive Haar measures

For an additive Haar measure `μ` on a finite-dimensional real normed space, a rescaling
`x ↦ c • x` with `c ≠ 0` is quasi-measure-preserving (Mathlib's
`MeasureTheory.Measure.quasiMeasurePreserving_smul`), so it transports `μ`-almost everywhere
equalities. With the factor `c` in front, `x ↦ c • f (c • x)` depends on `f` only up to `μ`-null
sets for every `c`, the zero scale included, where both sides vanish. On the real line, with
`c = h⁻¹`, this is the bandwidth rescaling `t ↦ h⁻¹ f(t / h)` of a density `f`; in dimension
`d > 1` the rescaling of a density by `c` carries the factor `|c| ^ d` instead, which this file
does not treat.

Conversely, rescaling normalizes Haar measures: on a nontrivial space, a dilation by
`t = c ^ (1 / d)`, where `μ = c • ν` and `d` is the dimension, carries `μ` to `ν`. This reduces a
statement about an arbitrary additive Haar measure to the same statement for `volume`, at the
price of dilating the domain.

## Main results

* `MeasureTheory.Measure.smul_comp_smul_ae_eq`: if `f =ᵐ[μ] g`, then
  `(fun x ↦ c • f (c • x)) =ᵐ[μ] fun x ↦ c • g (c • x)` for every real `c`.
* `MeasureTheory.Measure.exists_pos_map_smul_eq`: two additive Haar measures on a nontrivial space
  differ by a positive dilation.
* `Filter.EventuallyEq.inv_mul_comp_div`: the real-line form for the rescaling
  `t ↦ h⁻¹ f(t / h)` of a density by a bandwidth `h`.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Zero F] [SMulWithZero ℝ F]

/-- If `f` and `g` agree almost everywhere for an additive Haar measure `μ`, then so do their
rescalings `x ↦ c • f (c • x)` and `x ↦ c • g (c • x)`, for every real `c`. For `c = 0` both
rescalings are zero. -/
theorem smul_comp_smul_ae_eq (μ : Measure E) [μ.IsAddHaarMeasure] {f g : E → F}
    (hfg : f =ᵐ[μ] g) (c : ℝ) : (fun x ↦ c • f (c • x)) =ᵐ[μ] fun x ↦ c • g (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  filter_upwards [(quasiMeasurePreserving_smul μ hc).ae_eq_comp hfg] with x hx
  rw [Function.comp_apply, Function.comp_apply] at hx
  rw [hx]

/-- **Haar measures differ by a dilation.** On a nontrivial finite-dimensional real normed space,
every additive Haar measure `μ` is carried to any other additive Haar measure `ν` by a dilation
`x ↦ t • x` with `t > 0`. -/
theorem exists_pos_map_smul_eq [Nontrivial E] (μ ν : Measure E) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] : ∃ t : ℝ, 0 < t ∧ Measure.map (t • ·) μ = ν := by
  obtain ⟨c, hc, hμ⟩ : ∃ c : NNReal, 0 < c ∧ μ = c • ν :=
    ⟨_, addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν, isAddLeftInvariant_eq_smul μ ν⟩
  -- The dilation by `t = c ^ (1 / d)` scales volumes by `t ^ d = c`.
  have htd : ((c : ℝ) ^ (Module.finrank ℝ E : ℝ)⁻¹) ^ Module.finrank ℝ E = c :=
    Real.rpow_inv_natCast_pow c.coe_nonneg Module.finrank_pos.ne'
  refine ⟨(c : ℝ) ^ (Module.finrank ℝ E : ℝ)⁻¹, by positivity, ?_⟩
  rw [hμ, Measure.map_smul, map_addHaar_smul ν (by positivity), htd, ← smul_assoc,
    abs_of_pos (by positivity)]
  · simp [ENNReal.smul_def, ENNReal.ofReal_inv_of_pos, hc, ENNReal.mul_inv_cancel, hc.ne']
  · exact (measurable_const_smul _).aemeasurable

end MeasureTheory.Measure

namespace Filter.EventuallyEq

/-- If two real functions agree Lebesgue-almost everywhere, so do their rescalings
`t ↦ h⁻¹ f(t / h)`, for every real `h`. For `h = 0` both rescalings are zero. -/
theorem inv_mul_comp_div {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (h : ℝ) :
    (fun t ↦ h⁻¹ * f (t / h)) =ᵐ[volume] fun t ↦ h⁻¹ * g (t / h) := by
  filter_upwards [volume.smul_comp_smul_ae_eq hfg h⁻¹] with t ht
  simpa only [smul_eq_mul, div_eq_inv_mul] using ht

end Filter.EventuallyEq
