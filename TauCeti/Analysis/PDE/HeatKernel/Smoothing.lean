/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.Analysis.PDE.HeatKernel.HeatEquation

/-!
# Ultracontractivity of the heat semigroup

Convolution with the heat kernel sends `Lᵖ` data to bounded functions at every positive time.
In dimension `n`, the estimate is

`‖K_t ⋆ f‖_∞ ≤ (4πt)^(-n/(2p)) ‖f‖_p`.

The pointwise convolution estimate includes both endpoints `p = 1` and `p = ∞`, and allows
Banach-space-valued data. For `p < ∞` it also bounds the essentially bounded representative of
the existing `Lᵖ` heat semigroup. These estimates quantify instantaneous improvement of
integrability, unlike the `Lᵖ` contraction estimate. Splitting the evolution into two positive
time steps then gives a smooth representative for every `Lᵖ` datum with `p < ∞`.

The kernel estimate uses its mass one and its pointwise bound by `(4πt)^(-n/2)`; it does not
assert the optimal constant for intermediate exponents.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1.
* E. B. Davies, *Heat Kernels and Spectral Theory*, Chapter 2 (ultracontractivity).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real
open scoped Convolution ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Pointwise heat smoothing.** For `1 ≤ p ≤ ∞`,
`‖(K_t ⋆ f)(x)‖ ≤ (4πt)^(-n/(2p)) ‖f‖_p`, including `p = 1, ∞`.
The `Lᵖ` norm is written as an extended norm so the estimate also applies to measurable data
without an integrability assumption. -/
theorem enorm_heatKernel_convolution_le {t : ℝ} (ht : 0 < t) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f : E → F} (hf : AEStronglyMeasurable f volume) (x : E) :
    ‖(heatKernel t ⋆ f) x‖ₑ ≤
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / (2 * p.toReal))) *
        eLpNorm f p volume := by
  let q := ENNReal.conjExponent p
  have : q.HolderConjugate p := (ENNReal.HolderConjugate.conjExponent hp).symm
  have h := enorm_convolution_le (p := q) (q := p) (.lsmul ℝ ℝ)
    ((contDiff_heatKernel (k := ⊤) t).continuous.aestronglyMeasurable) hf x
  have hi : 1 / q.toReal + 1 / p.toReal = 1 := by
    have hi := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one q p)
    rw [ENNReal.toReal_add
      (ENNReal.inv_ne_top.mpr (ENNReal.HolderConjugate.pos q p).ne')
      (ENNReal.inv_ne_top.mpr (ENNReal.HolderConjugate.pos p q).ne')] at hi
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_one, one_div] using hi
  have he : -(Module.finrank ℝ E : ℝ) / 2 * (1 - 1 / q.toReal) =
      -(Module.finrank ℝ E : ℝ) / (2 * p.toReal) := by
    rw [show 1 - 1 / q.toReal = 1 / p.toReal by linarith]
    ring
  calc ‖(heatKernel t ⋆ f) x‖ₑ ≤
      eLpNorm (heatKernel t : E → ℝ) q volume * eLpNorm f p volume := by
        grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul] at h
        exact h
    _ ≤ ENNReal.ofReal ((4 * π * t) ^
        (-(Module.finrank ℝ E : ℝ) / (2 * p.toReal))) * eLpNorm f p volume := by
          rw [← he]
          gcongr
          exact eLpNorm_heatKernel_le ht (ENNReal.HolderConjugate.one_le q p)

/-- **Ultracontractivity of the heat semigroup.** At every positive time its `Lᵖ` output
is essentially bounded, with `‖e^{tΔ} f‖_∞ ≤ (4πt)^(-n/(2p)) ‖f‖_p`. -/
theorem eLpNorm_heatSemigroup_top_le [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    eLpNorm (heatSemigroup hp t f) ∞ volume ≤
      ENNReal.ofReal ((4 * π * (t : ℝ)) ^
        (-(Module.finrank ℝ E : ℝ) / (2 * p.toReal))) * eLpNorm f p volume := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [heatSemigroup_ae_eq_convolution_coeFn hp ht f] with x hx
  rw [hx]
  exact enorm_heatKernel_convolution_le (by positivity) Fact.out (Lp.aestronglyMeasurable f) x

/-- **Instantaneous smoothness for `Lᵖ` data.** At every positive time the heat semigroup
has a smooth representative. No boundedness of the initial datum is required. -/
theorem exists_contDiff_ae_eq_heatSemigroup [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    ∃ u : E → F, ContDiff ℝ (⊤ : ℕ∞) u ∧
      (heatSemigroup hp t f : E → F) =ᵐ[volume] u := by
  let s : ℝ≥0 := t / 2
  have hs : s ≠ 0 := by positivity
  have hsum : s + s = t := add_halves t
  let g := heatSemigroup hp s f
  -- The first half-step makes the datum essentially bounded.
  have hg : MemLp (g : E → F) ∞ volume :=
    (eLpNorm_heatSemigroup_top_le hp hs f).trans_lt (by finiteness)
  have hbound : ∀ᵐ x ∂volume, ‖g x‖ ≤ (eLpNorm (g : E → F) ∞ volume).toReal := by
    have h := enorm_ae_le_eLpNormEssSup (g : E → F) volume
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable g)] at h
    filter_upwards [h] with x hx
    simpa only [toReal_enorm] using ENNReal.toReal_mono hg.ne hx
  -- The second half-step smooths bounded data; the semigroup law identifies the result.
  refine ⟨heatKernel (s : ℝ) ⋆ (g : E → F),
    contDiff_heatKernel_convolution (t := (s : ℝ)) (by positivity)
      (Lp.aestronglyMeasurable g) hbound, ?_⟩
  have he : heatSemigroup hp t f = heatSemigroup hp s g := by
    simpa only [hsum, Semigroups.ContractionSemigroup.toStronglyContinuousSemigroup_apply]
      using (heatSemigroup hp).toStronglyContinuousSemigroup.map_add_apply s s f
  rw [he]
  exact heatSemigroup_ae_eq_convolution_coeFn hp hs g

end TauCeti
