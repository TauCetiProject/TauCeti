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

/-- The heat kernel is bounded by its value at the origin. -/
theorem heatKernel_le {t : ℝ} (ht : 0 < t) (x : E) :
    heatKernel t x ≤ (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  rw [heatKernel_apply]
  exact mul_le_of_le_one_right (by positivity)
    (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The heat kernel has finite `Lᵠ` norm for every `1 ≤ q ≤ ∞`, with the explicit bound
`‖K_t‖_q ≤ (4πt)^(-(n/2)(1 - 1/q))`. -/
theorem eLpNorm_heatKernel_le {t : ℝ} (ht : 0 < t) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (heatKernel t : E → ℝ) q volume ≤
      ENNReal.ofReal ((4 * π * t) ^
        (-(Module.finrank ℝ E : ℝ) / 2 * (1 - 1 / q.toReal))) := by
  have hm : AEStronglyMeasurable (heatKernel t : E → ℝ) volume :=
    (contDiff_heatKernel (k := ⊤) t).continuous.aestronglyMeasurable
  set c : ℝ := (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  have hc : 0 < c := by positivity
  have hbound : ∀ x : E, ‖heatKernel t x‖ ≤ c := fun x => by
    rw [norm_of_nonneg (heatKernel_pos ht x).le]
    exact heatKernel_le ht x
  by_cases hqt : q = ∞
  · subst q
    rw [eLpNorm_exponent_top hm]
    simpa [c] using eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hbound)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  have hqr : 1 ≤ q.toReal := by
    exact_mod_cast ENNReal.toReal_mono hqt hq
  have hpow (x : E) : ‖heatKernel t x‖ₑ ^ q.toReal ≤
      ENNReal.ofReal (c ^ (q.toReal - 1)) * ENNReal.ofReal (heatKernel t x) := by
    rw [Real.enorm_eq_ofReal (heatKernel_pos ht x).le, ENNReal.ofReal_rpow_of_nonneg
      (heatKernel_pos ht x).le (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc (heatKernel t x) ^ q.toReal =
        (heatKernel t x) ^ (q.toReal - 1) * heatKernel t x := by
          rw [← rpow_add_one (heatKernel_pos ht x).ne', sub_add_cancel]
      _ ≤ c ^ (q.toReal - 1) * heatKernel t x :=
          mul_le_mul_of_nonneg_right
            (rpow_le_rpow (heatKernel_pos ht x).le (heatKernel_le ht x) (by linarith))
            (heatKernel_pos ht x).le
  have hint : ∫⁻ x : E, ‖heatKernel t x‖ₑ ^ q.toReal ≤
      ENNReal.ofReal (c ^ (q.toReal - 1)) := by
    calc (∫⁻ x : E, ‖heatKernel t x‖ₑ ^ q.toReal) ≤
        ∫⁻ x : E, ENNReal.ofReal (c ^ (q.toReal - 1)) * ENNReal.ofReal (heatKernel t x) :=
          lintegral_mono hpow
      _ = ENNReal.ofReal (c ^ (q.toReal - 1)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel ht)
              (Filter.Eventually.of_forall fun x => (heatKernel_pos ht x).le),
            integral_heatKernel ht, ENNReal.ofReal_one, mul_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hm]
  refine (ENNReal.rpow_le_rpow hint (by positivity)).trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← rpow_mul hc.le]
  have he : (q.toReal - 1) * (1 / q.toReal) = 1 - 1 / q.toReal := by
    field_simp
  rw [he]
  simp only [c, ← rpow_mul (by positivity : 0 ≤ 4 * π * t)]

/-- The heat kernel belongs to every `Lᵠ` with `1 ≤ q ≤ ∞`. -/
theorem memLp_heatKernel {t : ℝ} (ht : 0 < t) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLp (heatKernel t : E → ℝ) q volume :=
  (eLpNorm_heatKernel_le ht hq).trans_lt ENNReal.ofReal_lt_top

/-- **Pointwise heat smoothing.** For Hölder conjugate exponents `q, p`,
`‖(K_t ⋆ f)(x)‖ ≤ (4πt)^(-n/(2p)) ‖f‖_p`, including `p = 1, ∞`.
The `Lᵖ` norm is written as an extended norm so the estimate also applies to measurable data
without an integrability assumption. -/
theorem enorm_heatKernel_convolution_le {t : ℝ} (ht : 0 < t) {p q : ℝ≥0∞}
    [q.HolderConjugate p] {f : E → F} (hf : AEStronglyMeasurable f volume) (x : E) :
    ‖(heatKernel t ⋆ f) x‖ₑ ≤
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / (2 * p.toReal))) *
        eLpNorm f p volume := by
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
theorem eLpNorm_heatSemigroup_top_le [CompleteSpace F] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [q.HolderConjugate p] (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    eLpNorm (heatSemigroup hp t f) ∞ volume ≤
      ENNReal.ofReal ((4 * π * (t : ℝ)) ^
        (-(Module.finrank ℝ E : ℝ) / (2 * p.toReal))) * eLpNorm f p volume := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  have hae := heatSemigroup_ae_eq_convolution hp ht (Lp.memLp f)
  have he : (Lp.memLp f).toLp f = f := Lp.toLp_coeFn f (Lp.memLp f)
  rw [he] at hae
  filter_upwards [hae] with x hx
  rw [hx]
  exact enorm_heatKernel_convolution_le (q := q) (by positivity) (Lp.aestronglyMeasurable f) x

/-- **Instantaneous smoothness for `Lᵖ` data.** At every positive time the heat semigroup
has a smooth representative. No boundedness of the initial datum is required. -/
theorem exists_contDiff_ae_eq_heatSemigroup [CompleteSpace F] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [q.HolderConjugate p] (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    ∃ u : E → F, ContDiff ℝ (⊤ : ℕ∞) u ∧
      (heatSemigroup hp t f : E → F) =ᵐ[volume] u := by
  let s : ℝ≥0 := t / 2
  have hs : s ≠ 0 := by positivity
  have hsum : s + s = t := add_halves t
  let g := heatSemigroup hp s f
  -- The first half-step makes the datum essentially bounded.
  have hg : MemLp (g : E → F) ∞ volume :=
    (eLpNorm_heatSemigroup_top_le (q := q) hp hs f).trans_lt (by finiteness)
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
  have hae := heatSemigroup_ae_eq_convolution hp hs (Lp.memLp g)
  rwa [Lp.toLp_coeFn g (Lp.memLp g)] at hae

end TauCeti
