/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.Analysis.PDE.HeatKernel.HeatEquation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.HeatKernel.Derivatives

/-!
# Smoothing by the heat semigroup

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

The same splitting gives the **smoothing estimates** in every `Lᵖ`, `1 ≤ p < ∞`: the smooth
representative `u` of `e^{tΔ} f` satisfies

`‖D^m u‖_p ≤ C t^(-m/2) ‖f‖_p`,

with `C` depending only on `m` and the dimension. The derivatives of `K_{t/2} ⋆ g` are the
convolutions `D^m K_{t/2} ⋆ g`, so Young's inequality bounds them by `‖D^m K_{t/2}‖_{L¹} ‖g‖_p`,
the kernel bound `‖D^m K_s‖_{L¹} ≤ C s^(-m/2)` supplies the power of `t`, and the contraction
property of the semigroup gives `‖g‖_p ≤ ‖f‖_p` for `g = e^{(t/2)Δ} f`. For `m = 2` this bounds
`‖Δ u‖_p` by `C t⁻¹ ‖f‖_p`. For essentially bounded data the estimate holds directly, including
`p = ∞`.

## Main declarations

* `TauCeti.enorm_heatKernel_convolution_le`, `TauCeti.eLpNorm_heatSemigroup_top_le`:
  ultracontractivity.
* `TauCeti.exists_contDiff_ae_eq_heatSemigroup`: the smooth representative.
* `TauCeti.eLpNorm_iteratedFDeriv_heatKernel_convolution_le`,
  `TauCeti.exists_eLpNorm_iteratedFDeriv_heatKernel_convolution_le`: the `Lᵖ` bounds on the
  derivatives of `K_t ⋆ g` for essentially bounded `g`.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_le_of_ae_eq_heatSemigroup`: the smoothing estimates for
  the heat semigroup on `Lᵖ`.
* `TauCeti.exists_eLpNorm_laplacian_le_of_ae_eq_heatSemigroup`: the `Lᵖ` bound on the
  Laplacian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1.
* E. B. Davies, *Heat Kernels and Spectral Theory*, Chapter 2 (ultracontractivity).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Real
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
  have h := eNorm_convolution_le (p := q) (q := p) (.lsmul ℝ ℝ)
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
  apply eLpNormEssSup_le_of_ae_eNorm_bound
  filter_upwards [heatSemigroup_ae_eq_convolution_coeFn hp ht f] with x hx
  rw [hx]
  exact enorm_heatKernel_convolution_le (by positivity) Fact.out (Lp.aestronglyMeasurable f) x

/-- **`Lᵖ` bounds on the derivatives of a heat convolution.** If `g` is essentially bounded, then
for `t > 0` and `1 ≤ p ≤ ∞`, `‖D^m (K_t ⋆ g)‖_p ≤ ‖D^m K_t‖_{L¹} ‖g‖_p`. The essential bound on
`g` only makes `K_t ⋆ g` smooth; it does not enter the estimate. -/
theorem eLpNorm_iteratedFDeriv_heatKernel_convolution_le {t M : ℝ} (ht : 0 < t) {g : E → F}
    (hg : AEStronglyMeasurable g volume) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (m : ℕ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) :
    eLpNorm (iteratedFDeriv ℝ m (heatKernel t ⋆ g)) p volume ≤
      ENNReal.ofReal (∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖) *
        eLpNorm g p volume := by
  set L := ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F
  -- `D^m (K_t ⋆ g)` is the convolution of `D^m K_t` with `g` along `L : (A, b) ↦ A ⊗ b`.
  have hconv : iteratedFDeriv ℝ m (heatKernel t ⋆ g) =
      iteratedFDeriv ℝ m (heatKernel t : E → ℝ) ⋆[L, volume] g := by
    ext1 x
    rw [iteratedFDeriv_heatKernel_convolution ht hg hM m x, convolution_def]
    simp only [L, ContinuousMultilinearMap.smulRightL_apply]
  have hK := integrable_iteratedFDeriv_heatKernel (E := E) ht m
  have hL : ‖L‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ContinuousMultilinearMap.norm_smulRightL_le
  rw [hconv]
  calc eLpNorm (iteratedFDeriv ℝ m (heatKernel t : E → ℝ) ⋆[L, volume] g) p volume
      ≤ ‖L‖ₑ * eLpNorm (iteratedFDeriv ℝ m (heatKernel t : E → ℝ)) 1 volume *
          eLpNorm g p volume := eLpNorm_convolution_le L hK.aestronglyMeasurable hg hp
    _ ≤ 1 * eLpNorm (iteratedFDeriv ℝ m (heatKernel t : E → ℝ)) 1 volume *
          eLpNorm g p volume := by gcongr
    _ = ENNReal.ofReal (∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖) *
          eLpNorm g p volume := by
        rw [one_mul, eLpNorm_one_eq_lintegral_eNorm hK.aestronglyMeasurable,
          ofReal_integral_norm_eq_lintegral_eNorm hK]

/-- **Heat smoothing of essentially bounded data, in every `Lᵖ`.** For each order `m` there is a
constant `C`, depending only on `m` and the dimension, such that for every `t > 0`, every
essentially bounded `g` and every `1 ≤ p ≤ ∞`,
`‖D^m (K_t ⋆ g)‖_p ≤ C t^(-m/2) ‖g‖_p`. -/
theorem exists_eLpNorm_iteratedFDeriv_heatKernel_convolution_le (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃t M : ℝ⦄, 0 < t → ∀ ⦃g : E → F⦄, AEStronglyMeasurable g volume →
      (∀ᵐ y, ‖g y‖ ≤ M) → ∀ ⦃p : ℝ≥0∞⦄, 1 ≤ p →
        eLpNorm (iteratedFDeriv ℝ m (heatKernel t ⋆ g)) p volume ≤
          ENNReal.ofReal (C * t ^ (-(m : ℝ) / 2)) * eLpNorm g p volume := by
  obtain ⟨C, hC⟩ := exists_integral_norm_iteratedFDeriv_heatKernel_le (E := E) m
  have hC₀ : 0 ≤ C := by
    have h := hC 1 one_pos
    rw [one_rpow, mul_one] at h
    exact (integral_nonneg fun _ => norm_nonneg _).trans h
  refine ⟨C, hC₀, fun t M ht g hg hM p hp => ?_⟩
  grw [eLpNorm_iteratedFDeriv_heatKernel_convolution_le ht hg hM m hp, hC t ht]

variable [CompleteSpace F]

/-- The essential bound of the heat semigroup at a positive time, as a pointwise almost-everywhere
bound by a real number. -/
private theorem ae_norm_heatSemigroup_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {t : ℝ≥0}
    (ht : t ≠ 0) (f : Lp F p (volume : Measure E)) :
    ∀ᵐ x ∂volume, ‖heatSemigroup hp t f x‖ ≤
      (eLpNorm (heatSemigroup hp t f : E → F) ∞ volume).toReal := by
  have hg : MemLp (heatSemigroup hp t f : E → F) ∞ volume :=
    (eLpNorm_heatSemigroup_top_le hp ht f).trans_lt (by finiteness)
  simpa only [toReal_eLpNorm] using ae_le_lpNorm_exponent_top hg

/-- Splitting the evolution in two half-steps writes the heat semigroup at a positive time as the
heat convolution of an essentially bounded function: `e^{tΔ} f = K_{t/2} ⋆ e^{(t/2)Δ} f`. -/
private theorem heatSemigroup_ae_eq_convolution_heatSemigroup_half {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0) (f : Lp F p (volume : Measure E)) :
    (heatSemigroup hp t f : E → F) =ᵐ[volume]
      heatKernel ((t / 2 : ℝ≥0) : ℝ) ⋆ (heatSemigroup hp (t / 2) f : E → F) := by
  have he : heatSemigroup hp t f = heatSemigroup hp (t / 2) (heatSemigroup hp (t / 2) f) := by
    simpa only [add_halves, Semigroups.ContractionSemigroup.toStronglyContinuousSemigroup_apply]
      using (heatSemigroup hp).toStronglyContinuousSemigroup.map_add_apply (t / 2) (t / 2) f
  rw [he]
  exact heatSemigroup_ae_eq_convolution_coeFn hp (by positivity) _

/-- **Instantaneous smoothness for `Lᵖ` data.** At every positive time the heat semigroup
has a smooth representative. No boundedness of the initial datum is required. -/
theorem exists_contDiff_ae_eq_heatSemigroup {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    ∃ u : E → F, ContDiff ℝ (⊤ : ℕ∞) u ∧
      (heatSemigroup hp t f : E → F) =ᵐ[volume] u :=
  -- The first half-step makes the datum essentially bounded, the second smooths it.
  ⟨_, contDiff_heatKernel_convolution (by positivity)
    (ae_norm_heatSemigroup_le hp (by positivity) f),
    heatSemigroup_ae_eq_convolution_heatSemigroup_half hp ht f⟩

/-- **Smoothing estimates for the heat semigroup on `Lᵖ`.** For each order `m` there is a
constant `C`, depending only on `m` and the dimension, such that for every `1 ≤ p < ∞`, every
`t > 0` and every `f ∈ Lᵖ`, the continuous representative `u` of `e^{tΔ} f` (which is smooth, by
`TauCeti.exists_contDiff_ae_eq_heatSemigroup`) satisfies
`‖D^m u‖_p ≤ C t^(-m/2) ‖f‖_p`. -/
theorem exists_eLpNorm_iteratedFDeriv_le_of_ae_eq_heatSemigroup (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃p : ℝ≥0∞⦄ [Fact (1 ≤ p)] (hp : p ≠ ∞) ⦃t : ℝ≥0⦄, t ≠ 0 →
      ∀ (f : Lp F p (volume : Measure E)) ⦃u : E → F⦄, Continuous u →
        (heatSemigroup hp t f : E → F) =ᵐ[volume] u →
          eLpNorm (iteratedFDeriv ℝ m u) p volume ≤
            ENNReal.ofReal (C * (t : ℝ) ^ (-(m : ℝ) / 2)) * eLpNorm f p volume := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_heatKernel_convolution_le (E := E) (F := F) m
  refine ⟨C * 2 ^ ((m : ℝ) / 2), by positivity, fun p _ hp t ht f u hu hfu => ?_⟩
  set s : ℝ≥0 := t / 2
  have hs : (0 : ℝ) < s := by positivity
  set g := heatSemigroup hp s f
  have hbound := ae_norm_heatSemigroup_le hp (NNReal.coe_ne_zero.1 hs.ne') f
  -- `u` is the smooth function `K_s ⋆ g`, two continuous functions being equal almost everywhere.
  have hug : u = heatKernel (s : ℝ) ⋆ (g : E → F) :=
    (Continuous.ae_eq_iff_eq volume hu (contDiff_heatKernel_convolution hs hbound).continuous).1
      (hfu.symm.trans (heatSemigroup_ae_eq_convolution_heatSemigroup_half hp ht f))
  -- The semigroup is a contraction, so `‖g‖_p ≤ ‖f‖_p`.
  have hgf : eLpNorm (g : E → F) p volume ≤ eLpNorm f p volume := by
    rw [← Lp.eNorm_def, ← Lp.eNorm_def, eNorm_le_iff_norm_le]
    exact ContinuousLinearMap.le_of_opNorm_le _ ((heatSemigroup hp).contracting s) f |>.trans_eq
      (one_mul _)
  have hs2 : (s : ℝ) = (t : ℝ) / 2 := by simp [s]
  have hst : (s : ℝ) ^ (-(m : ℝ) / 2) = 2 ^ ((m : ℝ) / 2) * (t : ℝ) ^ (-(m : ℝ) / 2) := by
    rw [hs2, div_rpow t.coe_nonneg zero_le_two]
    -- It remains to write `t ^ a / 2 ^ a` as `2 ^ (-a) * t ^ a`.
    rw [div_eq_inv_mul, ← rpow_neg zero_le_two, neg_div, neg_neg]
  rw [hug]
  grw [hC hs (Lp.aestronglyMeasurable g) hbound Fact.out, hgf, hst, ← mul_assoc]

/-- **The `Lᵖ` bound on the Laplacian of the heat semigroup.** There is a constant `C`, depending
only on the dimension, such that for every `1 ≤ p < ∞`, every `t > 0` and every `f ∈ Lᵖ`, the
continuous representative `u` of `e^{tΔ} f` satisfies `‖Δ u‖_p ≤ C t⁻¹ ‖f‖_p`. Formally
`∂ₜ e^{tΔ} f = Δ e^{tΔ} f`, so this is the `1 / t` bound characteristic of the analytic heat
semigroup; the time derivative of the semigroup in `Lᵖ` is not computed here. -/
theorem exists_eLpNorm_laplacian_le_of_ae_eq_heatSemigroup :
    ∃ C, 0 ≤ C ∧ ∀ ⦃p : ℝ≥0∞⦄ [Fact (1 ≤ p)] (hp : p ≠ ∞) ⦃t : ℝ≥0⦄, t ≠ 0 →
      ∀ (f : Lp F p (volume : Measure E)) ⦃u : E → F⦄, Continuous u →
        (heatSemigroup hp t f : E → F) =ᵐ[volume] u →
          eLpNorm (Δ u) p volume ≤ ENNReal.ofReal (C * (t : ℝ)⁻¹) * eLpNorm f p volume := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_le_of_ae_eq_heatSemigroup (E := E) (F := F) 2
  refine ⟨Module.finrank ℝ E * C, by positivity, fun p _ hp t ht f u hu hfu => ?_⟩
  have hD := hC hp ht f hu hfu
  norm_num only [Nat.cast_ofNat, rpow_neg_one] at hD
  -- `u` is the smooth representative, so `Δ u` is continuous.
  obtain ⟨w, hw, hfw⟩ := exists_contDiff_ae_eq_heatSemigroup hp ht f
  have huw : u = w := (Continuous.ae_eq_iff_eq volume hu hw.continuous).1 (hfu.symm.trans hfw)
  have hΔ : AEStronglyMeasurable (Δ u) volume := by
    rw [huw]
    exact (hw.of_le (by norm_cast)).continuous_laplacian.aestronglyMeasurable
  -- Pointwise, `‖Δ u‖ ≤ dim E * ‖D² u‖`.
  have hpt : ∀ᵐ x ∂volume, ‖Δ u x‖ ≤ Module.finrank ℝ E * ‖iteratedFDeriv ℝ 2 u x‖ :=
    ae_of_all _ fun x => by
      have h := norm_laplacian_le u x
      rwa [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at h
  grw [eLpNorm_le_mul_eLpNorm_of_ae_le_mul hΔ hpt p, hD, ← mul_assoc, ← ENNReal.ofReal_mul
    (by positivity), mul_assoc]

end TauCeti
