/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The Duhamel heat potential solves the inhomogeneous heat equation

For a forcing `f : ℝ → E → F` the Duhamel potential is
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` (`TauCeti.heatDuhamelPotential`). This file proves that
it solves the inhomogeneous heat equation at positive times:

`∂ₜw(t, x) = Δw(t, ·)(x) + f(t, x)`

whenever `f` is jointly measurable and essentially bounded on `(0, T) × E`, its time slices are
`α`-Hölder in space with a common constant, `0 < α ≤ 2`, and `s ↦ f(s, x)` is continuous at
`t ∈ (0, T)`. No further regularity in time is assumed. The Laplacian of `w(t, ·)` is computed
under the time integral (`TauCeti.laplacian_heatDuhamelPotential`).

The time derivative is not taken directly under the integral `∫₀ᵗ`: its upper limit moves with
`t`, and the time derivative `Δ(K_{t-s} ⋆ f(s, ·))(x)` of its integrand is singular at the
diagonal `s = t`. Bounded data alone only give the non-integrable bound `O(|t - s|⁻¹)` there;
spatial Hölder continuity improves it to the integrable bound `O(|t - s|^(α/2 - 1))`. Instead,
extending each Cauchy potential `u_s(r) = (K_r ⋆ f(s, ·))(x)` by `f(s, x)` for `r ≤ 0`
(`TauCeti.heatCauchyPotential`) gives, for `0 < τ < T`,

`w(τ, x) = ∫₀ᵀ u_s(τ - s) ds - ∫_τ^T f(s, x) ds`.

The second term has derivative `-f(t, x)` at a point of continuity. For the first, Hölder
continuity in space bounds the difference quotients `|u_s(τ - s) - u_s(t - s)| / |τ - t|` by
`C H |t - s|^(α/2 - 1)` (`TauCeti.exists_norm_heatCauchyPotential_sub_heatCauchyPotential_le_mul`),
which is integrable in `s`, so dominated convergence differentiates under the integral sign. The
derivative of `u_s(τ - s)` at `τ = t` is `Δ(K_{t-s} ⋆ f(s, ·))(x)` for `s < t` and zero for `s > t`,
and these integrate to `Δw(t, ·)(x)`.

## Main declarations

* `TauCeti.intervalIntegrable_laplacian_heatKernel_convolution`,
  `TauCeti.laplacian_heatDuhamelPotential`: `Δw(t, ·)(x) = ∫₀ᵗ Δ(K_{t-s} ⋆ f(s, ·))(x) ds`, with
  an integrable integrand.
* `TauCeti.hasDerivAt_heatDuhamelPotential`: the inhomogeneous heat equation
  `∂ₜw = Δw + f` at positive times.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1 (Duhamel's principle for the
  nonhomogeneous heat equation).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3 (the
  volume potential of a forcing Hölder continuous in space).
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Real Set Topology
open scoped Convolution NNReal Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → E → F} {M t T : ℝ} {H α : ℝ≥0}

/-- For `f` jointly measurable and essentially bounded on `(0, t) × E`, with `f(s, ·)` `α`-Hölder
for almost every `0 < s < t` and `α > 0`, the time integrand
`s ↦ Δ(K_{t-s} ⋆ f(s, ·))(x)` of the Laplacian of the Duhamel potential is interval integrable on
`[0, t]`. -/
theorem intervalIntegrable_laplacian_heatKernel_convolution
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (ht : 0 < t)
    (x : E) :
    IntervalIntegrable (fun s => Δ (heatKernel (t - s) ⋆ f s) x) volume 0 t := by
  have h := intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith hf hfM hH hα
    ht le_rfl x
  simp only [laplacian_eq_traceL_iteratedFDeriv]
  exact ⟨ContinuousLinearMap.integrable_comp _ h.1, ContinuousLinearMap.integrable_comp _ h.2⟩

/-- **The Laplacian of the Duhamel potential.** If `f` is jointly measurable and essentially
bounded on `(0, t) × E`, and `f(s, ·)` is `α`-Hölder for almost every `0 < s < t`, with `α > 0`,
then the Laplacian of `w(t, ·)` is computed under the time integral:
`Δw(t, ·)(x) = ∫₀ᵗ Δ(K_{t-s} ⋆ f(s, ·))(x) ds`. -/
theorem laplacian_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (ht : 0 < t)
    (x : E) :
    Δ (heatDuhamelPotential f t) x = ∫ s in 0..t, Δ (heatKernel (t - s) ⋆ f s) x := by
  simp only [laplacian_eq_traceL_iteratedFDeriv]
  rw [iteratedFDeriv_heatDuhamelPotential_of_holderWith hf hfM hH hα ht le_rfl]
  exact (ContinuousLinearMap.intervalIntegral_comp_comm _
    (intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith hf hfM hH hα ht
      le_rfl x)).symm

omit [CompleteSpace F] in
/-- The time-shifted Cauchy potentials `s ↦ u_s(τ - s)` of the slices of a jointly measurable
forcing are strongly measurable. -/
private theorem stronglyMeasurable_heatCauchyPotential_sub
    (hf : StronglyMeasurable (Function.uncurry f)) (τ : ℝ) (x : E) :
    StronglyMeasurable fun s => heatCauchyPotential (f s) (τ - s) x := by
  simp only [heatCauchyPotential_def]
  refine StronglyMeasurable.integral_prod_right
    (f := fun s y => heatKernel 1 y • f s (x - √(τ - s) • y)) ?_
  exact ((contDiff_heatKernel (k := 0) 1).continuous.comp continuous_snd).stronglyMeasurable.smul
    (hf.comp_measurable (g := fun p : ℝ × E => (p.1, x - √(τ - p.1) • p.2)) (by fun_prop))

/-- On `(0, T)`, the Duhamel potential is `w(τ, x) = ∫₀ᵀ u_s(τ - s) ds - ∫_τ^T f(s, x) ds`, where
`u_s` is the Cauchy potential of `f(s, ·)`, equal to `f(s, x)` at nonpositive times. -/
private theorem heatDuhamelPotential_eq_setIntegral_sub
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M) {x : E}
    (hfint : IntervalIntegrable (fun s => f s x) volume 0 T) {τ : ℝ} (hτ : τ ∈ Ioo 0 T) :
    heatDuhamelPotential f τ x =
      (∫ s in Ioo 0 T, heatCauchyPotential (f s) (τ - s) x) - ∫ s in τ..T, f s x := by
  set u : ℝ → F := fun s => heatCauchyPotential (f s) (τ - s) x
  have hconv : ∀ᵐ s ∂volume, s ∈ Ι 0 τ → u s = (heatKernel (τ - s) ⋆ f s) x := by
    filter_upwards [Measure.ae_ne volume τ] with s hsτ hs
    rw [uIoc_of_le hτ.1.le] at hs
    exact heatCauchyPotential_eq_convolution _ (sub_pos.2 (lt_of_le_of_ne hs.2 hsτ)) x
  have hconst : EqOn u (fun s => f s x) (uIcc τ T) := fun s hs => by
    rw [uIcc_of_le hτ.2.le] at hs
    exact heatCauchyPotential_of_nonpos _ (sub_nonpos.2 hs.1) x
  have hi₁ : IntervalIntegrable u volume 0 τ :=
    (intervalIntegrable_heatKernel_convolution hf
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hτ.2.le) hfM) hτ.1 x).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 (hconv.mono fun s hs hsI => (hs hsI).symm))
  have hi₂ : IntervalIntegrable u volume τ T :=
    (intervalIntegrable_congr (hconst.mono uIoc_subset_uIcc)).2 (hfint.mono_set (by
      rw [uIcc_of_le hτ.2.le, uIcc_of_le (hτ.1.trans hτ.2).le]
      exact Icc_subset_Icc_left hτ.1.le))
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (hτ.1.trans hτ.2).le,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,
    intervalIntegral.integral_congr hconst, heatDuhamelPotential_def,
    intervalIntegral.integral_congr_ae hconv, add_sub_cancel_right]

/-- The time derivative of `τ ↦ ∫₀ᵀ u_s(τ - s) ds` at `t` is `Δw(t, ·)(x)`, by dominated
convergence of the difference quotients. -/
private theorem hasDerivAt_setIntegral_heatCauchyPotential_sub
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) (hα₀ : 0 < α) (hα₂ : α ≤ 2)
    (ht : 0 < t) (htT : t < T) (x : E) :
    HasDerivAt (fun τ => ∫ s in Ioo 0 T, heatCauchyPotential (f s) (τ - s) x)
      (Δ (heatDuhamelPotential f t) x) t := by
  set μ := volume.restrict (Ioo (0 : ℝ) T)
  set u : ℝ → ℝ → F := fun τ s => heatCauchyPotential (f s) (τ - s) x
  -- Almost every slice is Hölder, continuous and bounded everywhere.
  have hgood : ∀ᵐ s ∂μ, HolderWith H α (f s) ∧ Continuous (f s) ∧ ∀ y, ‖f s y‖ ≤ M := by
    filter_upwards [hfM, hH] with s hsM hsH
    have hc := hsH.continuous hα₀
    exact ⟨hsH, hc, ((continuous_norm.comp hc).ae_le_iff_le volume continuous_const).1 hsM⟩
  have hfM' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right htT.le) hfM
  have hH' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right htT.le) hH
  obtain ⟨C, hC⟩ := exists_norm_heatCauchyPotential_sub_heatCauchyPotential_le_mul
    (E := E) (F := F) hα₂
  -- The derivative of `u_s(τ - s)` at `τ = t` is `Δ(K_{t-s} ⋆ f(s, ·))(x)` for `s < t`, else `0`.
  set G : ℝ → F := (Iio t).indicator fun s => Δ (heatKernel (t - s) ⋆ f s) x
  have hGint : Integrable G μ := by
    have h := intervalIntegrable_laplacian_heatKernel_convolution hf hfM' hH' hα₀ ht x
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le] at h
    refine (integrable_indicator_iff measurableSet_Iio).2 ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioo,
      min_eq_left htT.le]
    exact h
  have hbound : Integrable (fun s => C * H * |t - s| ^ ((α : ℝ) / 2 - 1)) μ := by
    have hr : -(Module.finrank ℝ ℝ : ℝ) < (α : ℝ) / 2 - 1 := by
      have : (0 : ℝ) < α := hα₀
      rw [Module.finrank_self, Nat.cast_one]
      linarith
    have h := ((locallyIntegrable_norm_sub_rpow (mu := volume) hr t).integrableOn_isCompact
      isCompact_Icc).mono_set (Ioo_subset_Icc_self (a := 0) (b := T))
    simp only [Real.norm_eq_abs] at h
    exact h.const_mul (C * H)
  set L : F →L[ℝ] ℝ →L[ℝ] F := ContinuousLinearMap.smulRightL ℝ ℝ F 1
  have key := hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := μ) (F := u)
    (F' := fun s => L (G s)) (x₀ := t) (Ioo_mem_nhds ht htT)
    (fun τ _ => (stronglyMeasurable_heatCauchyPotential_sub hf τ x).aestronglyMeasurable)
    ((integrable_const M).mono'
      (stronglyMeasurable_heatCauchyPotential_sub hf t x).aestronglyMeasurable
      (hgood.mono fun s hs => norm_heatCauchyPotential_le hs.2.2 _ x))
    (L.integrable_comp hGint).aestronglyMeasurable ?_ hbound ?_
  · have h := key.2.hasDerivAt
    rw [L.integral_comp_comm hGint, setIntegral_indicator measurableSet_Iio, Ioo_inter_Iio,
      min_eq_right htT.le, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      ← laplacian_heatDuhamelPotential hf hfM' hH' hα₀ ht x] at h
    simpa [L] using h
  · -- The pointwise Lipschitz bound at `t`, away from the diagonal `s = t`.
    filter_upwards [hgood, Measure.ae_ne μ t] with s hs hst τ _
    have h := hC hs.1 hs.2.1 hs.2.2 (a := t - s) (sub_ne_zero.2 hst.symm) (τ - s) x
    rw [sub_sub_sub_cancel_right] at h
    rw [Real.norm_eq_abs]
    exact h.trans_eq (by ring)
  · filter_upwards [hgood, Measure.ae_ne μ t] with s hs hst
    rcases lt_or_gt_of_ne hst with hst | hst
    · -- Before `t`, the heat equation for the Cauchy potential of `f(s, ·)`.
      have h := (hasDerivAt_heatCauchyPotential_of_aestronglyMeasurable
        hs.2.1.aestronglyMeasurable (ae_of_all _ hs.2.2) (sub_pos.2 hst) x).comp_sub_const t s
      rw [heatCauchyPotential_eq_convolution_fun _ (sub_pos.2 hst)] at h
      simpa [G, L, indicator_of_mem (mem_Iio.2 hst),
        ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using h.hasFDerivAt
    · -- After `t`, the integrand is the constant `f(s, x)` near `t`.
      have h : HasDerivAt (u · s) 0 t :=
        (hasDerivAt_const t (f s x)).congr_of_eventuallyEq
          (eventually_of_mem (Iio_mem_nhds hst) fun τ hτ =>
            heatCauchyPotential_of_nonpos _ (sub_nonpos.2 (mem_Iio.1 hτ).le) x)
      simpa [G, L, indicator_of_notMem (notMem_Iio.2 hst.le),
        ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using h.hasFDerivAt

/-- **The Duhamel potential solves the inhomogeneous heat equation.** Let `0 < α ≤ 2` and
`0 < t < T`. Let `f` be jointly measurable and essentially bounded on `(0, T) × E`, with `f(s, ·)`
`α`-Hölder with constant `H` for almost every `0 < s < T`, and let `s ↦ f(s, x)` be continuous at
`t`. Then the Duhamel potential satisfies `∂ₜw(t, x) = Δw(t, ·)(x) + f(t, x)`. -/
theorem hasDerivAt_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) (hα₀ : 0 < α) (hα₂ : α ≤ 2)
    (ht : 0 < t) (htT : t < T) {x : E} (hfx : ContinuousAt (fun s => f s x) t) :
    HasDerivAt (fun τ => heatDuhamelPotential f τ x)
      (Δ (heatDuhamelPotential f t) x + f t x) t := by
  have hT : 0 < T := ht.trans htT
  have hfm : StronglyMeasurable fun s => f s x :=
    hf.comp_measurable (measurable_id.prodMk measurable_const)
  have hfint : IntervalIntegrable (fun s => f s x) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
    refine (integrable_const M).mono' hfm.aestronglyMeasurable ?_
    filter_upwards [hfM, hH] with s hsM hsH
    exact ((continuous_norm.comp (hsH.continuous hα₀)).ae_le_iff_le volume continuous_const).1
      hsM x
  have hI : HasDerivAt (fun τ => ∫ s in τ..T, f s x) (-f t x) t :=
    intervalIntegral.integral_hasDerivAt_left (hfint.mono_set (by
      rw [uIcc_of_le htT.le, uIcc_of_le hT.le]
      exact Icc_subset_Icc_left ht.le)) hfm.stronglyMeasurableAtFilter hfx
  rw [← sub_neg_eq_add]
  exact ((hasDerivAt_setIntegral_heatCauchyPotential_sub hf hfM hH hα₀ hα₂ ht htT x).sub
    hI).congr_of_eventuallyEq (eventually_of_mem (Ioo_mem_nhds ht htT)
      fun τ hτ => heatDuhamelPotential_eq_setIntegral_sub hf hfM hfint hτ)

end TauCeti
