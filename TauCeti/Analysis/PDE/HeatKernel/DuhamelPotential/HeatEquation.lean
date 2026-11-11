/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.InitialTrace
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Duhamel heat potential solves the inhomogeneous heat equation

For a forcing term `f : ℝ → E → F` on a finite-dimensional real inner product space `E`, the
Duhamel potential `w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` (`TauCeti.heatDuhamelPotential`) is
the candidate solution of `∂ₜw = Δw + f` with zero initial datum. This file proves that it is a
solution at positive times. Let `f` be jointly measurable and essentially bounded on `(0, T) × E`,
with `f(s, ·)` `α`-Hölder with constant `H` for almost every `0 < s < T`, where `α > 0`.

* `TauCeti.heatDuhamelPotential_eq_integral`: **Duhamel's principle in integrated form**,
  `w(t, x) = ∫₀ᵗ (Δw(σ, x) + f(σ, x)) dσ` for `0 ≤ t ≤ T`.
* `TauCeti.laplacian_heatDuhamelPotential_of_holderWith`: the Laplacian under the time integral,
  `Δw(t, x) = ∫₀ᵗ Δ(K_{t-s} ⋆ f(s, ·))(x) ds`.
* `TauCeti.continuousOn_laplacian_heatDuhamelPotential`: for `α < 2`, `σ ↦ Δw(σ, x)` is
  continuous on `[0, T]`.
* `TauCeti.hasDerivWithinAt_heatDuhamelPotential`, `TauCeti.hasDerivAt_heatDuhamelPotential`:
  **the inhomogeneous heat equation**. If moreover `α < 2` and `s ↦ f(s, x)` is continuous at
  `t`, then `∂ₜw(t, x) = Δw(t, x) + f(t, x)`, within `[0, T]` for `t ∈ [0, T]` and two-sided for
  `t ∈ (0, T)`.
* `TauCeti.hasDerivWithinAt_heatDuhamelPotential_of_holderOnWith`: the same on the closed slab
  `E × [0, T]` for forcing parabolically Hölder there, which supplies both hypotheses.

Together with the Hölder estimates of the Hessian in
`TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic`, this is the time regularity of the
Duhamel potential needed to place it in the parabolic Hölder spaces of a closed slab.

## The argument

The time integrand of the potential is singular at `s = t`, so the derivative is not computed by
differentiating under the integral. Instead, write `v_s(σ) = u_s(σ - s, x)`, where `u_s` is the
Cauchy heat potential of the slice `f(s, ·)` (`TauCeti.heatCauchyPotential`), so that
`v_s(σ) = (K_{σ-s} ⋆ f(s, ·))(x)` for `σ > s` and `v_s(σ) = f(s, x)` for `σ ≤ s`. The function
`v_s` is continuous, by the temporal Hölder estimate of the Cauchy potential; it is constant for
`σ < s`; and for `σ > s` its derivative is `Δ(K_{σ-s} ⋆ f(s, ·))(x)` by the heat equation for the
heat convolution. This derivative is `O(H (σ - s)^((α - 2)/2))`, which is integrable for `α > 0`,
so the fundamental theorem of calculus with one exceptional point gives
`(K_{t-s} ⋆ f(s, ·))(x) - f(s, x) = ∫₀ᵗ ∂_σ v_s(σ) dσ`. Integrating in `s` and exchanging the
order of integration by Fubini's theorem, the inner integral `∫₀^σ Δ(K_{σ-s} ⋆ f(s, ·))(x) ds` is
`Δw(σ, x)`, because the Hessian of `w(σ, ·)` is computed under the time integral
(`TauCeti.iteratedFDeriv_heatDuhamelPotential_of_holderWith`). This gives the integrated form.
For the derivative at `t`, the integrand `Δw(·, x) + f(·, x)` is continuous at `t`: the Hessian
of `w` is Hölder in time (`TauCeti.exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential`),
and the Laplacian is a sum of its values along an orthonormal basis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1, Theorem 2 (Duhamel's principle
  for the nonhomogeneous heat equation).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3 (the
  volume potential of a forcing Hölder continuous in space).
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Module Real Set Topology
open scoped Convolution NNReal Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → E → F} {M t T : ℝ} {H α : ℝ≥0}

/-- The time derivative of the slice `σ ↦ u_s(σ - s, x)`, where `u_s` is the Cauchy heat potential
of `f(s, ·)`: the Laplacian of `K_{σ-s} ⋆ f(s, ·)` at `x` for `σ > s`, and zero for `σ ≤ s`. -/
private def laplacianSlice (f : ℝ → E → F) (x : E) (s σ : ℝ) : F :=
  if s < σ then Δ (heatKernel (σ - s) ⋆ f s) x else 0

/-- For `α > 0`, the exponent `(α - 2)/2` of the Laplacian bound exceeds `-1`. -/
private theorem neg_one_lt_sub_two_div_two (hα : 0 < α) : -1 < ((α : ℝ) - 2) / 2 := by
  have : (0 : ℝ) < α := hα
  linarith

/-- Off the diagonal `σ = s`, the slice `σ ↦ u_s(σ - s, x)` has derivative `laplacianSlice`. -/
private theorem hasDerivAt_heatCauchyPotential_sub {s σ : ℝ}
    (hg : AEStronglyMeasurable (f s)) (hM : ∀ᵐ y, ‖f s y‖ ≤ M) (hσ : σ ≠ s) (x : E) :
    HasDerivAt (fun σ => heatCauchyPotential (f s) (σ - s) x) (laplacianSlice f x s σ) σ := by
  rcases hσ.lt_or_gt with hσ | hσ
  · simp only [laplacianSlice, hσ.not_gt, ↓reduceIte]
    refine (hasDerivAt_const σ (f s x)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hσ] with σ' hσ'
    exact heatCauchyPotential_of_nonpos _ (by linarith) x
  · simp only [laplacianSlice, hσ, ↓reduceIte]
    refine ((hasDerivAt_heatKernel_convolution (sub_pos.2 hσ) hg hM x).comp_sub_const σ s
      ).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hσ] with σ' hσ'
    exact heatCauchyPotential_eq_convolution _ (sub_pos.2 hσ') x

/-- For a bounded `α`-Hölder slice, `laplacianSlice` is interval integrable in its time variable
on every interval: it is `O(H (σ - s)^((α - 2)/2))` for `σ > s` and vanishes for `σ ≤ s`. -/
private theorem intervalIntegrable_laplacianSlice {s : ℝ} (hg : AEStronglyMeasurable (f s))
    (hM : ∀ᵐ y, ‖f s y‖ ≤ M) (hH : HolderWith H α (f s)) (hα : 0 < α) (x : E) (a b : ℝ) :
    IntervalIntegrable (laplacianSlice f x s) volume a b := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_laplacian_heatKernel_convolution_le (E := E) (F := F) (α := α)
  refine ((intervalIntegrable_sub_const_rpow (neg_one_lt_sub_two_div_two hα) s a b).const_mul
    (C * H)).mono_fun ?_
    (ae_of_all _ fun σ => ?_)
  · refine (stronglyMeasurable_deriv
      (fun σ => heatCauchyPotential (f s) (σ - s) x)).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_of_ae ((countable_singleton s).ae_notMem volume)] with σ hσ
    exact (hasDerivAt_heatCauchyPotential_sub hg hM hσ x).deriv
  · simp only [laplacianSlice]
    split_ifs with h
    · exact (hC hg hM hH (sub_pos.2 h) x).trans (le_abs_self _)
    · rw [norm_zero]
      exact norm_nonneg _

/-- **The fundamental theorem of calculus for a slice.** For a bounded `α`-Hölder slice,
`∫ₐᵇ laplacianSlice f x s σ dσ = u_s(b - s, x) - u_s(a - s, x)`. -/
private theorem integral_laplacianSlice {s : ℝ} (hg : AEStronglyMeasurable (f s))
    (hM : ∀ᵐ y, ‖f s y‖ ≤ M) (hH : HolderWith H α (f s)) (hα : 0 < α) {a b : ℝ} (hab : a ≤ b)
    (x : E) :
    ∫ σ in a..b, laplacianSlice f x s σ =
      heatCauchyPotential (f s) (b - s) x - heatCauchyPotential (f s) (a - s) x := by
  -- The slice is continuous by the temporal Hölder estimate of the Cauchy heat potential.
  have hhol : HolderOnWith (H * heatKernelMoment E α) (α / 2)
      (fun τ => heatCauchyPotential (f s) τ x) univ :=
    HolderOnWith.of_dist_le fun τ _ τ' _ => by
      simpa [dist_eq_norm, Real.dist_eq] using
        norm_heatCauchyPotential_sub_heatCauchyPotential_le hH (hH.continuous hα) τ τ' x
  have hc : Continuous fun σ => heatCauchyPotential (f s) (σ - s) x :=
    (continuousOn_univ.1 (hhol.continuousOn (by positivity))).comp (continuous_sub_right s)
  exact integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab (countable_singleton s)
    hc.continuousOn (fun σ hσ => hasDerivAt_heatCauchyPotential_sub hg hM hσ.2 x)
    (intervalIntegrable_laplacianSlice hg hM hH hα x a b)

omit [CompleteSpace F] in
/-- `laplacianSlice f x` is jointly measurable, up to the null set of first coordinates `s` at
which `f(s, ·)` is not essentially bounded. -/
private theorem aestronglyMeasurable_laplacianSlice (hf : StronglyMeasurable (Function.uncurry f))
    {μ ν : Measure ℝ} (hfM : ∀ᵐ s ∂μ, ∀ᵐ y, ‖f s y‖ ≤ M) (x : E) :
    AEStronglyMeasurable (Function.uncurry (laplacianSlice f x)) (μ.prod ν) := by
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_stronglyMeasurable_eq_iteratedFDeriv_heatKernel_convolution hf 2 x
  -- The Laplacian is a continuous linear functional of the Hessian.
  have hΨ : StronglyMeasurable fun p : ℝ × ℝ => if p.1 < p.2 then
      (∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F
        ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]) (Φ (p.1, p.2 - p.1)) else 0 :=
    StronglyMeasurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((ContinuousLinearMap.continuous _).comp_stronglyMeasurable
        (hΦ.comp_measurable (by fun_prop)))
      stronglyMeasurable_const
  refine hΨ.aestronglyMeasurable.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfM] with p hp
  simp only [Function.uncurry_def, laplacianSlice]
  split_ifs with h
  · rw [hΦeq p.1 (p.2 - p.1) M (sub_pos.2 h) hp, laplacian_eq_traceL_iteratedFDeriv]
  · rfl

/-- `laplacianSlice f x` is integrable on the square `(0, t)²`: for almost every `s` its slice is
integrable in `σ`, with integral of its norm at most `C H t^(α/2) / (α/2)`. -/
private theorem integrable_laplacianSlice (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (x : E) :
    Integrable (Function.uncurry (laplacianSlice f x))
      ((volume.restrict (Ioo 0 t)).prod (volume.restrict (Ioo 0 t))) := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_laplacian_heatKernel_convolution_le (E := E) (F := F) (α := α)
  set p : ℝ := ((α : ℝ) - 2) / 2 with hp_def
  have hp : -1 < p := neg_one_lt_sub_two_div_two hα
  have hp1 : 0 < p + 1 := by linarith
  have hfs (s : ℝ) : AEStronglyMeasurable (f s) :=
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  have hmeas := aestronglyMeasurable_laplacianSlice (ν := volume.restrict (Ioo 0 t)) hf hfM x
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, (integrable_const (C * H * t ^ (p + 1) / (p + 1))).mono'
    hmeas.norm.integral_prod_right' ?_⟩
  · filter_upwards [hfM, hH] with s hsM hsH
    exact (intervalIntegrable_laplacianSlice (hfs s) hsM hsH hα x 0 t).1.mono_set
      Ioo_subset_Ioc_self
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hfM, hH] with s hs hsM hsH
  have hint := intervalIntegrable_laplacianSlice (hfs s) hsM hsH hα x
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  -- The slice vanishes for `σ ≤ s`, and is `O(H (σ - s)^p)` for `σ > s`.
  have h₀ : ∫ σ in 0..s, ‖laplacianSlice f x s σ‖ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun σ hσ => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hs.1.le] at hσ
    simp [laplacianSlice, not_lt.2 hσ.2]
  have hle : ∫ σ in s..t, ‖laplacianSlice f x s σ‖ ≤ ∫ σ in s..t, C * H * (σ - s) ^ p := by
    refine intervalIntegral.integral_mono_on hs.2.le (hint s t).norm
      ((intervalIntegrable_sub_const_rpow hp s s t).const_mul _) fun σ hσ => ?_
    simp only [laplacianSlice]
    split_ifs with h
    · exact hC (hfs s) hsM hsH (sub_pos.2 h) x
    · rw [norm_zero]
      have := rpow_nonneg (sub_nonneg.2 hσ.1) p
      positivity
  have hval : ∫ σ in s..t, C * H * (σ - s) ^ p = C * H * ((t - s) ^ (p + 1) / (p + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_sub_const_rpow hp]
  calc ∫ σ in Ioo 0 t, ‖laplacianSlice f x s σ‖
      = (∫ σ in 0..s, ‖laplacianSlice f x s σ‖) + ∫ σ in s..t, ‖laplacianSlice f x s σ‖ := by
        rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 s).norm (hint s t).norm,
          intervalIntegral.integral_of_le (hs.1.trans hs.2).le, integral_Ioc_eq_integral_Ioo]
    _ ≤ C * H * ((t - s) ^ (p + 1) / (p + 1)) := by rw [h₀, zero_add, ← hval]; exact hle
    _ ≤ C * H * t ^ (p + 1) / (p + 1) := by
        rw [mul_div_assoc]
        gcongr
        · linarith [hs.2]
        · linarith [hs.1]

/-- **The Laplacian of the Duhamel potential.** Let `f` be jointly measurable and essentially
bounded on `(0, t) × E`, with `f(s, ·)` `α`-Hölder for almost every `0 < s < t`, where `α > 0`.
Then the Laplacian of `w(t, ·)` is computed under the time integral:
`Δw(t, x) = ∫₀ᵗ Δ(K_{t-s} ⋆ f(s, ·))(x) ds`. -/
theorem laplacian_heatDuhamelPotential_of_holderWith
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (ht : 0 < t)
    (x : E) :
    Δ (heatDuhamelPotential f t) x = ∫ s in 0..t, Δ (heatKernel (t - s) ⋆ f s) x := by
  have hint := intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith hf hfM hH
    hα ht le_rfl x
  -- The Laplacian is a continuous linear functional of the Hessian.
  simp only [laplacian_eq_traceL_iteratedFDeriv]
  rw [congrFun (iteratedFDeriv_heatDuhamelPotential_of_holderWith hf hfM hH hα ht le_rfl) x]
  exact (ContinuousLinearMap.intervalIntegral_comp_comm _ hint).symm

/-- **Duhamel's principle in integrated form**, together with the integrability of both terms. -/
private theorem heatDuhamelPotential_eq_integral_add_integral
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (ht : 0 ≤ t)
    (x : E) :
    IntervalIntegrable (fun σ => Δ (heatDuhamelPotential f σ) x) volume 0 t ∧
      IntervalIntegrable (fun σ => f σ x) volume 0 t ∧
      heatDuhamelPotential f t x =
        (∫ σ in 0..t, Δ (heatDuhamelPotential f σ) x) + ∫ σ in 0..t, f σ x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hfs (s : ℝ) : AEStronglyMeasurable (f s) :=
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  have hG := integrable_laplacianSlice hf hfM hH hα x
  -- Integrating `laplacianSlice` in `s` gives the Laplacian of the potential.
  have hΔ : ∀ σ ∈ Ioo 0 t,
      ∫ s in Ioo 0 t, laplacianSlice f x s σ = Δ (heatDuhamelPotential f σ) x := by
    intro σ hσ
    rw [laplacian_heatDuhamelPotential_of_holderWith hf
        (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hσ.2.le) hfM)
        (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hσ.2.le) hH) hα hσ.1 x,
      intervalIntegral.integral_of_le hσ.1.le, integral_Ioc_eq_integral_Ioo,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
        (Ioo_subset_Ioo_right hσ.2.le) fun s hs => ?_]
    · exact setIntegral_congr_fun measurableSet_Ioo fun s hs => by simp [laplacianSlice, hs.2]
    · have : ¬ s < σ := fun h => hs.2 ⟨hs.1.1, h⟩
      simp [laplacianSlice, this]
  -- Integrating `laplacianSlice` in `σ` gives the increment of the slice.
  have hslice : ∀ᵐ s ∂volume.restrict (Ioo 0 t),
      ∫ σ in Ioo 0 t, laplacianSlice f x s σ = (heatKernel (t - s) ⋆ f s) x - f s x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hfM, hH] with s hs hsM hsH
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      integral_laplacianSlice (hfs s) hsM hsH hα ht.le,
      heatCauchyPotential_eq_convolution _ (sub_pos.2 hs.2),
      heatCauchyPotential_of_nonpos _ (by linarith [hs.1])]
  -- A continuous function essentially bounded by `M` is bounded by `M`.
  have hfx : IntegrableOn (fun s => f s x) (Ioo 0 t) := by
    refine Measure.integrableOn_of_bounded (M := M) measure_Ioo_lt_top.ne
      (hf.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    filter_upwards [hfM, hH] with s hsM hsH
    have hd := (Measure.dense_of_ae hsM).closure_eq
    rw [(isClosed_le (hsH.continuous hα).norm continuous_const).closure_eq] at hd
    exact eq_univ_iff_forall.1 hd x
  have hconv : IntegrableOn (fun s => (heatKernel (t - s) ⋆ f s) x) (Ioo 0 t) :=
    (intervalIntegrable_heatKernel_convolution hf hfM ht x).1.mono_set Ioo_subset_Ioc_self
  have hΔint : IntegrableOn (fun σ => Δ (heatDuhamelPotential f σ) x) (Ioo 0 t) :=
    hG.integral_prod_right.congr <| (ae_restrict_mem measurableSet_Ioo).mono hΔ
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).2 hΔint,
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).2 hfx, ?_⟩
  simp only [heatDuhamelPotential_def, intervalIntegral.integral_of_le ht.le,
    integral_Ioc_eq_integral_Ioo]
  calc ∫ s in Ioo 0 t, (heatKernel (t - s) ⋆ f s) x
      = (∫ s in Ioo 0 t, ((heatKernel (t - s) ⋆ f s) x - f s x)) + ∫ s in Ioo 0 t, f s x := by
        rw [integral_sub hconv hfx, sub_add_cancel]
    _ = (∫ s in Ioo 0 t, ∫ σ in Ioo 0 t, laplacianSlice f x s σ) + ∫ s in Ioo 0 t, f s x := by
        rw [integral_congr_ae hslice]
    _ = (∫ σ in Ioo 0 t, ∫ s in Ioo 0 t, laplacianSlice f x s σ) + ∫ s in Ioo 0 t, f s x := by
        rw [integral_integral_swap hG]
    _ = _ := by rw [setIntegral_congr_fun measurableSet_Ioo hΔ]

/-- **Duhamel's principle in integrated form.** Let `f` be jointly measurable and essentially
bounded on `(0, t) × E`, with `f(s, ·)` `α`-Hölder for almost every `0 < s < t`, where `α > 0`.
Then the Duhamel potential `w` satisfies `w(t, x) = ∫₀ᵗ (Δw(σ, x) + f(σ, x)) dσ`. -/
theorem heatDuhamelPotential_eq_integral (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (ht : 0 ≤ t)
    (x : E) :
    heatDuhamelPotential f t x = ∫ σ in 0..t, (Δ (heatDuhamelPotential f σ) x + f σ x) := by
  obtain ⟨h₁, h₂, h⟩ := heatDuhamelPotential_eq_integral_add_integral hf hfM hH hα ht x
  rw [intervalIntegral.integral_add h₁ h₂, h]

/-- **Time continuity of the Laplacian of the Duhamel potential.** Let `f` be jointly measurable
and essentially bounded on `(0, T) × E`, with `f(s, ·)` `α`-Hölder for almost every `0 < s < T`,
where `0 < α < 2`. Then `σ ↦ Δw(σ, x)` is continuous on `[0, T]`. -/
theorem continuousOn_laplacian_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) (hα₀ : 0 < α) (hα₂ : α < 2)
    (x : E) :
    ContinuousOn (fun σ => Δ (heatDuhamelPotential f σ) x) (Icc 0 T) := by
  obtain ⟨C, hC⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential (E := E) (F := F) hα₀ hα₂
  have h := (hC hf hfM hH x).continuousOn (by positivity)
  simp only [laplacian_eq_traceL_iteratedFDeriv]
  exact (ContinuousLinearMap.continuous _).comp_continuousOn h

/-- **The inhomogeneous heat equation on `[0, T]`.** Let `f` be jointly measurable and
essentially bounded on `(0, T) × E`, with `f(s, ·)` `α`-Hölder for almost every `0 < s < T`,
where `0 < α < 2`. If `t ∈ [0, T]` and `s ↦ f(s, x)` is continuous at `t` within `[0, T]`, then
the Duhamel potential `w` has time derivative `Δw(t, x) + f(t, x)` at `t` within `[0, T]`. -/
theorem hasDerivWithinAt_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) (hα₀ : 0 < α) (hα₂ : α < 2)
    (ht : t ∈ Icc 0 T) {x : E} (hfx : ContinuousWithinAt (fun s => f s x) (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => heatDuhamelPotential f τ x)
      (Δ (heatDuhamelPotential f t) x + f t x) (Icc 0 T) t := by
  have hfM' {τ : ℝ} (hτ : τ ∈ Icc 0 T) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hτ.2) hfM
  have hH' {τ : ℝ} (hτ : τ ∈ Icc 0 T) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hτ.2) hH
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨h₁, h₂, -⟩ := heatDuhamelPotential_eq_integral_add_integral hf hfM hH hα₀ hT x
  have hint := h₁.add h₂
  have hmeas : StronglyMeasurableAtFilter (fun σ => Δ (heatDuhamelPotential f σ) x + f σ x)
      (𝓝[Icc 0 T] t) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hint).aestronglyMeasurable
      self_mem_nhdsWithin
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  refine (intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (hint.mono_set ?_) hmeas
    ((continuousOn_laplacian_heatDuhamelPotential hf hfM hH hα₀ hα₂ x t ht).add hfx)).congr
    (fun τ hτ => heatDuhamelPotential_eq_integral hf (hfM' hτ) (hH' hτ) hα₀ hτ.1 x)
    (heatDuhamelPotential_eq_integral hf (hfM' ht) (hH' ht) hα₀ ht.1 x)
  rw [uIcc_of_le ht.1, uIcc_of_le hT]
  exact Icc_subset_Icc_right ht.2

/-- **The Duhamel potential solves the inhomogeneous heat equation.** Let `f` be jointly
measurable and essentially bounded on `(0, T) × E`, with `f(s, ·)` `α`-Hölder for almost every
`0 < s < T`, where `0 < α < 2`. If `s ↦ f(s, x)` is continuous at `t ∈ (0, T)`, then the Duhamel
potential `w` satisfies `∂ₜw(t, x) = Δw(t, x) + f(t, x)`. -/
theorem hasDerivAt_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) (hα₀ : 0 < α) (hα₂ : α < 2)
    (ht : t ∈ Ioo 0 T) {x : E} (hfx : ContinuousAt (fun s => f s x) t) :
    HasDerivAt (fun τ => heatDuhamelPotential f τ x)
      (Δ (heatDuhamelPotential f t) x + f t x) t :=
  (hasDerivWithinAt_heatDuhamelPotential hf hfM hH hα₀ hα₂ (Ioo_subset_Icc_self ht)
    hfx.continuousWithinAt).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- **The inhomogeneous heat equation on a closed slab.** Let `f` be jointly measurable and
essentially bounded on `(0, T) × E`, and parabolically `α`-Hölder on the slab `E × [0, T]`, where
`0 < α < 2`. Then at every time `t ∈ [0, T]` the Duhamel potential `w` has time derivative
`Δw(t, x) + f(t, x)` within `[0, T]`, one-sided at the endpoints. -/
theorem hasDerivWithinAt_heatDuhamelPotential_of_holderOnWith
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hpar : HolderOnWith H α (fun p : ParabolicSpaceTime E => f p.time p.space)
      (ParabolicSpaceTime.slab 0 T))
    (hα₀ : 0 < α) (hα₂ : α < 2) (ht : t ∈ Icc 0 T) (x : E) :
    HasDerivWithinAt (fun τ => heatDuhamelPotential f τ x)
      (Δ (heatDuhamelPotential f t) x + f t x) (Icc 0 T) t := by
  have hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ParabolicSpaceTime.holderWith_of_holderOnWith_slab hpar ⟨hs.1.le, hs.2.le⟩
  -- The time slice through `x` of the forcing is continuous on `[0, T]`.
  have hc : Continuous fun σ : ℝ => ParabolicSpaceTime.ofCoords x σ :=
    ParabolicSpaceTime.continuous_ofCoords.comp (continuous_const.prodMk continuous_id)
  have hfx := (hpar.continuousOn hα₀).comp hc.continuousOn (s := Icc 0 T) fun σ hσ => by
    simpa using hσ
  simp only [Function.comp_def, ParabolicSpaceTime.time_ofCoords,
    ParabolicSpaceTime.space_ofCoords] at hfx
  exact hasDerivWithinAt_heatDuhamelPotential hf hfM hH hα₀ hα₂ ht (hfx t ht)

end TauCeti
