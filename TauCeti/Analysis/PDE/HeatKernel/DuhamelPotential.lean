/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.HeatEquation
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Duhamel heat potential and its spatial derivatives

For a forcing term `f : ℝ → E → F` on a finite-dimensional real inner product space `E`, the
*Duhamel potential* (or volume potential) is

`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`,

where `K_τ` is the heat kernel. By Duhamel's principle it is the candidate solution of the
inhomogeneous heat equation `∂ₜw = Δw + f` with zero initial datum, complementing the heat
convolution `K_t ⋆ g` of an initial datum `g`. This file proves the spatial regularity of each
time slice `w(t, ·)`, `t > 0`, with bounds whose constants depend only on the dimension (and on
`α` below):

* if `‖f‖ ≤ M` almost everywhere, then `‖w(t, x)‖ ≤ M t`;
* if `f` is moreover jointly measurable, `w(t, ·)` is `C¹`, its derivative is computed under the
  time integral, and `‖D w(t, x)‖ ≤ C M √t`;
* if moreover `f(s, ·)` is `α`-Hölder with constant `H` for almost every `0 < s < t`, and
  `α > 0`, then `w(t, ·)` is `C²`, its second derivative is computed under the time integral, and
  `‖D² w(t, x)‖ ≤ C H t^(α / 2)`.

The time integrand is singular at `s = t`. For the first derivative, the bound
`‖D(K_τ ⋆ g)‖ ≤ ‖DK_τ‖_{L¹} M = O(M τ^(-1/2))` is integrable in `τ`. For the second derivative,
`‖D²K_τ‖_{L¹}` is of order `τ⁻¹`, which is not integrable. Since `∫ D²K_τ = 0`, the value of `g` at
the base point can be subtracted, and Hölder continuity improves the bound to `O(H τ^(α/2 - 1))`
(`TauCeti.norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith`), which is integrable for
`α > 0`. Derivatives are then taken under the time integral with
`TauCeti.iteratedFDeriv_intervalIntegral`. Measurability of the derivatives in the time variable
comes from the parabolic scaling `D^m K_τ(z) = τ^(-(n + m)/2) D^m K_1(τ^(-1/2) z)`.

Without the Hölder condition the second derivative of `w(t, ·)` need not exist, so this is the
form in which `D² w` is controlled by the forcing.

## Main declarations

* `TauCeti.heatDuhamelPotential`: the Duhamel potential `∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`.
* `TauCeti.norm_heatDuhamelPotential_le`: the bound `‖w(t, x)‖ ≤ M t`.
* `TauCeti.intervalIntegrable_heatKernel_convolution`,
  `TauCeti.intervalIntegrable_iteratedFDeriv_heatKernel_convolution`,
  `TauCeti.intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith`: the time
  integrands of the potential and of its spatial derivatives are interval integrable.
* `TauCeti.iteratedFDeriv_heatDuhamelPotential`, `TauCeti.contDiff_heatDuhamelPotential`:
  the first spatial derivative under the time integral, for essentially bounded measurable
  forcing.
* `TauCeti.exists_norm_fderiv_heatDuhamelPotential_le`: the bound `‖D w(t, x)‖ ≤ C M √t`.
* `TauCeti.iteratedFDeriv_heatDuhamelPotential_of_holderWith`,
  `TauCeti.contDiff_heatDuhamelPotential_of_holderWith`: the spatial derivatives up to order two
  under the time integral, for forcing Hölder in space.
* `TauCeti.exists_norm_iteratedFDeriv_two_heatDuhamelPotential_le`: the bound
  `‖D² w(t, x)‖ ≤ C H t^(α / 2)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1 (Duhamel's principle for the
  nonhomogeneous heat equation).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3 (the
  derivatives of the volume potential of a forcing Hölder continuous in space).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap MeasureTheory Module Real Set
open scoped Convolution ContDiff NNReal Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Duhamel

variable {f : ℝ → E → F} {M t : ℝ}

/-- The **Duhamel heat potential** of a forcing `f`,
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`, where `K_τ` is the heat kernel. -/
def heatDuhamelPotential (f : ℝ → E → F) (t : ℝ) (x : E) : F :=
  ∫ s in 0..t, (heatKernel (t - s) ⋆ f s) x

/-- The defining formula of the Duhamel heat potential. -/
theorem heatDuhamelPotential_def (f : ℝ → E → F) (t : ℝ) (x : E) :
    heatDuhamelPotential f t x = ∫ s in 0..t, (heatKernel (t - s) ⋆ f s) x :=
  (rfl)

/-- The Duhamel heat potential vanishes at time zero. -/
@[simp]
theorem heatDuhamelPotential_zero (f : ℝ → E → F) : heatDuhamelPotential f 0 = 0 := by
  funext x
  simp [heatDuhamelPotential_def]

/-- The Duhamel potential at time `t` as a function of space. -/
private theorem heatDuhamelPotential_eq_fun (f : ℝ → E → F) (t : ℝ) :
    heatDuhamelPotential f t = fun x => ∫ s in 0..t, (heatKernel (t - s) ⋆ f s) x :=
  funext (heatDuhamelPotential_def f t)

omit [NormedSpace ℝ F] in
/-- Almost every time `s` in `Ι 0 t` lies in the open interval, where `t - s > 0`, and has an
essentially bounded forcing slice `f(s, ·)`. -/
private theorem ae_mem_Ioo_and_ae_norm_le (ht : 0 ≤ t)
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) :
    ∀ᵐ s ∂volume.restrict (Ι 0 t), s ∈ Ioo 0 t ∧ ∀ᵐ y, ‖f s y‖ ≤ M := by
  rw [uIoc_of_le ht, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hfM] with s hs hsM using ⟨hs, hsM⟩

/-- **The sup bound.** If `‖f(s, y)‖ ≤ M` for almost every `y`, for almost every `0 < s < t`,
then `‖w(t, x)‖ ≤ M t`. -/
theorem norm_heatDuhamelPotential_le (ht : 0 ≤ t)
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (x : E) :
    ‖heatDuhamelPotential f t x‖ ≤ M * t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hae := ae_mem_Ioo_and_ae_norm_le ht.le hfM
  rw [uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc] at hae
  rw [heatDuhamelPotential_def]
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun _ => M) ht.le ?_
    intervalIntegrable_const).trans_eq (by simp [mul_comm])
  filter_upwards [hae] with s hs hsI
  exact norm_heatKernel_convolution_le (sub_pos.2 (hs hsI).1.2) (hs hsI).2 x

/-- For jointly measurable essentially bounded `f`, the spatial derivatives
`D^m (K_{t-s} ⋆ f(s, ·))(x)` are measurable in `s`. Writing `D^m K_{t-s}` through the parabolic
scaling of `K_1` makes the integrand jointly measurable in `(s, z)`. -/
private theorem aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (ht : 0 < t) (m : ℕ) (x : E) :
    AEStronglyMeasurable (fun s => iteratedFDeriv ℝ m (heatKernel (t - s) ⋆ f s) x)
      (volume.restrict (Ι 0 t)) := by
  set Φ : ℝ × E → ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F := fun p =>
    ((t - p.1) ^ (-(finrank ℝ E + m : ℝ) / 2) •
      iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) ((t - p.1) ^ (-1 / 2 : ℝ) • p.2)).smulRight
        (f p.1 (x - p.2))
  have hΦ : StronglyMeasurable Φ := by
    have h₁ : Measurable fun p : ℝ × E => (t - p.1) ^ (-(finrank ℝ E + m : ℝ) / 2) := by
      fun_prop
    have h₂ : Measurable fun p : ℝ × E => (t - p.1) ^ (-1 / 2 : ℝ) • p.2 := by fun_prop
    have h₃ : StronglyMeasurable fun p : ℝ × E => f p.1 (x - p.2) :=
      hf.comp_measurable (g := fun p : ℝ × E => (p.1, x - p.2)) (by fun_prop)
    exact (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F).continuous₂
      |>.comp_stronglyMeasurable ((h₁.stronglyMeasurable.smul
        (((contDiff_heatKernel 1).continuous_iteratedFDeriv le_top).comp_stronglyMeasurable
          h₂.stronglyMeasurable)).prodMk h₃)
  refine (hΦ.integral_prod_right' (ν := volume)).aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM] with s hs
  have hts : 0 < t - s := sub_pos.2 hs.1.2
  have hfs : AEStronglyMeasurable (f s) volume :=
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  rw [iteratedFDeriv_heatKernel_convolution hts hfs hs.2 m x]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Φ, iteratedFDeriv_heatKernel_eq_rpow_smul hts]

/-- The time slices `K_{t-s} ⋆ f(s, ·)` are smooth for almost every `s ∈ Ι 0 t`. -/
private theorem ae_contDiff_heatKernel_convolution (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) (N : ℕ) :
    ∀ᵐ s ∂volume.restrict (Ι 0 t), ContDiff ℝ N (heatKernel (t - s) ⋆ f s) := by
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM] with s hs
  exact (contDiff_heatKernel_convolution (sub_pos.2 hs.1.2)
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    hs.2).of_le (by exact_mod_cast le_top)

/-- The time slices are bounded by the essential bound of `f`. -/
private theorem ae_norm_iteratedFDeriv_heatKernel_convolution_le_zero
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) :
    ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x,
      ‖iteratedFDeriv ℝ 0 (heatKernel (t - s) ⋆ f s) x‖ ≤ M := by
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM] with s hs x
  rw [norm_iteratedFDeriv_zero]
  exact norm_heatKernel_convolution_le (sub_pos.2 hs.1.2) hs.2 x

/-- The first derivatives of the time slices are `O(M (t - s)^(-1/2))`. -/
private theorem exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_one :
    ∃ C, ∀ {f : ℝ → E → F} {M t : ℝ}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) → 0 < t →
      ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x,
        ‖iteratedFDeriv ℝ 1 (heatKernel (t - s) ⋆ f s) x‖ ≤ C * M * (t - s) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := exists_integral_norm_iteratedFDeriv_heatKernel_le (E := E) 1
  refine ⟨C, fun {f M t} hf hfM ht => ?_⟩
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM] with s hs x
  have hts : 0 < t - s := sub_pos.2 hs.1.2
  refine (norm_iteratedFDeriv_heatKernel_convolution_le hts
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    hs.2 1 x).trans ?_
  obtain ⟨y, hy⟩ := hs.2.exists
  have hM : 0 ≤ M := (norm_nonneg _).trans hy
  have := mul_le_mul_of_nonneg_right (hC (t - s) hts) hM
  simp only [Nat.cast_one] at this
  linarith

/-- Integrable bounds on the time slices and their first derivatives. -/
private theorem exists_bounds_one (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) :
    ∃ bound : ℕ → ℝ → ℝ, (∀ k ≤ 1, IntervalIntegrable (bound k) volume 0 t) ∧
      ∀ k ≤ 1, ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x,
        ‖iteratedFDeriv ℝ k (heatKernel (t - s) ⋆ f s) x‖ ≤ bound k s := by
  obtain ⟨C, hC⟩ := exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_one (E := E) (F := F)
  refine ⟨fun k s => if k = 0 then M else C * M * (t - s) ^ (-1 / 2 : ℝ), fun k hk => ?_,
    fun k hk => ?_⟩ <;> interval_cases k
  · simp
  · simpa using (intervalIntegrable_sub_rpow (by norm_num) 0 t).const_mul (C * M)
  · simpa using ae_norm_iteratedFDeriv_heatKernel_convolution_le_zero hfM ht
  · simpa using hC hf hfM ht

/-- For `f` jointly measurable and essentially bounded on `(0, t) × E`, the time integrand
`s ↦ (K_{t-s} ⋆ f(s, ·))(x)` of the Duhamel potential is interval integrable on `[0, t]`. -/
theorem intervalIntegrable_heatKernel_convolution (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) (x : E) :
    IntervalIntegrable (fun s => (heatKernel (t - s) ⋆ f s) x) volume 0 t := by
  refine (intervalIntegrable_const (c := M)).mono_fun' ?_ ?_
  · simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using
      (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht 0 x)
  · filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM] with s hs
    exact norm_heatKernel_convolution_le (sub_pos.2 hs.1.2) hs.2 x

/-- For `f` jointly measurable and essentially bounded on `(0, t) × E`, the time integrands
`s ↦ D^k (K_{t-s} ⋆ f(s, ·))(x)` of the spatial derivatives of order at most one of the Duhamel
potential are interval integrable on `[0, t]`. -/
theorem intervalIntegrable_iteratedFDeriv_heatKernel_convolution
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) {k : ℕ} (hk : k ≤ 1)
    (x : E) :
    IntervalIntegrable (fun s => iteratedFDeriv ℝ k (heatKernel (t - s) ⋆ f s) x) volume 0 t := by
  obtain ⟨bound, hb, hub⟩ := exists_bounds_one hf hfM ht
  exact (hb k hk).mono_fun'
    (aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht k x)
    ((hub k hk).mono fun s hs => hs x)

variable [CompleteSpace F]

/-- For forcing `α`-Hölder in space, the second derivatives of the time slices are
`O(H (t - s)^((α - 2)/2))`. -/
private theorem exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_two {α : ℝ≥0} :
    ∃ C, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x,
        ‖iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s) x‖ ≤
          C * H * (t - s) ^ (((α : ℝ) - 2) / 2) := by
  obtain ⟨C, -, hC⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) 2 α.coe_nonneg
  refine ⟨C, fun {f M t H} hf hfM hH ht => ?_⟩
  have hH' : ∀ᵐ s ∂volume.restrict (Ι 0 t), HolderWith H α (f s) := by
    rwa [uIoc_of_le ht.le, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM, hH'] with s hs hsH x
  have hts : 0 < t - s := sub_pos.2 hs.1.2
  refine (norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith hts
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    hs.2 hsH two_ne_zero x).trans ?_
  have := mul_le_mul_of_nonneg_left (hC (t - s) hts) H.coe_nonneg
  simp only [Nat.cast_ofNat] at this
  linarith

/-- Integrable bounds on the time slices and their derivatives up to order two, for forcing
`α`-Hölder in space with `α > 0`. -/
private theorem exists_bounds_two (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) {H α : ℝ≥0}
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α) (ht : 0 < t) :
    ∃ bound : ℕ → ℝ → ℝ, (∀ k ≤ 2, IntervalIntegrable (bound k) volume 0 t) ∧
      ∀ k ≤ 2, ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x,
        ‖iteratedFDeriv ℝ k (heatKernel (t - s) ⋆ f s) x‖ ≤ bound k s := by
  obtain ⟨C₁, hC₁⟩ := exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_one (E := E) (F := F)
  obtain ⟨C₂, hC₂⟩ :=
    exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_two (E := E) (F := F) (α := α)
  refine ⟨fun k s => if k = 0 then M else if k = 1 then C₁ * M * (t - s) ^ (-1 / 2 : ℝ)
    else C₂ * H * (t - s) ^ (((α : ℝ) - 2) / 2), fun k hk => ?_, fun k hk => ?_⟩ <;>
    interval_cases k
  · simp
  · simpa using (intervalIntegrable_sub_rpow (by norm_num) 0 t).const_mul (C₁ * M)
  · have hα' : (0 : ℝ) < α := hα
    simpa using (intervalIntegrable_sub_rpow (by linarith) 0 t).const_mul (C₂ * H)
  · simpa using ae_norm_iteratedFDeriv_heatKernel_convolution_le_zero hfM ht
  · simpa using hC₁ hf hfM ht
  · simpa using hC₂ hf hfM hH ht

/-- If `f` is jointly measurable and essentially bounded on `(0, t) × E`, and `f(s, ·)` is
`α`-Hölder for almost every `0 < s < t`, with `α > 0`, then the time integrands
`s ↦ D^k (K_{t-s} ⋆ f(s, ·))(x)` of the spatial derivatives of order at most two of the Duhamel
potential are interval integrable on `[0, t]`. -/
theorem intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    {H α : ℝ≥0} (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α)
    (ht : 0 < t) {k : ℕ} (hk : k ≤ 2) (x : E) :
    IntervalIntegrable (fun s => iteratedFDeriv ℝ k (heatKernel (t - s) ⋆ f s) x) volume 0 t := by
  obtain ⟨bound, hb, hub⟩ := exists_bounds_two hf hfM hH hα ht
  exact (hb k hk).mono_fun'
    (aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht k x)
    ((hub k hk).mono fun s hs => hs x)

/-- **The first derivative of the Duhamel potential.** For `f` jointly measurable and essentially
bounded on `(0, t) × E`, the derivatives of `w(t, ·)` of order at most one are computed under
the time integral: `D^k w(t, x) = ∫₀ᵗ D^k (K_{t-s} ⋆ f(s, ·))(x) ds`. -/
theorem iteratedFDeriv_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) {k : ℕ} (hk : k ≤ 1) :
    iteratedFDeriv ℝ k (heatDuhamelPotential f t) =
      fun x => ∫ s in 0..t, iteratedFDeriv ℝ k (heatKernel (t - s) ⋆ f s) x := by
  obtain ⟨bound, hb, hub⟩ := exists_bounds_one hf hfM ht
  rw [heatDuhamelPotential_eq_fun]
  exact iteratedFDeriv_intervalIntegral (ae_contDiff_heatKernel_convolution hf hfM ht 1)
    (fun k _ => aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht k) hb hub hk

/-- For `f` jointly measurable and essentially bounded on `(0, t) × E`, the Duhamel potential
`w(t, ·)` is `C¹`. -/
theorem contDiff_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) (ht : 0 < t) :
    ContDiff ℝ 1 (heatDuhamelPotential f t) := by
  obtain ⟨bound, hb, hub⟩ := exists_bounds_one hf hfM ht
  rw [heatDuhamelPotential_eq_fun]
  exact contDiff_intervalIntegral (ae_contDiff_heatKernel_convolution hf hfM ht 1)
    (fun k _ => aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht k) hb hub

/-- **The second derivative of the Duhamel potential.** If `f` is jointly measurable and
essentially bounded on `(0, t) × E`, and `f(s, ·)` is `α`-Hölder with constant `H` for almost
every `0 < s < t`, with `α > 0`, then the derivatives of `w(t, ·)` of order at most two are
computed under the time integral: `D^k w(t, x) = ∫₀ᵗ D^k (K_{t-s} ⋆ f(s, ·))(x) ds`. -/
theorem iteratedFDeriv_heatDuhamelPotential_of_holderWith
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    {H α : ℝ≥0} (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α)
    (ht : 0 < t) {k : ℕ} (hk : k ≤ 2) :
    iteratedFDeriv ℝ k (heatDuhamelPotential f t) =
      fun x => ∫ s in 0..t, iteratedFDeriv ℝ k (heatKernel (t - s) ⋆ f s) x := by
  obtain ⟨bound, hb, hub⟩ := exists_bounds_two hf hfM hH hα ht
  rw [heatDuhamelPotential_eq_fun]
  exact iteratedFDeriv_intervalIntegral (ae_contDiff_heatKernel_convolution hf hfM ht 2)
    (fun k _ => aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht k) hb hub hk

/-- If `f` is jointly measurable and essentially bounded on `(0, t) × E`, and `f(s, ·)` is
`α`-Hölder for almost every `0 < s < t`, with `α > 0`, then the Duhamel potential `w(t, ·)` is
`C²`. -/
theorem contDiff_heatDuhamelPotential_of_holderWith
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    {H α : ℝ≥0} (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) (hα : 0 < α)
    (ht : 0 < t) :
    ContDiff ℝ 2 (heatDuhamelPotential f t) := by
  obtain ⟨bound, hb, hub⟩ := exists_bounds_two hf hfM hH hα ht
  rw [heatDuhamelPotential_eq_fun]
  exact contDiff_intervalIntegral (ae_contDiff_heatKernel_convolution hf hfM ht 2)
    (fun k _ => aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution hf hfM ht k) hb hub

/-- **The gradient bound for the Duhamel potential.** There is a constant `C`, depending only on
the dimension, such that `‖D w(t, x)‖ ≤ C M √t` whenever `f` is jointly measurable and
`‖f(s, y)‖ ≤ M` for almost every `y`, for almost every `0 < s < t`. -/
theorem exists_norm_fderiv_heatDuhamelPotential_le :
    ∃ C, ∀ {f : ℝ → E → F} {M t : ℝ}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) → 0 < t → ∀ x,
        ‖fderiv ℝ (heatDuhamelPotential f t) x‖ ≤ C * M * √t := by
  obtain ⟨C, hC⟩ := exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_one (E := E) (F := F)
  refine ⟨2 * C, fun {f M t} hf hfM ht x => ?_⟩
  have hae := hC hf hfM ht
  rw [uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc] at hae
  rw [← norm_iteratedFDeriv_one, iteratedFDeriv_heatDuhamelPotential hf hfM ht le_rfl]
  refine (intervalIntegral.norm_integral_le_of_norm_le ht.le (hae.mono fun s hs hsI => hs hsI x)
    ((intervalIntegrable_sub_rpow (by norm_num) 0 t).const_mul (C * M))).trans_eq ?_
  rw [intervalIntegral.integral_const_mul, integral_sub_rpow (by norm_num), sqrt_eq_rpow]
  norm_num
  ring

/-- **The Hessian bound for the Duhamel potential.** For `α > 0` there is a constant `C`,
depending only on `α` and the dimension, such that `‖D² w(t, x)‖ ≤ C H t^(α / 2)` whenever `f` is
jointly measurable and essentially bounded on `(0, t) × E` and `f(s, ·)` is `α`-Hölder with
constant `H` for almost every `0 < s < t`. The bound on `f` does not enter the estimate. -/
theorem exists_norm_iteratedFDeriv_two_heatDuhamelPotential_le {α : ℝ≥0} (hα : 0 < α) :
    ∃ C, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      ∀ x, ‖iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x‖ ≤ C * H * t ^ ((α : ℝ) / 2) := by
  obtain ⟨C, hC⟩ :=
    exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le_two (E := E) (F := F) (α := α)
  have hα' : (0 : ℝ) < α := hα
  refine ⟨2 / α * C, fun {f M t H} hf hfM hH ht x => ?_⟩
  have hae := hC hf hfM hH ht
  rw [uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc] at hae
  rw [iteratedFDeriv_heatDuhamelPotential_of_holderWith hf hfM hH hα ht le_rfl]
  refine (intervalIntegral.norm_integral_le_of_norm_le ht.le (hae.mono fun s hs hsI => hs hsI x)
    ((intervalIntegrable_sub_rpow (by linarith) 0 t).const_mul (C * H))).trans_eq ?_
  rw [intervalIntegral.integral_const_mul, integral_sub_rpow (by linarith), sub_zero]
  have h : ((α : ℝ) - 2) / 2 + 1 = α / 2 := by ring
  rw [h]
  field_simp

end Duhamel

end TauCeti
