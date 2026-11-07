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
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Duhamel heat potential, its spatial derivatives and the Hölder estimates of its Hessian

For a forcing term `f : ℝ → E → F` on a finite-dimensional real inner product space `E`, the
*Duhamel potential* (or volume potential) is

`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`,

where `K_τ` is the heat kernel. By Duhamel's principle it is the candidate solution of the
inhomogeneous heat equation `∂ₜw = Δw + f` with zero initial datum, complementing the heat
convolution `K_t ⋆ g` of an initial datum `g`. This file proves the spatial regularity of each
time slice `w(t, ·)`, `t > 0`, and the temporal regularity of its Hessian, with bounds whose
constants depend only on the dimension (and on `α` below):

* if `‖f‖ ≤ M` almost everywhere, then `‖w(t, x)‖ ≤ M t`;
* if `f` is moreover jointly measurable, `w(t, ·)` is `C¹`, its derivative is computed under the
  time integral, and `‖D w(t, x)‖ ≤ C M √t`;
* if moreover `f(s, ·)` is `α`-Hölder with constant `H` for almost every `0 < s < t`, and
  `α > 0`, then `w(t, ·)` is `C²`, its second derivative is computed under the time integral, and
  `‖D² w(t, x)‖ ≤ C H t^(α / 2)`;
* if moreover `α < 1`, then `D² w(t, ·)` is `α`-Hölder with constant `C H`, independently of `t`;
* if instead `α < 2`, then at each point `x` the Hessian `t ↦ D² w(t, ·)(x)` is `α/2`-Hölder in
  time on `[0, T]` with constant `C H`, independently of `T`.

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

For the Hölder estimate of `D² w(t, ·)` at two points at distance `δ`, the times `t - δ² < s < t`
are handled by the bound above, which integrates to `O(H δ^α)`. For `s < t - δ²` the mean value
theorem and the bound `‖D³(K_τ ⋆ g)‖ = O(H τ^((α - 3)/2))`, obtained by the same cancellation,
give a contribution `O(H δ ∫_{δ²}^∞ τ^((α - 3)/2) dτ) = O(H δ^α)`, which requires `α < 1`. This is
the spatial half of the order-two parabolic Hölder estimate of the Duhamel potential.

The temporal half compares `D² w` at times `t' < t`, with `h = t - t'`. If `t' ≤ h`, both
Hessians are `O(H h^(α/2))` by the bound above. Otherwise the times `s > t' - h` contribute
`O(H h^(α/2))` by the same bound, while for `s < t' - h` the slices at elapsed times `t' - s` and
`t - s` differ by `O(H h (t' - s)^((α - 4)/2))`
(`TauCeti.norm_iteratedFDeriv_heatKernel_convolution_sub_le_of_holderWith`, one time derivative of
the kernel at the cost of a factor `(t' - s)⁻¹`), which integrates to `O(H h^(α/2))` when
`α < 2`. For `0 < α < 1`, the two halves together give the parabolic `α`-Hölder estimate of
`D² w`.

## Main declarations

* `TauCeti.heatDuhamelPotential`: the Duhamel potential `∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`.
* `TauCeti.norm_heatDuhamelPotential_le`: the bound `‖w(t, x)‖ ≤ M t`.
* `TauCeti.exists_stronglyMeasurable_eq_iteratedFDeriv_heatKernel_convolution`: the derivatives
  `D^m (K_τ ⋆ f(s, ·))(x)` agree with a jointly measurable function of `(s, τ)`.
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
* `TauCeti.exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential`: for `0 < α < 1`,
  `D² w(t, ·)` is `α`-Hölder with constant `C H`.
* `TauCeti.exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential`: for `0 < α < 2`,
  `t ↦ D² w(t, ·)(x)` is `α/2`-Hölder on `[0, T]` with constant `C H`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1 (Duhamel's principle for the
  nonhomogeneous heat equation).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3 (the
  derivatives of the volume potential of a forcing Hölder continuous in space).
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (Hölder estimates for the heat equation).
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

/-- The Duhamel heat potential commutes with scalar multiplication, at every time. -/
theorem heatDuhamelPotential_smul (c : ℝ) (f : ℝ → E → F) (t : ℝ) (x : E) :
    heatDuhamelPotential (c • f) t x = c • heatDuhamelPotential f t x := by
  simp only [heatDuhamelPotential_def, Pi.smul_apply, convolution_smul]
  exact intervalIntegral.integral_smul c _

/-- The Duhamel heat potential vanishes at time zero. -/
@[simp]
theorem heatDuhamelPotential_zero (f : ℝ → E → F) : heatDuhamelPotential f 0 = 0 := by
  funext x
  simp [heatDuhamelPotential_def]

/-- Constant forcing produces linear growth in time. -/
@[simp]
theorem heatDuhamelPotential_const [CompleteSpace F] (c : F) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    heatDuhamelPotential (fun _ _ => c) t x = t • c := by
  rw [heatDuhamelPotential_def]
  calc (∫ s in 0..t, (heatKernel (t - s) ⋆ fun _ : E => c) x) = ∫ _ in 0..t, c := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le ht, ← restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        rw [convolution_def]
        simp only [ContinuousLinearMap.lsmul_apply]
        rw [integral_smul_const, integral_heatKernel (sub_pos.2 hs.2), one_smul]
    _ = t • c := by simp

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

/-- **Joint measurability of the derivatives of heat convolutions.** For jointly measurable `f`,
some jointly strongly measurable function of `(s, τ)` equals `D^m (K_τ ⋆ f(s, ·))(x)` whenever
`τ > 0` and `f(s, ·)` is essentially bounded. Writing `D^m K_τ` through the parabolic scaling of
`K_1` makes the convolution integrand jointly measurable in `(s, τ, z)`. -/
theorem exists_stronglyMeasurable_eq_iteratedFDeriv_heatKernel_convolution
    (hf : StronglyMeasurable (Function.uncurry f)) (m : ℕ) (x : E) :
    ∃ Φ : ℝ × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F, StronglyMeasurable Φ ∧
      ∀ s τ (B : ℝ), 0 < τ → (∀ᵐ y, ‖f s y‖ ≤ B) →
        Φ (s, τ) = iteratedFDeriv ℝ m (heatKernel τ ⋆ f s) x := by
  set Ψ : (ℝ × ℝ) × E → ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F := fun p =>
    (p.1.2 ^ (-(finrank ℝ E + m : ℝ) / 2) •
      iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) (p.1.2 ^ (-1 / 2 : ℝ) • p.2)).smulRight
        (f p.1.1 (x - p.2))
  have hΨ : StronglyMeasurable Ψ := by
    have h₁ : Measurable fun p : (ℝ × ℝ) × E => p.1.2 ^ (-(finrank ℝ E + m : ℝ) / 2) := by
      fun_prop
    have h₂ : Measurable fun p : (ℝ × ℝ) × E => p.1.2 ^ (-1 / 2 : ℝ) • p.2 := by fun_prop
    have h₃ : StronglyMeasurable fun p : (ℝ × ℝ) × E => f p.1.1 (x - p.2) :=
      hf.comp_measurable (g := fun p : (ℝ × ℝ) × E => (p.1.1, x - p.2)) (by fun_prop)
    exact (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F).continuous₂
      |>.comp_stronglyMeasurable ((h₁.stronglyMeasurable.smul
        (((contDiff_heatKernel 1).continuous_iteratedFDeriv le_top).comp_stronglyMeasurable
          h₂.stronglyMeasurable)).prodMk h₃)
  refine ⟨fun q => ∫ z, Ψ (q, z), hΨ.integral_prod_right', fun s τ B hτ hB => ?_⟩
  rw [iteratedFDeriv_heatKernel_convolution (g := f s) hτ
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable hB m x]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Ψ, iteratedFDeriv_heatKernel_eq_rpow_smul hτ]

/-- For jointly measurable essentially bounded `f`, the spatial derivatives
`D^m (K_{t-s} ⋆ f(s, ·))(x)` are measurable in `s`. -/
private theorem aestronglyMeasurable_iteratedFDeriv_heatKernel_convolution
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (ht : 0 < t) (m : ℕ) (x : E) :
    AEStronglyMeasurable (fun s => iteratedFDeriv ℝ m (heatKernel (t - s) ⋆ f s) x)
      (volume.restrict (Ι 0 t)) := by
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_stronglyMeasurable_eq_iteratedFDeriv_heatKernel_convolution hf m x
  refine (hΦ.comp_measurable (by fun_prop : Measurable fun s : ℝ => (s, t - s))
    ).aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM] with s hs
  exact hΦeq s (t - s) M (sub_pos.2 hs.1.2) hs.2

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

/-- The Duhamel heat potential is additive for jointly measurable, essentially bounded
forcing on the integration interval. No spatial continuity is required. -/
theorem heatDuhamelPotential_add {g : ℝ → E → F} {N : ℝ}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hg : StronglyMeasurable (Function.uncurry g))
    (hgN : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖g s y‖ ≤ N)
    (ht : 0 ≤ t) (x : E) :
    heatDuhamelPotential (f + g) t x =
      heatDuhamelPotential f t x + heatDuhamelPotential g t x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [heatDuhamelPotential_def, heatDuhamelPotential_def, heatDuhamelPotential_def,
    ← intervalIntegral.integral_add (intervalIntegrable_heatKernel_convolution hf hfM ht x)
      (intervalIntegrable_heatKernel_convolution hg hgN ht x)]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM,
    ae_mem_Ioo_and_ae_norm_le ht.le hgN] with s hs hs'
  exact (convolutionExists_of_integrable_of_ae_norm_le _
    (integrable_heatKernel (sub_pos.2 hs.1.2))
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable hs.2 x).distrib_add
      (convolutionExists_of_integrable_of_ae_norm_le _
        (integrable_heatKernel (sub_pos.2 hs'.1.2))
        (hg.comp_measurable measurable_prodMk_left).aestronglyMeasurable hs'.2 x)

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

/-- For forcing `α`-Hölder in space, the derivatives of order `m ≥ 1` of the time slices are
`O(H (t - s)^((α - m)/2))`. -/
private theorem exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le {α : ℝ≥0} {m : ℕ}
    (hm : m ≠ 0) :
    ∃ C ≥ 0, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x,
        ‖iteratedFDeriv ℝ m (heatKernel (t - s) ⋆ f s) x‖ ≤
          C * H * (t - s) ^ (((α : ℝ) - m) / 2) := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) m α.coe_nonneg
  refine ⟨C, hC₀.le, fun {f M t H} hf hfM hH ht => ?_⟩
  have hH' : ∀ᵐ s ∂volume.restrict (Ι 0 t), HolderWith H α (f s) := by
    rwa [uIoc_of_le ht.le, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_mem_Ioo_and_ae_norm_le ht.le hfM, hH'] with s hs hsH x
  have hts : 0 < t - s := sub_pos.2 hs.1.2
  refine (norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith hts
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    hs.2 hsH hm x).trans ?_
  have := mul_le_mul_of_nonneg_left (hC (t - s) hts) H.coe_nonneg
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
  obtain ⟨C₂, -, hC₂⟩ :=
    exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le (E := E) (F := F) (α := α)
      two_ne_zero
  simp only [Nat.cast_ofNat] at hC₂
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
  rw [uIoc_of_le ht.le] at hae
  rw [← norm_iteratedFDeriv_one, iteratedFDeriv_heatDuhamelPotential hf hfM ht le_rfl]
  refine (intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_left (K := C * M)
    (by norm_num) ht.le (hae.mono fun s hs => hs x)).trans_eq ?_
  rw [sqrt_eq_rpow]
  norm_num
  ring

/-- Near the singular endpoint, the time integral over `[a, t]` of the Hessians of the slices is
`O(H (t - a)^(α/2))`. -/
private theorem exists_norm_integral_iteratedFDeriv_two_heatKernel_convolution_le {α : ℝ≥0}
    (hα : 0 < α) :
    ∃ C ≥ 0, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → ∀ a, 0 ≤ a → a ≤ t → ∀ x,
        ‖∫ s in a..t, iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s) x‖ ≤
          C * H * (t - a) ^ ((α : ℝ) / 2) := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le (E := E) (F := F) (α := α)
      two_ne_zero
  simp only [Nat.cast_ofNat] at hC
  have hα' : (0 : ℝ) < α := hα
  refine ⟨2 / α * C, by positivity, fun {f M t H} hf hfM hH a ha hat x => ?_⟩
  rcases hat.eq_or_lt with rfl | hat
  · rw [intervalIntegral.integral_same, norm_zero]
    positivity
  have ht : 0 < t := ha.trans_lt hat
  have hae := hC hf hfM hH ht
  rw [uIoc_of_le ht.le] at hae
  refine (intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_left (K := C * H)
    (by linarith) hat.le (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc ha le_rfl)
      (hae.mono fun s hs => hs x))).trans_eq ?_
  have h : ((α : ℝ) - 2) / 2 + 1 = α / 2 := by ring
  rw [h]
  field_simp

/-- **The Hessian bound for the Duhamel potential.** For `α > 0` there is a constant `C`,
depending only on `α` and the dimension, such that `‖D² w(t, x)‖ ≤ C H t^(α / 2)` whenever `f` is
jointly measurable and essentially bounded on `(0, t) × E` and `f(s, ·)` is `α`-Hölder with
constant `H` for almost every `0 < s < t`. The bound on `f` does not enter the estimate. -/
theorem exists_norm_iteratedFDeriv_two_heatDuhamelPotential_le {α : ℝ≥0} (hα : 0 < α) :
    ∃ C, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      ∀ x, ‖iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x‖ ≤ C * H * t ^ ((α : ℝ) / 2) := by
  obtain ⟨C, -, hC⟩ :=
    exists_norm_integral_iteratedFDeriv_two_heatKernel_convolution_le (E := E) (F := F) hα
  refine ⟨C, fun {f M t H} hf hfM hH ht x => ?_⟩
  rw [iteratedFDeriv_heatDuhamelPotential_of_holderWith hf hfM hH hα ht le_rfl]
  simpa using hC hf hfM hH 0 le_rfl ht.le x

/-! ### The Hölder estimate of the Hessian -/

/-- For forcing `α`-Hölder in space, the Hessians of the time slices are Lipschitz in space with
constant `O(H (t - s)^((α - 3)/2))`. -/
private theorem exists_ae_norm_iteratedFDeriv_two_heatKernel_convolution_sub_le {α : ℝ≥0} :
    ∃ C ≥ 0, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ x y,
        ‖iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s) x -
            iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s) y‖ ≤
          C * H * (t - s) ^ (((α : ℝ) - 3) / 2) * ‖x - y‖ := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le (E := E) (F := F) (α := α)
      (m := 3) three_ne_zero
  refine ⟨C, hC₀, fun {f M t H} hf hfM hH ht => ?_⟩
  filter_upwards [hC hf hfM hH ht, ae_contDiff_heatKernel_convolution hf hfM ht 3]
    with s hs hsd x y
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s)) :=
    hsd.differentiable_iteratedFDeriv (by norm_num)
  refine convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z) (fun z _ => ?_)
    (mem_univ y) (mem_univ x)
  have := hs z
  rw [Nat.cast_ofNat] at this
  rwa [norm_fderiv_iteratedFDeriv]

/-- **The Hölder estimate for the Hessian of the Duhamel potential.** For `0 < α < 1` there is a
constant `C`, depending only on `α` and the dimension, such that the Hessian `D² w(t, ·)` is
`α`-Hölder with constant `C H` whenever `f` is jointly measurable and essentially bounded on
`(0, t) × E` and `f(s, ·)` is `α`-Hölder with constant `H` for almost every `0 < s < t`. Neither
the bound on `f` nor the time `t` enters the estimate. -/
theorem exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential {α : ℝ≥0} (hα₀ : 0 < α)
    (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      HolderWith (C * H) α (iteratedFDeriv ℝ 2 (heatDuhamelPotential f t)) := by
  obtain ⟨C₂, hC₂₀, hC₂⟩ :=
    exists_ae_norm_iteratedFDeriv_heatKernel_convolution_le (E := E) (F := F) (α := α)
      two_ne_zero
  simp only [Nat.cast_ofNat] at hC₂
  obtain ⟨C₃, hC₃₀, hC₃⟩ :=
    exists_ae_norm_iteratedFDeriv_two_heatKernel_convolution_sub_le (E := E) (F := F) (α := α)
  have hα₀' : (0 : ℝ) < α := hα₀
  have hα₁' : (α : ℝ) < 1 := hα₁
  have h1α : (0 : ℝ) < 1 - α := by linarith
  refine ⟨(2 / α * (2 * C₂) + 2 / (1 - α) * C₃).toNNReal, fun {f M t H} hf hfM hH ht => ?_⟩
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ => ?_
  rcases eq_or_ne x y with rfl | hxy
  · rw [dist_self, dist_self, zero_rpow hα₀'.ne']
    simp
  have hint : ∀ z, IntervalIntegrable
      (fun s => iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s) z) volume 0 t := fun z =>
    intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith hf hfM hH hα₀ ht
      le_rfl z
  have hae₂ := hC₂ hf hfM hH ht
  have hae₃ := hC₃ hf hfM hH ht
  rw [uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc] at hae₂ hae₃
  rw [dist_eq_norm, iteratedFDeriv_heatDuhamelPotential_of_holderWith hf hfM hH hα₀ ht le_rfl,
    ← intervalIntegral.integral_sub (hint x) (hint y), dist_eq_norm]
  refine (norm_integral_le_of_ae_norm_le_rpow (A := 2 * C₂ * H) (B := C₃ * H) hα₀' hα₁' ht
    (norm_pos_iff.2 (sub_ne_zero.2 hxy)) (by positivity) (by positivity) ((hint x).sub (hint y))
    ?_ ?_).trans_eq ?_
  · filter_upwards [hae₂] with s hs hsI
    refine (norm_sub_le _ _).trans ?_
    linarith [hs hsI x, hs hsI y]
  · filter_upwards [hae₃] with s hs hsI using hs hsI x y
  · rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    ring

/-! ### The temporal Hölder estimate of the Hessian -/

/-- Away from the diagonal, the Hessians of the slices at the times `t' < t` differ by
`O(H (t - t') (t' - s)^((α - 4)/2))`, at almost every `0 < s ≤ t' - (t - t')`. -/
private theorem exists_ae_norm_iteratedFDeriv_two_heatKernel_convolution_sub_time_le {α : ℝ≥0} :
    ∃ C ≥ 0, ∀ {f : ℝ → E → F} {M t t' : ℝ} {H : ℝ≥0},
      StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → t' < t →
      ∀ᵐ s, s ∈ Ioc 0 (t' - (t - t')) → ∀ x,
        ‖iteratedFDeriv ℝ 2 (heatKernel (t - s) ⋆ f s) x -
            iteratedFDeriv ℝ 2 (heatKernel (t' - s) ⋆ f s) x‖ ≤
          C * H * (t - t') * (t' - s) ^ (((α : ℝ) - 4) / 2) := by
  obtain ⟨K, hK₀, hK⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_sub_mul_rpow_le (E := E) 2 α.coe_nonneg
  refine ⟨K, hK₀.le, fun {f M t t' H} hf hfM hH htt' => ?_⟩
  have hae : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∀ᵐ y, ‖f s y‖ ≤ M) ∧ HolderWith H α (f s) := by
    filter_upwards [hfM, hH] with s hsM hsH using ⟨hsM, hsH⟩
  rw [ae_restrict_iff' measurableSet_Ioo] at hae
  filter_upwards [hae] with s hs hsI x
  obtain ⟨hsM, hsH⟩ := hs ⟨hsI.1, by linarith [hsI.2]⟩
  have ha : 0 < t' - s := by linarith [hsI.2]
  refine (norm_iteratedFDeriv_heatKernel_convolution_sub_le_of_holderWith ha (by linarith)
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable hsM hsH two_ne_zero
    x).trans ?_
  have := mul_le_mul_of_nonneg_left
    (hK (t' - s) (t - s) ha (by linarith) (by linarith [hsI.2])) H.coe_nonneg
  have hexp : ((α : ℝ) - (2 : ℕ) - 2) / 2 = ((α : ℝ) - 4) / 2 := by
    push_cast
    ring
  rw [hexp, show t - s - (t' - s) = t - t' by ring] at this
  linarith

/-- The temporal increment of the Hessian of the Duhamel potential between times `t' ≤ t` is
`O(H (t - t')^(α/2))`, for `0 < α < 2`. -/
private theorem exists_norm_iteratedFDeriv_two_heatDuhamelPotential_sub_le {α : ℝ≥0}
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    ∃ C ≥ 0, ∀ {f : ℝ → E → F} {M t t' : ℝ} {H : ℝ≥0},
      StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 ≤ t' → t' ≤ t → ∀ x,
        ‖iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x -
            iteratedFDeriv ℝ 2 (heatDuhamelPotential f t') x‖ ≤
          C * H * (t - t') ^ ((α : ℝ) / 2) := by
  obtain ⟨C₁, hC₁₀, hC₁⟩ :=
    exists_norm_integral_iteratedFDeriv_two_heatKernel_convolution_le (E := E) (F := F) hα₀
  obtain ⟨K, hK₀, hK⟩ :=
    exists_ae_norm_iteratedFDeriv_two_heatKernel_convolution_sub_time_le (E := E) (F := F) (α := α)
  have hα₀' : (0 : ℝ) < α := hα₀
  have hα₂' : (α : ℝ) < 2 := hα₂
  have h2α : (0 : ℝ) < 2 - α := by linarith
  refine ⟨3 * C₁ + 2 / (2 - α) * K, by positivity,
    fun {f M t t' H} hf hfM hH ht' htt' x => ?_⟩
  rcases htt'.eq_or_lt with rfl | htt'
  · rw [sub_self, norm_zero]
    positivity
  have ht : 0 < t := ht'.trans_lt htt'
  set h := t - t' with hh_def
  have hh : 0 < h := sub_pos.2 htt'
  set Φ : ℝ → ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F :=
    fun τ s => iteratedFDeriv ℝ 2 (heatKernel (τ - s) ⋆ f s) x with hΦ_def
  have hfM' {τ : ℝ} (hτ : τ ≤ t) : ∀ᵐ s ∂volume.restrict (Ioo 0 τ), ∀ᵐ y, ‖f s y‖ ≤ M :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hτ) hfM
  have hH' {τ : ℝ} (hτ : τ ≤ t) : ∀ᵐ s ∂volume.restrict (Ioo 0 τ), HolderWith H α (f s) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hτ) hH
  -- At every time `τ ∈ [0, t]` the Hessian is the time integral of the Hessians of the slices.
  have hrep {τ : ℝ} (hτ : 0 ≤ τ) (hτt : τ ≤ t) :
      iteratedFDeriv ℝ 2 (heatDuhamelPotential f τ) x = ∫ s in 0..τ, Φ τ s := by
    rcases hτ.eq_or_lt with rfl | hτ
    · simp [iteratedFDeriv_zero]
    exact congrFun (iteratedFDeriv_heatDuhamelPotential_of_holderWith hf (hfM' hτt) (hH' hτt)
      hα₀ hτ le_rfl) x
  have hnear {τ a : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) (hτt : τ ≤ t) :
      ‖∫ s in a..τ, Φ τ s‖ ≤ C₁ * H * (τ - a) ^ ((α : ℝ) / 2) :=
    hC₁ hf (hfM' hτt) (hH' hτt) a ha haτ x
  -- Times up to `2h` contribute at most twice `h^(α/2)`, since `α/2 ≤ 1`.
  have hpow {r : ℝ} (hr : 0 ≤ r) (hrh : r ≤ 2 * h) :
      r ^ ((α : ℝ) / 2) ≤ 2 * h ^ ((α : ℝ) / 2) :=
    rpow_le_two_mul_rpow_of_le_two_mul hr hrh (by positivity) (by linarith)
  have hfinal : 3 * C₁ * H * h ^ ((α : ℝ) / 2) + 2 / (2 - α) * K * H * h ^ ((α : ℝ) / 2) =
      (3 * C₁ + 2 / (2 - α) * K) * H * h ^ ((α : ℝ) / 2) := by ring
  rw [hrep (ht'.trans htt'.le) le_rfl, hrep ht' htt'.le]
  rcases le_or_gt t' h with hsmall | hbig
  · -- For `t' ≤ h` both Hessians are already of size `O(H h^(α/2))`.
    calc ‖(∫ s in 0..t, Φ t s) - ∫ s in 0..t', Φ t' s‖
        ≤ ‖∫ s in 0..t, Φ t s‖ + ‖∫ s in 0..t', Φ t' s‖ := norm_sub_le _ _
      _ ≤ C₁ * H * (t - 0) ^ ((α : ℝ) / 2) + C₁ * H * (t' - 0) ^ ((α : ℝ) / 2) :=
          add_le_add (hnear le_rfl ht.le le_rfl) (hnear le_rfl ht' htt'.le)
      _ ≤ C₁ * H * (2 * h ^ ((α : ℝ) / 2)) + C₁ * H * h ^ ((α : ℝ) / 2) := by
          gcongr
          · exact hpow (by linarith) (by linarith)
          · linarith
      _ ≤ (3 * C₁ + 2 / (2 - α) * K) * H * h ^ ((α : ℝ) / 2) := by
          rw [← hfinal]
          have : 0 ≤ 2 / (2 - α) * K * H * h ^ ((α : ℝ) / 2) := by positivity
          linarith
  -- Otherwise split both integrals at `s₀ = t' - h`.
  set s₀ := t' - h with hs₀_def
  have hs₀ : 0 < s₀ := by linarith
  have hint {τ : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) : IntervalIntegrable (Φ τ) volume 0 τ :=
    intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith hf (hfM' hτt)
      (hH' hτt) hα₀ hτ le_rfl x
  have hmem {τ : ℝ} (hτ : s₀ ≤ τ) : s₀ ∈ [[0, τ]] := by
    rw [uIcc_of_le (hs₀.le.trans hτ)]
    exact ⟨hs₀.le, hτ⟩
  have hint₀ {τ : ℝ} (hτ : s₀ ≤ τ) (hτt : τ ≤ t) : IntervalIntegrable (Φ τ) volume 0 s₀ :=
    (hint (hs₀.trans_le hτ) hτt).mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem hτ))
  have hsplit {τ : ℝ} (hτ : s₀ ≤ τ) (hτt : τ ≤ t) :
      ∫ s in 0..τ, Φ τ s = (∫ s in 0..s₀, Φ τ s) + ∫ s in s₀..τ, Φ τ s :=
    (intervalIntegral.integral_add_adjacent_intervals (hint₀ hτ hτt)
      ((hint (hs₀.trans_le hτ) hτt).mono_set (uIcc_subset_uIcc (hmem hτ) right_mem_uIcc))).symm
  -- Away from the diagonal, the time Lipschitz bound integrates to `O(H h^(α/2))`.
  have hfar : ‖∫ s in 0..s₀, (Φ t s - Φ t' s)‖ ≤ 2 / (2 - α) * K * H * h ^ ((α : ℝ) / 2) := by
    simpa only [mul_assoc] using norm_integral_le_of_ae_norm_le_mul_sub_rpow (A := K * H)
      (by positivity) hh hbig hα₂' (hK hf hfM hH htt' |>.mono fun s hs hsI => hs hsI x)
  rw [hsplit (by linarith) le_rfl, hsplit (by linarith) htt'.le,
    show ∀ a b c d : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F,
      a + b - (c + d) = (a - c) + b - d from fun a b c d => by abel,
    ← intervalIntegral.integral_sub (hint₀ (by linarith) le_rfl) (hint₀ (by linarith) htt'.le)]
  calc ‖(∫ s in 0..s₀, (Φ t s - Φ t' s)) + (∫ s in s₀..t, Φ t s) - ∫ s in s₀..t', Φ t' s‖
      ≤ ‖∫ s in 0..s₀, (Φ t s - Φ t' s)‖ + ‖∫ s in s₀..t, Φ t s‖ +
          ‖∫ s in s₀..t', Φ t' s‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ 2 / (2 - α) * K * H * h ^ ((α : ℝ) / 2) + C₁ * H * (t - s₀) ^ ((α : ℝ) / 2) +
          C₁ * H * (t' - s₀) ^ ((α : ℝ) / 2) := by
        gcongr
        · exact hnear hs₀.le (by linarith) le_rfl
        · exact hnear hs₀.le (by linarith) htt'.le
    _ ≤ 2 / (2 - α) * K * H * h ^ ((α : ℝ) / 2) + C₁ * H * (2 * h ^ ((α : ℝ) / 2)) +
          C₁ * H * h ^ ((α : ℝ) / 2) := by
        rw [show t - s₀ = 2 * h by ring, show t' - s₀ = h by ring]
        gcongr
        exact hpow (by linarith) le_rfl
    _ = _ := by
        rw [← hfinal]
        ring

/-- **The temporal Hölder estimate for the Hessian of the Duhamel potential.** For `0 < α < 2`
there is a constant `C`, depending only on `α` and the dimension, such that at every point `x`
the Hessian `t ↦ D² w(t, ·)(x)` is `α/2`-Hölder in time on `[0, T]` with constant `C H`, whenever
`f` is jointly measurable and essentially bounded on `(0, T) × E` and `f(s, ·)` is `α`-Hölder
with constant `H` for almost every `0 < s < T`. Neither the bound on `f` nor the horizon `T`
enters the estimate. Together with
`TauCeti.exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential` this is the parabolic
`α`-Hölder estimate of `D² w` on the slab `E × [0, T]`, for `0 < α < 1`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential {α : ℝ≥0} (hα₀ : 0 < α)
    (hα₂ : α < 2) :
    ∃ C : ℝ≥0, ∀ {f : ℝ → E → F} {M T : ℝ} {H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s)) → ∀ x,
        HolderOnWith (C * H) (α / 2)
          (fun t => iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x) (Icc 0 T) := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_norm_iteratedFDeriv_two_heatDuhamelPotential_sub_le (E := E) (F := F) hα₀ hα₂
  refine ⟨C.toNNReal, fun {f M T H} hf hfM hH x => ?_⟩
  have hsub {t t' : ℝ} (ht' : 0 ≤ t') (htt' : t' ≤ t) (htT : t ≤ T) :
      ‖iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x -
          iteratedFDeriv ℝ 2 (heatDuhamelPotential f t') x‖ ≤
        C * H * dist t t' ^ ((α / 2 : ℝ≥0) : ℝ) := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 htt'), NNReal.coe_div, NNReal.coe_ofNat]
    exact hC hf (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right htT) hfM)
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right htT) hH) ht' htt' x
  refine HolderOnWith.of_dist_le fun t ht t' ht' => ?_
  rw [dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hC₀]
  rcases le_total t' t with htt' | htt'
  · exact hsub ht'.1 htt' ht.2
  · rw [norm_sub_rev, dist_comm]
    exact hsub ht.1 htt' ht'.2

end Duhamel

end TauCeti
