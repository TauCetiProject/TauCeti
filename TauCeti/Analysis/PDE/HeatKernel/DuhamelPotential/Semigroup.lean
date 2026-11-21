/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Lp

/-!
# Duhamel's formula for the heat equation on `Lᵖ`

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The inhomogeneous heat equation

`∂ₜu = Δu + f`, `u(0) = u₀`,

with `u₀ ∈ Lᵖ(E; F)` and a forcing `f` whose time slices lie in `Lᵖ`, is posed on `Lᵖ` through the
heat semigroup `e^{tΔ}` (`TauCeti.heatSemigroup`), whose generator is the Laplacian `Δ` in the
sense of distributions with domain `{u ∈ Lᵖ : Δu ∈ Lᵖ}`
(`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`). A *mild solution*
(`TauCeti.Semigroups.IsForcedMildSolution`) is a continuous `u : ℝ → Lᵖ` whose time integrals lie
in that domain, with

`Δ (∫₀ᵗ u) = u(t) - u₀ - ∫₀ᵗ f`.

This file proves **Duhamel's formula**: for `f` locally integrable in time with values in `Lᵖ`,
the heat equation has exactly one mild solution on `[0, ∞)`, namely

`u(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} f(s) ds`

(`TauCeti.isForcedMildSolution_weakLaplacianLp_iff`), and identifies it with the classical
formula. The integral above is a Bochner integral of `Lᵖ`-valued functions. If `f` is given by a
jointly measurable function `f(s, x)`, it is represented almost everywhere by the classical
Duhamel heat potential `w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` of
`TauCeti.heatDuhamelPotential` (`TauCeti.duhamel_heatSemigroup_ae_eq_heatDuhamelPotential`), so the
mild solution at time `t > 0` is represented by the convolution of the heat kernel `K_t` with
`u₀` plus `w(t, ·)`
(`TauCeti.Semigroups.IsForcedMildSolution.ae_eq_heatKernel_convolution_add_heatDuhamelPotential`).
Since the semigroup is a contraction, the potential obeys the estimate
`‖w(t, ·)‖_p ≤ ∫₀ᵗ ‖f(s, ·)‖_p ds` (`TauCeti.eLpNorm_heatDuhamelPotential_le`).

The identification of the two integrals is made on sets of finite measure: integrating the
`Lᵖ`-valued integral over such a set is a continuous linear functional on `Lᵖ`, which commutes
with the time integral, and Fubini's theorem exchanges the time and space integrals of the
representatives `(K_{t-s} ⋆ f(s, ·))(x)` of `e^{(t-s)Δ} f(s)`
(`MeasureTheory.Integrable.coeFn_integral_Lp`).

## Main declarations

* `TauCeti.isForcedMildSolution_weakLaplacianLp_iff`: **Duhamel's formula**, existence and
  uniqueness of the mild solution of `∂ₜu = Δu + f`, `u(0) = u₀`, on `Lᵖ`.
* `TauCeti.duhamel_heatSemigroup_ae_eq_heatDuhamelPotential`: the `Lᵖ`-valued Duhamel integral is
  represented by the classical Duhamel heat potential.
* `TauCeti.Semigroups.IsForcedMildSolution.ae_eq_heatKernel_convolution_add_heatDuhamelPotential`:
  the mild solution is represented by `K_t ⋆ u₀ + w(t, ·)`.
* `TauCeti.eLpNorm_heatDuhamelPotential_le`: the `Lᵖ` estimate of the Duhamel heat potential.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.3.1 (Duhamel's principle for the
  nonhomogeneous heat equation).
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 4.2 (mild solutions of the inhomogeneous Cauchy problem).
-/

public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Semigroups Set
open scoped Convolution ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {G : ℝ → Lp F p (volume : Measure E)} {f : ℝ → E → F}
  {u₀ : Lp F p (volume : Measure E)} {u : ℝ → Lp F p (volume : Measure E)} {t : ℝ}

/-- **Duhamel's formula for the heat equation on `Lᵖ`.** Let `1 ≤ p < ∞` and let the forcing
`G : ℝ → Lᵖ` be locally integrable on `[0, ∞)`. Then `u` is a mild solution of `∂ₜu = Δu + G`,
`u(0) = u₀`, for the Laplacian `Δ` in the sense of distributions, if and only if
`u(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} G(s) ds` for every `t ≥ 0`. In particular the mild solution
exists and is unique on `[0, ∞)`. -/
theorem isForcedMildSolution_weakLaplacianLp_iff (hp : p ≠ ∞) (hG : LocallyIntegrableOn G (Ici 0)) :
    IsForcedMildSolution (weakLaplacianLp E F p) G u₀ u ↔
      ∀ t, 0 ≤ t → u t = (heatSemigroup hp).realOperator t u₀ + (heatSemigroup hp).duhamel G t := by
  rw [← generator_heatSemigroup_eq_weakLaplacianLp hp]
  exact ⟨fun hu t ht => hu.eq_realOperator_add_duhamel ht, fun h =>
    ((heatSemigroup hp).isForcedMildSolution_realOperator_add_duhamel hG u₀).congr
      fun t ht => (h t ht).symm⟩

/-- **The `Lᵖ` Duhamel integral is the classical Duhamel heat potential.** Let `1 ≤ p < ∞`, `t ≥ 0`
and let `G : ℝ → Lᵖ` be integrable on `(0, t]`. If `f` is jointly measurable and `G(s)` is the
class of `f(s, ·)` for almost every `s ∈ (0, t]`, then the `Lᵖ`-valued integral
`∫₀ᵗ e^{(t-s)Δ} G(s) ds` is represented almost everywhere by the Duhamel heat potential
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds`. -/
theorem duhamel_heatSemigroup_ae_eq_heatDuhamelPotential (hp : p ≠ ∞) (ht : 0 ≤ t)
    (hG : IntegrableOn G (Ioc 0 t)) (hf : StronglyMeasurable (uncurry f))
    (hGf : ∀ᵐ s ∂volume.restrict (Ioc 0 t), G s =ᵐ[volume] f s) :
    (heatSemigroup hp).duhamel G t =ᵐ[volume] heatDuhamelPotential f t := by
  have hIoo : ∀ᵐ s ∂volume.restrict (Ioc 0 t), s ∈ Ioo 0 t := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  -- The representatives of `e^{(t-s)Δ} G(s)` are the heat convolutions `K_{t-s} ⋆ f(s, ·)`.
  have h := ((heatSemigroup hp).integrableOn_realOperator_sub_apply hG).coeFn_integral_Lp
    (X := fun s x => (heatKernel (t - s) ⋆ f s) x)
    (stronglyMeasurable_heatKernel_convolution (τ := (t - ·)) (by fun_prop)
      hf).aestronglyMeasurable <| by
      filter_upwards [hGf, hIoo] with s hs hst
      rw [heatSemigroup_realOperator hp (sub_pos.2 hst.2)]
      exact (convolutionLp_ae_eq_convolution_coeFn hp (integrable_heatKernel (sub_pos.2 hst.2))
        (G s)).trans (.of_eq (convolution_congr _ .rfl hs))
  rw [StronglyContinuousSemigroup.duhamel_def]
  refine h.trans (.of_eq (funext fun x => ?_))
  rw [heatDuhamelPotential_def, intervalIntegral.integral_of_le ht]

/-- **Duhamel's formula for the heat equation, in classical form.** Let `1 ≤ p < ∞`, `t > 0`, and
let `u` be a mild solution on `Lᵖ` of `∂ₜu = Δu + G`, `u(0) = u₀`. If `f` is jointly measurable and
`G(s)` is the class of `f(s, ·)` for almost every `s ∈ (0, t]`, then `u(t)` is represented almost
everywhere by `K_t ⋆ u₀ + w(t, ·)`, where `K_t` is the heat kernel and
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` is the Duhamel heat potential. -/
theorem Semigroups.IsForcedMildSolution.ae_eq_heatKernel_convolution_add_heatDuhamelPotential
    (hp : p ≠ ∞) (hu : IsForcedMildSolution (weakLaplacianLp E F p) G u₀ u) (ht : 0 < t)
    (hf : StronglyMeasurable (uncurry f))
    (hGf : ∀ᵐ s ∂volume.restrict (Ioc 0 t), G s =ᵐ[volume] f s) :
    u t =ᵐ[volume] heatKernel t ⋆ (u₀ : E → F) + heatDuhamelPotential f t := by
  rw [(isForcedMildSolution_weakLaplacianLp_iff hp hu.locallyIntegrableOn).1 hu t ht.le,
    heatSemigroup_realOperator hp ht]
  filter_upwards [Lp.coeFn_add (convolutionLp hp (heatKernel t) volume u₀)
      ((heatSemigroup hp).duhamel G t),
    convolutionLp_ae_eq_convolution_coeFn hp (integrable_heatKernel ht) u₀,
    duhamel_heatSemigroup_ae_eq_heatDuhamelPotential hp ht.le
      (hu.locallyIntegrableOn.integrableOn_Ioc_of_Ici t) hf hGf] with x h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃, Pi.add_apply]

/-- **The `Lᵖ` estimate for the Duhamel heat potential.** Let `1 ≤ p < ∞`, `t ≥ 0` and let
`G : ℝ → Lᵖ` be integrable on `(0, t]`. If `f` is jointly measurable and `G(s)` is the class of
`f(s, ·)` for almost every `s ∈ (0, t]`, then the Duhamel heat potential
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` satisfies `‖w(t, ·)‖_p ≤ ∫₀ᵗ ‖G(s)‖_p ds`, where
`‖G(s)‖_p = ‖f(s, ·)‖_p` for almost every `s`. -/
theorem eLpNorm_heatDuhamelPotential_le (hp : p ≠ ∞) (ht : 0 ≤ t)
    (hG : IntegrableOn G (Ioc 0 t)) (hf : StronglyMeasurable (uncurry f))
    (hGf : ∀ᵐ s ∂volume.restrict (Ioc 0 t), G s =ᵐ[volume] f s) :
    eLpNorm (heatDuhamelPotential f t) p volume ≤ ENNReal.ofReal (∫ s in Ioc 0 t, ‖G s‖) := by
  rw [← eLpNorm_congr_ae (duhamel_heatSemigroup_ae_eq_heatDuhamelPotential hp ht hG hf hGf),
    ← Lp.eNorm_def, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (((heatSemigroup hp).norm_duhamel_le
    (fun τ _ => (heatSemigroup hp).contracting_real τ) hG).trans_eq (one_mul _))

end TauCeti
