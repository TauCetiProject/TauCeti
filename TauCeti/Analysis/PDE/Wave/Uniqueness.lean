/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.WeakSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.PDE.HeatKernel.Core
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Uniqueness of weak solutions of the wave equation

On a finite-dimensional real inner product space `E`, consider the Cauchy problem for the wave
equation

`∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`,

with data `f, g ∈ L²(E, F)` and a continuous forcing `G : ℝ → L²(E, F)`. Pairing the equation with
a test function `φ` and integrating twice in time gives its **weak formulation**: for every time
`t`,

`⟪φ, u t⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - r) (⟪Δφ, u r⟫ + ⟪φ, G r⟫) dr`,

which is Taylor's formula of order one for `t ↦ ⟪φ, u t⟫`, whose second derivative is
`⟪Δφ, u t⟫ + ⟪φ, G t⟫`. It makes sense for every `u` continuous in time with values in `L²`, with
no differentiability in time and no regularity in space.

Duhamel's formula `u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - r)D) G(r) dr`
(`TauCeti.waveDuhamelSolution`) satisfies the weak formulation against every `φ ∈ L²` whose
distributional Laplacian `ψ = Δφ` lies in `L²` (`TauCeti.inner_waveDuhamelSolution`), in particular
against every Schwartz function (`TauCeti.inner_toLp_waveDuhamelSolution`). This file proves the
converse: on an order-connected set of times `s` containing `0`, a function continuous on `s` with
values in `L²` satisfies the weak formulation against Schwartz functions exactly when it agrees on
`s` with Duhamel's formula (`TauCeti.eqOn_waveDuhamelSolution_iff`). So the Cauchy problem has
exactly one weak solution in `C(s; L²)`, and a fortiori in the energy class, where `u` is moreover
continuous with values in `H¹` and continuously differentiable with values in `L²`. The heart of
the matter is the case of zero data and zero forcing
(`TauCeti.eqOn_zero_of_forall_inner_toLp_eq_integral_smul_inner_toLp_laplacian`). A strong solution
(`TauCeti.IsWaveSolutionOn`) with continuous forcing is given by Duhamel's formula
(`TauCeti.IsWaveSolutionOn.eq_waveDuhamelSolution`), so it is a weak solution, and this uniqueness
theorem extends the energy uniqueness theorem `TauCeti.IsWaveSolutionOn.eq_zero` for strong
solutions, from which it is deduced.

## The argument

Let `w` be continuous on `s` and satisfy the weak formulation with zero data and zero forcing.

* **Passing to the domain of the Laplacian.** The Schwartz functions are a core for the Laplacian
  on `L²` (`TauCeti.exists_tendsto_toLp_and_tendsto_toLp_laplacian`), and both sides of the weak
  formulation are continuous in the pair `(φ, Δφ)`, once the time integral is moved into the second
  slot of the inner product: `⟪φ, w t⟫ = ⟪ψ, ∫₀ᵗ (t - r) w r dr⟫` whenever `Δφ = ψ ∈ L²`.
* **Smoothing in space.** Let `P = (1 - Δ)⁻¹` and `Q = Δ (1 - Δ)⁻¹`, the `L²` Fourier multipliers
  with the real symbols `(1 + 4π² ‖ξ‖²)⁻¹` and `-4π² ‖ξ‖² (1 + 4π² ‖ξ‖²)⁻¹`, both bounded by `1`.
  Both are self-adjoint, `Δ (P χ) = Q χ` for every `χ ∈ L²`, and `P` is injective, since its symbol
  does not vanish. Testing with `φ = P χ`, `ψ = Q χ` for arbitrary `χ` gives the identity
  `P (w t) = ∫₀ᵗ (t - r) Q (w r) dr` in `L²`.
* **A strong solution.** The right-hand side is twice differentiable in `t` on every compact
  interval of `s` containing `0`, with second derivative `Q (w t) = Δ (P (w t))`, since `Q ∘ w` is
  continuous. So `P ∘ w` is a strong solution of the free wave equation with zero data, and the
  energy uniqueness theorem gives `P (w t) = 0`, hence `w t = 0`.

## Main declarations

* `TauCeti.inner_waveDuhamelSolution`, `TauCeti.inner_toLp_waveDuhamelSolution`: Duhamel's formula
  satisfies the weak formulation.
* `TauCeti.eqOn_zero_of_forall_inner_toLp_eq_integral_smul_inner_toLp_laplacian`: a continuous weak
  solution of the free equation with zero data vanishes.
* `TauCeti.eqOn_waveDuhamelSolution_iff`: the weak formulation characterizes Duhamel's formula.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 7.2 (weak solutions of
  hyperbolic equations and their uniqueness).
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Duhamel's formula and the wave equation).
-/

public section

noncomputable section

open scoped FourierTransform ComplexInnerProductSpace Topology ENNReal SchwartzMap Laplacian
open MeasureTheory Filter Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ### Taylor's formula of order one and the double time integral -/

/-- **Taylor's formula of order one with integral remainder**: if `a' = b` and `b' = c` everywhere,
with `c` continuous, then `a t = a 0 + t b 0 + ∫₀ᵗ (t - r) c r dr`. -/
private theorem eq_add_smul_add_integral_sub_smul {a b c : ℝ → ℂ}
    (ha : ∀ τ, HasDerivAt a (b τ) τ) (hb : ∀ τ, HasDerivAt b (c τ) τ) (hc : Continuous c)
    (t : ℝ) : a t = a 0 + t • b 0 + ∫ r in (0 : ℝ)..t, (t - r) • c r := by
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun τ ↦ (hb τ).continuousAt
  -- Integrate by parts against `r ↦ t - r`, whose derivative is `-1`.
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt (a := 0)
    (b := t) (u := fun r ↦ t - r) (u' := fun _ ↦ (-1 : ℝ)) (v := b) (v' := c)
    (continuous_const.sub continuous_id).continuousOn hbc.continuousOn
    (fun r _ ↦ by simpa using (hasDerivAt_id r).const_sub t) (fun r _ ↦ hb r)
    intervalIntegrable_const (hc.intervalIntegrable 0 t)
  have hftc : ∫ r in (0 : ℝ)..t, b r = a t - a 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ ha r) (hbc.intervalIntegrable 0 t)
  rw [hparts, sub_self, zero_smul, zero_sub, sub_zero]
  simp only [neg_smul, one_smul, intervalIntegral.integral_neg, hftc]
  abel

/-- The fundamental theorem of calculus within a compact interval `[a, b]` containing `0`. -/
private theorem hasDerivWithinAt_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {A : ℝ → X} {a b τ : ℝ} (hA : ContinuousOn A (Icc a b))
    (h0 : (0 : ℝ) ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    HasDerivWithinAt (fun σ ↦ ∫ r in (0 : ℝ)..σ, A r) (A τ) (Icc a b) τ := by
  have : Fact (τ ∈ Icc a b) := ⟨hτ⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (hA.mono (uIcc_subset_Icc h0 hτ)).intervalIntegrable
    (hA.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc τ) (hA τ hτ)

/-- Within a compact interval `[a, b]` containing `0`, the double time integral
`σ ↦ ∫₀^σ (σ - r) A r dr` of a continuous `A` has derivative `∫₀^τ A r dr` at `τ`. -/
private theorem hasDerivWithinAt_integral_sub_smul {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {A : ℝ → X} {a b τ : ℝ} (hA : ContinuousOn A (Icc a b))
    (h0 : (0 : ℝ) ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    HasDerivWithinAt (fun σ ↦ ∫ r in (0 : ℝ)..σ, (σ - r) • A r) (∫ r in (0 : ℝ)..τ, A r)
      (Icc a b) τ := by
  have hrA : ContinuousOn (fun r ↦ r • A r) (Icc a b) := continuousOn_id.smul hA
  -- On `[a, b]`, `∫₀^σ (σ - r) A r dr = σ ∫₀^σ A r dr - ∫₀^σ r A r dr`.
  have hsplit (σ : ℝ) (hσ : σ ∈ Icc a b) : ∫ r in (0 : ℝ)..σ, (σ - r) • A r =
      σ • (∫ r in (0 : ℝ)..σ, A r) - ∫ r in (0 : ℝ)..σ, r • A r := by
    have h₁ : IntervalIntegrable (fun r ↦ σ • A r) volume 0 σ :=
      (continuousOn_const.smul (hA.mono (uIcc_subset_Icc h0 hσ))).intervalIntegrable
    simp_rw [sub_smul]
    rw [intervalIntegral.integral_sub h₁ (hrA.mono (uIcc_subset_Icc h0 hσ)).intervalIntegrable,
      intervalIntegral.integral_smul]
  have h := ((hasDerivWithinAt_id τ (Icc a b)).smul (hasDerivWithinAt_integral hA h0 hτ)).sub
    (hasDerivWithinAt_integral hrA h0 hτ)
  refine (h.congr hsplit (hsplit τ hτ)).congr_deriv ?_
  simp

/-! ### The resolvent `(1 - Δ)⁻¹` -/

/-- The symbol `(1 + 4π² ‖ξ‖²)⁻¹ = (1 - Λ(ξ))⁻¹` of the resolvent `(1 - Δ)⁻¹`, where `Λ` is the
symbol `-4π² ‖ξ‖²` of `Δ`. -/
private def resolventSymbol (ξ : E) : ℝ :=
  (1 - laplacianSymbol ξ)⁻¹

/-- The symbol `Λ(ξ) (1 - Λ(ξ))⁻¹` of `Δ (1 - Δ)⁻¹`. -/
private def laplacianResolventSymbol (ξ : E) : ℝ :=
  laplacianSymbol ξ * resolventSymbol ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem laplacianSymbol_nonpos (ξ : E) : laplacianSymbol ξ ≤ 0 := by
  rw [laplacianSymbol_apply, neg_nonpos]
  positivity

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem resolventSymbol_pos (ξ : E) : 0 < resolventSymbol ξ :=
  inv_pos.2 (by linarith [laplacianSymbol_nonpos ξ])

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_resolventSymbol : Continuous (resolventSymbol (E := E)) :=
  (continuous_const.sub laplacianSymbol.continuous).inv₀ fun ξ ↦
    (by linarith [laplacianSymbol_nonpos ξ] : (0 : ℝ) < 1 - laplacianSymbol ξ).ne'

private theorem memLp_resolventSymbol :
    MemLp (fun ξ : E ↦ (resolventSymbol ξ : ℂ)) ∞ volume := by
  refine memLp_top_of_bound (Complex.continuous_ofReal.comp
    continuous_resolventSymbol).aestronglyMeasurable 1 (Eventually.of_forall fun ξ ↦ ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (resolventSymbol_pos ξ).le]
  exact inv_le_one_of_one_le₀ (by linarith [laplacianSymbol_nonpos ξ])

private theorem memLp_laplacianResolventSymbol :
    MemLp (fun ξ : E ↦ (laplacianResolventSymbol ξ : ℂ)) ∞ volume := by
  refine memLp_top_of_bound (Complex.continuous_ofReal.comp
    (laplacianSymbol.continuous.mul continuous_resolventSymbol)).aestronglyMeasurable 1
    (Eventually.of_forall fun ξ ↦ ?_)
  have hl := laplacianSymbol_nonpos ξ
  rw [Complex.norm_real, Real.norm_eq_abs, laplacianResolventSymbol, resolventSymbol,
    ← div_eq_mul_inv, abs_div, abs_of_nonpos hl, abs_of_pos (by linarith),
    div_le_one (by linarith)]
  linarith

variable (F) in
/-- The resolvent `P = (1 - Δ)⁻¹` on `L²(E, F)`. -/
private def resolventL : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F (memLp_resolventSymbol.toLp _)

variable (F) in
/-- The bounded operator `Q = Δ (1 - Δ)⁻¹` on `L²(E, F)`. -/
private def laplacianResolventL : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F (memLp_laplacianResolventSymbol.toLp _)

/-- `Δ (P χ) = Q χ` for every `χ ∈ L²`. -/
private theorem laplacian_resolventL_apply (χ : Lp F 2 (volume : Measure E)) :
    Δ ((resolventL F χ : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (laplacianResolventL F χ : 𝓢'(E, F)) := by
  refine (Lp.laplacian_toTemperedDistribution_eq_iff _ _).2 ?_
  filter_upwards [Lp.coeFn_fourier_fourierMultiplierCLM_toLp χ memLp_laplacianResolventSymbol,
    Lp.coeFn_fourier_fourierMultiplierCLM_toLp χ memLp_resolventSymbol] with ξ h₁ h₂
  rw [laplacianResolventL, resolventL, h₁, h₂, smul_smul, laplacianResolventSymbol,
    Complex.ofReal_mul]

/-- `P` moves across the `L²` inner product, since its symbol is real. -/
private theorem inner_resolventL_apply (x y : Lp F 2 (volume : Measure E)) :
    ⟪resolventL F x, y⟫ = ⟪x, resolventL F y⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, resolventL,
    (Lp.isSelfAdjoint_fourierMultiplierCLM
      (Lp.star_eq_self_of_ae_eq_ofReal memLp_resolventSymbol.coeFn_toLp)).adjoint_eq]

/-- `Q` moves across the `L²` inner product, since its symbol is real. -/
private theorem inner_laplacianResolventL_apply (x y : Lp F 2 (volume : Measure E)) :
    ⟪laplacianResolventL F x, y⟫ = ⟪x, laplacianResolventL F y⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, laplacianResolventL,
    (Lp.isSelfAdjoint_fourierMultiplierCLM
      (Lp.star_eq_self_of_ae_eq_ofReal memLp_laplacianResolventSymbol.coeFn_toLp)).adjoint_eq]

/-- `P` is injective, since its symbol does not vanish. -/
private theorem resolventL_injective : Function.Injective (resolventL (E := E) F) := by
  refine (injective_iff_map_eq_zero (resolventL (E := E) F)).2 fun x hx ↦ ?_
  -- The Fourier transform on `L²` is by definition `Lp.fourierTransformₗᵢ`.
  have hF (y : Lp F 2 (volume : Measure E)) : Lp.fourierTransformₗᵢ E F y = 𝓕 y := rfl
  have h := Lp.coeFn_fourier_fourierMultiplierCLM_toLp x memLp_resolventSymbol
  rw [← resolventL, hx, ← hF, map_zero] at h
  refine (Lp.fourierTransformₗᵢ E F).injective ?_
  rw [map_zero, hF]
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  filter_upwards [h, Lp.coeFn_zero F 2 (volume : Measure E)] with ξ h₁ h₂
  rw [h₂, Pi.zero_apply, eq_comm, smul_eq_zero] at h₁
  exact h₁.resolve_left (Complex.ofReal_ne_zero.2 (resolventSymbol_pos ξ).ne')

/-! ### Uniqueness -/

/-- **Uniqueness of weak solutions, against the domain of the Laplacian.** A function `w`
continuous on an order-connected set of times `s ∋ 0` with
`⟪φ, w t⟫ = ⟪ψ, ∫₀ᵗ (t - r) w r dr⟫` for all `t ∈ s` and all `φ, ψ ∈ L²` with `Δφ = ψ` vanishes
on `s`. -/
private theorem eqOn_zero_of_forall_inner_eq_inner_integral {s : Set ℝ} [s.OrdConnected]
    (h0 : 0 ∈ s) {w : ℝ → Lp F 2 (volume : Measure E)} (hw : ContinuousOn w s)
    (h : ∀ φ ψ : Lp F 2 (volume : Measure E), Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)) →
      ∀ t ∈ s, ⟪φ, w t⟫ = ⟪ψ, ∫ r in (0 : ℝ)..t, (t - r) • w r⟫) :
    EqOn w 0 s := by
  intro t ht
  have hI : Icc (0 ⊓ t) (0 ⊔ t) ⊆ s := Set.OrdConnected.uIcc_subset ‹_› h0 ht
  have h0I : (0 : ℝ) ∈ Icc (0 ⊓ t) (0 ⊔ t) := ⟨inf_le_left, le_sup_left⟩
  have hwI : ContinuousOn w (Icc (0 ⊓ t) (0 ⊔ t)) := hw.mono hI
  -- Testing with `φ = P χ` and `ψ = Q χ` for every `χ` gives `P (w τ) = ∫₀^τ (τ - r) Q (w r) dr`.
  have hP (τ : ℝ) (hτ : τ ∈ Icc (0 ⊓ t) (0 ⊔ t)) :
      resolventL F (w τ) = ∫ r in (0 : ℝ)..τ, (τ - r) • laplacianResolventL F (w r) := by
    have hint : IntervalIntegrable (fun r ↦ (τ - r) • w r) volume 0 τ :=
      ((continuous_const.sub continuous_id).continuousOn.smul
        (hwI.mono (uIcc_subset_Icc h0I hτ))).intervalIntegrable
    refine ext_inner_left ℂ fun χ ↦ ?_
    rw [← inner_resolventL_apply, h _ _ (laplacian_resolventL_apply χ) τ (hI hτ),
      inner_laplacianResolventL_apply, ← (laplacianResolventL F).intervalIntegral_comp_comm hint]
    simp only [ContinuousLinearMap.map_smul_of_tower]
  -- So `P ∘ w` is a strong solution of the free wave equation with zero data on `[0 ⊓ t, 0 ⊔ t]`.
  have hQ : ContinuousOn (fun τ ↦ laplacianResolventL F (w τ)) (Icc (0 ⊓ t) (0 ⊔ t)) :=
    (laplacianResolventL F).continuous.comp_continuousOn hwI
  have hsol : IsWaveSolutionOn (fun τ ↦ resolventL F (w τ))
      (fun τ ↦ ∫ r in (0 : ℝ)..τ, laplacianResolventL F (w r))
      (fun τ ↦ laplacianResolventL F (w τ)) 0 (Icc (0 ⊓ t) (0 ⊔ t)) :=
    ⟨fun τ hτ ↦
      (hasDerivWithinAt_integral_sub_smul hQ h0I hτ).congr (fun σ hσ ↦ hP σ hσ) (hP τ hτ),
    fun τ hτ ↦ hasDerivWithinAt_integral hQ h0I hτ,
    fun τ _ ↦ by simpa using laplacian_resolventL_apply (w τ)⟩
  have hzero := hsol.eq_zero h0I (by simp [hP 0 h0I]) (by simp) ⟨inf_le_right, le_sup_right⟩
  exact resolventL_injective (hzero.trans (map_zero _).symm)

/-- A weak solution of the free equation with zero data against Schwartz functions is one against
every pair `φ, ψ ∈ L²` with `Δφ = ψ`, since Schwartz functions are a core for the Laplacian. -/
private theorem inner_eq_inner_integral_of_forall_inner_toLp_eq {s : Set ℝ} [s.OrdConnected]
    (h0 : 0 ∈ s) {w : ℝ → Lp F 2 (volume : Measure E)} (hw : ContinuousOn w s)
    (h : ∀ φ : 𝓢(E, F), ∀ t ∈ s,
      ⟪φ.toLp 2, w t⟫ = ∫ r in (0 : ℝ)..t, (t - r) • ⟪(Δ φ).toLp 2, w r⟫)
    {φ ψ : Lp F 2 (volume : Measure E)} (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) {t : ℝ}
    (ht : t ∈ s) :
    ⟪φ, w t⟫ = ⟪ψ, ∫ r in (0 : ℝ)..t, (t - r) • w r⟫ := by
  obtain ⟨φₙ, h₁, h₂⟩ := exists_tendsto_toLp_and_tendsto_toLp_laplacian
    ((Lp.laplacian_toTemperedDistribution_eq_iff φ ψ).1 hφψ)
  have hint : IntervalIntegrable (fun r ↦ (t - r) • w r) volume 0 t :=
    ((continuous_const.sub continuous_id).continuousOn.smul
      (hw.mono (Set.OrdConnected.uIcc_subset ‹_› h0 ht))).intervalIntegrable
  -- The time integral moves into the second slot of the inner product.
  have hpull (χ : Lp F 2 (volume : Measure E)) :
      ∫ r in (0 : ℝ)..t, (t - r) • ⟪χ, w r⟫ = ⟪χ, ∫ r in (0 : ℝ)..t, (t - r) • w r⟫ := by
    rw [← innerSL_apply_apply ℂ, ← (innerSL ℂ χ).intervalIntegral_comp_comm hint]
    simp only [innerSL_apply_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_real_right]
  refine tendsto_nhds_unique (h₁.inner tendsto_const_nhds)
    ((h₂.inner tendsto_const_nhds).congr fun n ↦ ?_)
  rw [h (φₙ n) t ht, hpull]

/-- **Uniqueness of weak solutions of the wave equation.** Let `s` be an order-connected set of
times containing `0`, and let `w` be continuous on `s` with values in `L²(E, F)`. Suppose that `w`
solves the free wave equation `∂ₜ²w = Δw` with `w(0) = 0` and `∂ₜw(0) = 0` weakly against
Schwartz functions: for every `φ ∈ 𝓢(E, F)` and every `t ∈ s`,

`⟪φ, w t⟫ = ∫₀ᵗ (t - r) ⟪Δφ, w r⟫ dr`.

Then `w = 0` on `s`. -/
theorem eqOn_zero_of_forall_inner_toLp_eq_integral_smul_inner_toLp_laplacian {s : Set ℝ}
    [s.OrdConnected] (h0 : 0 ∈ s) {w : ℝ → Lp F 2 (volume : Measure E)} (hw : ContinuousOn w s)
    (h : ∀ φ : 𝓢(E, F), ∀ t ∈ s,
      ⟪φ.toLp 2, w t⟫ = ∫ r in (0 : ℝ)..t, (t - r) • ⟪(Δ φ).toLp 2, w r⟫) :
    EqOn w 0 s :=
  eqOn_zero_of_forall_inner_eq_inner_integral h0 hw fun _ _ hφψ _ ht ↦
    inner_eq_inner_integral_of_forall_inner_toLp_eq h0 hw h hφψ ht

/-! ### Duhamel's formula is the weak solution -/

/-- **Duhamel's formula is a weak solution** of the wave equation `∂ₜ²u - Δu = G`, `u(0) = f`,
`∂ₜu(0) = g`, for continuous forcing `G`: for all `φ, ψ ∈ L²` with `Δφ = ψ` and every time `t`,

`⟪φ, u t⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - r) (⟪ψ, u r⟫ + ⟪φ, G r⟫) dr`. -/
theorem inner_waveDuhamelSolution {φ ψ : Lp F 2 (volume : Measure E)}
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} (hG : Continuous G) (t : ℝ) :
    ⟪φ, waveDuhamelSolution F f g G t⟫ = ⟪φ, f⟫ + t • ⟪φ, g⟫ +
      ∫ r in (0 : ℝ)..t, (t - r) • (⟪ψ, waveDuhamelSolution F f g G r⟫ + ⟪φ, G r⟫) := by
  have hc : Continuous fun r ↦ ⟪ψ, waveDuhamelSolution F f g G r⟫ + ⟪φ, G r⟫ :=
    (continuous_const.inner (continuous_waveDuhamelSolution f g hG)).add
      (continuous_const.inner hG)
  rw [eq_add_smul_add_integral_sub_smul
    (fun τ ↦ (hasDerivAt_inner_waveDuhamelSolution hφψ f g hG τ).differentiableAt.hasDerivAt)
    (hasDerivAt_deriv_inner_waveDuhamelSolution hφψ f g hG) hc t,
    (hasDerivAt_inner_waveDuhamelSolution_zero hφψ f g hG).deriv, waveDuhamelSolution_zero]

/-- **The wave equation in the sense of distributions, integrated in time.** Duhamel's formula
satisfies the weak formulation against every Schwartz function `φ`:
`⟪φ, u t⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - r) (⟪Δφ, u r⟫ + ⟪φ, G r⟫) dr`. -/
theorem inner_toLp_waveDuhamelSolution (φ : 𝓢(E, F)) (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} (hG : Continuous G) (t : ℝ) :
    ⟪φ.toLp 2, waveDuhamelSolution F f g G t⟫ = ⟪φ.toLp 2, f⟫ + t • ⟪φ.toLp 2, g⟫ +
      ∫ r in (0 : ℝ)..t,
        (t - r) • (⟪(Δ φ).toLp 2, waveDuhamelSolution F f g G r⟫ + ⟪φ.toLp 2, G r⟫) :=
  inner_waveDuhamelSolution (by simp) f g hG t

/-- **The weak formulation of the wave equation characterizes Duhamel's formula.** Let `G` be
continuous, let `s` be an order-connected set of times containing `0`, and let `u` be continuous on
`s` with values in `L²(E, F)`. Then `u` agrees on `s` with Duhamel's formula
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - r)D) G(r) dr` if and only if `u` is a weak
solution of `∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g` on `s`: for every Schwartz function `φ` and
every `t ∈ s`,

`⟪φ, u t⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - r) (⟪Δφ, u r⟫ + ⟪φ, G r⟫) dr`.

In particular the weak solution is unique in `C(s; L²)`. -/
theorem eqOn_waveDuhamelSolution_iff {f g : Lp F 2 (volume : Measure E)}
    {G : ℝ → Lp F 2 (volume : Measure E)} (hG : Continuous G) {s : Set ℝ} [s.OrdConnected]
    (h0 : 0 ∈ s) {u : ℝ → Lp F 2 (volume : Measure E)} (hu : ContinuousOn u s) :
    EqOn u (waveDuhamelSolution F f g G) s ↔
      ∀ φ : 𝓢(E, F), ∀ t ∈ s, ⟪φ.toLp 2, u t⟫ = ⟪φ.toLp 2, f⟫ + t • ⟪φ.toLp 2, g⟫ +
        ∫ r in (0 : ℝ)..t, (t - r) • (⟪(Δ φ).toLp 2, u r⟫ + ⟪φ.toLp 2, G r⟫) := by
  have hU : Continuous (waveDuhamelSolution F f g G) := continuous_waveDuhamelSolution f g hG
  refine ⟨fun heq φ t ht ↦ ?_, fun h ↦ ?_⟩
  · have hsub := Set.OrdConnected.uIcc_subset ‹_› h0 ht
    rw [heq ht, inner_toLp_waveDuhamelSolution φ f g hG t]
    congr 1
    exact intervalIntegral.integral_congr fun r hr ↦ by simp only [heq (hsub hr)]
  -- The difference of `u` and Duhamel's formula is a weak solution with zero data.
  have hzero := eqOn_zero_of_forall_inner_toLp_eq_integral_smul_inner_toLp_laplacian h0
    (hu.sub hU.continuousOn) fun φ t ht ↦ ?_
  · exact fun t ht ↦ sub_eq_zero.1 (hzero ht)
  have hsub := Set.OrdConnected.uIcc_subset ‹_› h0 ht
  have hint {v : ℝ → Lp F 2 (volume : Measure E)} (hv : ContinuousOn v (uIcc 0 t)) :
      IntervalIntegrable (fun r ↦ (t - r) • (⟪(Δ φ).toLp 2, v r⟫ + ⟪φ.toLp 2, G r⟫)) volume 0 t :=
    ((continuous_const.sub continuous_id).continuousOn.smul ((continuousOn_const.inner hv).add
      (continuous_const.inner hG).continuousOn)).intervalIntegrable
  rw [Pi.sub_apply, inner_sub_right, h φ t ht, inner_toLp_waveDuhamelSolution φ f g hG t,
    add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hint (hu.mono hsub))
      (hint hU.continuousOn)]
  refine intervalIntegral.integral_congr fun r _ ↦ ?_
  simp only [Pi.sub_apply, inner_sub_right, ← smul_sub]
  abel_nf

end TauCeti
