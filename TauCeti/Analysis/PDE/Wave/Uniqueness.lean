/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.WeakSolution
import TauCeti.Analysis.Calculus.Taylor.OrderOne
import TauCeti.Analysis.Fourier.Laplacian.Resolvent
import TauCeti.Analysis.PDE.HeatKernel.Core
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
distributional Laplacian `ψ = Δφ` lies in `L²` (`TauCeti.inner_waveDuhamelSolution`, in
`TauCeti.Analysis.PDE.Wave.WeakSolution`), in particular against every Schwartz function
(`TauCeti.inner_toLp_waveDuhamelSolution`). This file proves the converse: on an order-connected
set of times `s` containing `0`, a function continuous on `s` with values in `L²` satisfies the
weak formulation against Schwartz functions exactly when it agrees on `s` with Duhamel's formula
(`TauCeti.eqOn_waveDuhamelSolution_iff`). So the Cauchy problem has exactly one weak solution in
`C(s; L²)`, and a fortiori in the energy class, where `u` is moreover continuous with values in
`H¹` and continuously differentiable with values in `L²`. The heart of the matter is the case of
zero data and zero forcing
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
* **Smoothing in space.** Let `P = (1 - Δ)⁻¹` and `Q = Δ (1 - Δ)⁻¹`
  (`MeasureTheory.Lp.laplacianResolventCLM`, `MeasureTheory.Lp.laplacianMulResolventCLM`), the
  `L²` Fourier multipliers with the real symbols `(1 + 4π² ‖ξ‖²)⁻¹` and
  `-4π² ‖ξ‖² (1 + 4π² ‖ξ‖²)⁻¹`, both bounded by `1`. Both are self-adjoint, `Δ (P χ) = Q χ` for
  every `χ ∈ L²`, and `P` is injective, since its symbol does not vanish. Testing with `φ = P χ`,
  `ψ = Q χ` for arbitrary `χ` gives the identity `P (w t) = ∫₀ᵗ (t - r) Q (w r) dr` in `L²`.
* **A strong solution.** The right-hand side is twice differentiable in `t` on every compact
  interval of `s` containing `0`, with second derivative `Q (w t) = Δ (P (w t))`, since `Q ∘ w` is
  continuous. So `P ∘ w` is a strong solution of the free wave equation with zero data, and the
  energy uniqueness theorem gives `P (w t) = 0`, hence `w t = 0`.

## Main declarations

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
  have hPs (x y : Lp F 2 (volume : Measure E)) :
      ⟪Lp.laplacianResolventCLM F x, y⟫ = ⟪x, Lp.laplacianResolventCLM F y⟫ :=
    Lp.isSelfAdjoint_laplacianResolventCLM.isSymmetric x y
  have hQs (x y : Lp F 2 (volume : Measure E)) :
      ⟪Lp.laplacianMulResolventCLM F x, y⟫ = ⟪x, Lp.laplacianMulResolventCLM F y⟫ :=
    Lp.isSelfAdjoint_laplacianMulResolventCLM.isSymmetric x y
  have hP (τ : ℝ) (hτ : τ ∈ Icc (0 ⊓ t) (0 ⊔ t)) : Lp.laplacianResolventCLM F (w τ) =
      ∫ r in (0 : ℝ)..τ, (τ - r) • Lp.laplacianMulResolventCLM F (w r) := by
    have hint := intervalIntegral.intervalIntegrable_sub_smul (hwI.mono (uIcc_subset_Icc h0I hτ))
    refine ext_inner_left ℂ fun χ ↦ ?_
    rw [← hPs, h _ _ (Lp.laplacian_laplacianResolventCLM_apply χ) τ (hI hτ), hQs,
      ← (Lp.laplacianMulResolventCLM F).intervalIntegral_comp_comm hint]
    simp only [ContinuousLinearMap.map_smul_of_tower]
  -- So `P ∘ w` is a strong solution of the free wave equation with zero data on `[0 ⊓ t, 0 ⊔ t]`.
  have hQ : ContinuousOn (fun τ ↦ Lp.laplacianMulResolventCLM F (w τ)) (Icc (0 ⊓ t) (0 ⊔ t)) :=
    (Lp.laplacianMulResolventCLM F).continuous.comp_continuousOn hwI
  have hsol : IsWaveSolutionOn (fun τ ↦ Lp.laplacianResolventCLM F (w τ))
      (fun τ ↦ ∫ r in (0 : ℝ)..τ, Lp.laplacianMulResolventCLM F (w r))
      (fun τ ↦ Lp.laplacianMulResolventCLM F (w τ)) 0 (Icc (0 ⊓ t) (0 ⊔ t)) :=
    ⟨fun τ hτ ↦ (intervalIntegral.hasDerivWithinAt_integral_sub_smul hQ h0I hτ).congr
      (fun σ hσ ↦ hP σ hσ) (hP τ hτ),
    fun τ hτ ↦ intervalIntegral.hasDerivWithinAt_integral hQ h0I hτ,
    fun τ _ ↦ by simpa using Lp.laplacian_laplacianResolventCLM_apply (w τ)⟩
  have hzero := hsol.eq_zero h0I (by simp [hP 0 h0I]) (by simp) ⟨inf_le_right, le_sup_right⟩
  exact Lp.laplacianResolventCLM_injective (hzero.trans (map_zero _).symm)

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
  have hint :=
    intervalIntegral.intervalIntegrable_sub_smul (hw.mono (Set.OrdConnected.uIcc_subset ‹_› h0 ht))
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

/-! ### The weak formulation characterizes Duhamel's formula -/

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
    intervalIntegral.intervalIntegrable_sub_smul ((continuousOn_const.inner hv).add
      (continuous_const.inner hG).continuousOn)
  rw [Pi.sub_apply, inner_sub_right, h φ t ht, inner_toLp_waveDuhamelSolution φ f g hG t,
    add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hint (hu.mono hsub))
      (hint hU.continuousOn)]
  refine intervalIntegral.integral_congr fun r _ ↦ ?_
  simp only [Pi.sub_apply, inner_sub_right, ← smul_sub]
  abel_nf

end TauCeti
