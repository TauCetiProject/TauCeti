/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Tempered
public import TauCeti.Analysis.Distribution.WaveFrontSet.VectorValued
public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Sobolev
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.MeasureTheory.Integral.ConicDecay

/-!
# Microlocality of pseudodifferential operators

Let `a` be a scalar symbol of order `m` on `ℝⁿ` with compact spatial support, and `v` an element of
the Bessel-potential space `H^t`. This file proves that the pseudodifferential operator
`Op(a) : H^t → H^{t - m}` does not enlarge the wave front set:

`WF(Op(a) v) ⊆ WF(v)`

(`TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`), where both sides are wave
front sets of the restrictions of tempered distributions to distributions on `ℝⁿ`
(`TemperedDistribution.toDistribution`).

The same holds for a symbol `a` with values in `V →L[ℂ] W`, for a finite-dimensional complex
inner product space `V`, acting on `v ∈ H^t(ℝⁿ; V)`
(`TauCeti.Symbol.vectorWaveFrontSet_toDistribution_quantizeSobolev_subset`), for the wave front
set of vector-valued distributions, the union of the wave front sets of the components
(`Distribution.vectorWaveFrontSet`). This is the form in which operators between vector bundles
appear in local frames. The component of `Op(a) v` along a functional `ℓ` on `W` is
`∑ⱼ Op(ℓ ∘ a ∘ e_j) (c_j v)` for a basis `(e_j)` of `V` with coordinate functionals `(c_j)`
(`TauCeti.Symbol.quantizeSobolev_map`,
`BesselPotentialSpace.sum_postcomp_toSpanSingleton_coord`), so the scalar statement applies to each
term. Projecting to positions, `Op(a)` does not enlarge the singular support when `W` is
finite-dimensional as well (`TauCeti.Symbol.singularSupport_toDistribution_quantizeSobolev_subset`).

## Proof

Let `v` be microlocally smooth at `(x₀, ξ₀)`: for some neighbourhood `U` of `x₀` and an open cone
`Γ` around `ξ₀`, the localized Fourier transform `ζ ↦ v (χ e_ζ)` decays rapidly on `Γ` for every
cutoff `χ` supported in `U`. Choose such a `χ` equal to `1` near `x₀`, a cutoff `ψ` equal to `1`
near `x₀` with `χ = 1` near the support `K` of `ψ`, and split `a = ψ a + (1 - ψ) a`.

* `(1 - ψ) a` vanishes near `x₀`, and `Op((1 - ψ) a) v` is supported where the symbol does not
  vanish (`TauCeti.Symbol.dsupport_toDistribution_quantizeSobolev_subset`), so it vanishes near
  `x₀`.
* For `b = ψ a`, the composition symbol `b # χ` agrees with `b` up to a smoothing symbol, since
  `χ = 1` near the support of `b`. So `Op(b) v = Op(b) (χ v) + Op(e) v` with `e` smoothing
  (`Symbol.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add`),
  and `Op(e) v` lies in every `H^s`, hence has empty wave front set
  (`TemperedDistribution.waveFrontSet_toDistribution_eq_empty`).
* The Fourier transform of the compactly supported distribution `Op(b) (χ v)` is
  `∫ b̂(η - ζ, 2πζ) v (χ e_ζ) dζ`, where `b̂(θ, ξ)` is the Fourier transform of `b` in the position
  (`TauCeti.Symbol.toDistr_quantizeSobolev_smulLeftCLM_fourierAtomMulSchwartzMap`). On Schwartz
  functions this is
  `TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`, and it extends to `H^t`
  by dominated convergence, with the bound `‖v (χ e_ζ)‖ ≤ C ‖v‖ ⟨ζ⟩ ^ (-t)`. Since `b̂(θ, 2πζ)` is
  rapidly decreasing in `θ` with polynomial growth in `ζ`, this integral decays rapidly on a
  smaller cone around `ξ₀` (`TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`).

## Main results

* `TauCeti.Symbol.toDistr_quantizeSobolev_smulLeftCLM_fourierAtomMulSchwartzMap`: the localized
  Fourier transform of `Op(b) (χ v)`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`: **microlocality**,
  `WF(Op(a) v) ⊆ WF(v)`.
* `TauCeti.Symbol.vectorWaveFrontSet_toDistribution_quantizeSobolev_subset`: microlocality for
  matrix-valued symbols.
* `TauCeti.Symbol.singularSupport_toDistribution_quantizeSobolev_subset`: the singular support of
  `Op(a) v` lies in that of `v`, for matrix-valued symbols between finite-dimensional spaces.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008, Lecture I,
  Proposition 7.3 (`WF(Pu) ⊆ WF(u)`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (the wave front set and the localization of its decay estimates).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators and wave front sets).
-/

public section

noncomputable section

open Complex MeasureTheory Filter Set TopologicalSpace TestFunction TemperedDistribution
  FourierTransform Metric Distribution
open scoped Distributions SchwartzMap BesselPotentialSpace Topology ContDiff RealInnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The localized Fourier transform of `Op(b) (χ v)` -/

/-- The Fourier transform `b̂(θ, 2πζ)` of a symbol with compact spatial support in the position is
rapidly decreasing in `θ`, with polynomial growth of degree `⌈|m|⌉₊` in `ζ`. -/
private theorem HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_two_pi_le
    {b : Symbol n ℂ ℂ m} (hb : b.HasCompactSpatialSupport) (j : ℕ) :
    ∃ A, ∀ θ ζ : CoordinateSpace n,
      (1 + ‖θ‖) ^ j * ‖𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) θ‖ ≤
        A * (1 + ‖ζ‖) ^ ⌈|m|⌉₊ := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_one_add_norm_pow_mul_norm_fourier_le j
  obtain ⟨C', hC'⟩ := exists_one_add_norm_smul_sq_rpow_le (E := CoordinateSpace n)
    (c := 2 * Real.pi) (by positivity) (m / 2)
  have hC'0 : 0 ≤ C' := zero_le_one.trans (by simpa using hC' 0)
  refine ⟨C * C', fun θ ζ ↦ ?_⟩
  calc (1 + ‖θ‖) ^ j * ‖𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) θ‖
      ≤ C * (1 + ‖(2 * Real.pi) • ζ‖ ^ 2) ^ (m / 2) := hC θ _
    _ ≤ C * (C' * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) := by gcongr; exact hC' ζ
    _ ≤ C * (C' * (1 + ‖ζ‖) ^ ⌈|m|⌉₊) := by
        gcongr
        exact one_add_norm_sq_rpow_le_one_add_norm_pow_of_le ζ
          ((le_abs_self m).trans (Nat.le_ceil _))
    _ = C * C' * (1 + ‖ζ‖) ^ ⌈|m|⌉₊ := by ring

variable {b : Symbol n ℂ ℂ m} (hb : b.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}
  (hbK : ∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) {θ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
  (hθ : ∀ x ∈ K, θ x = 1) (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ))

include hbK hθ in
/-- The localized Fourier transform of `Op(b) (χ u)` for a Schwartz function `u`. -/
private theorem toDistr_quantizeSobolev_smulLeftCLM_toBesselPotentialSpaceCLM (t : ℝ)
    (u : 𝓢(CoordinateSpace n, ℂ)) (η : CoordinateSpace n) :
    (b.quantizeSobolev hb t (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ)
      (SchwartzMap.toBesselPotentialSpaceCLM t 2 u))).toDistr (θ.fourierAtomMulSchwartzMap η) =
      ∫ ζ, 𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ)
        ((SchwartzMap.toBesselPotentialSpaceCLM t 2 u).toDistr
          (χ.fourierAtomMulSchwartzMap ζ)) := by
  set w := SchwartzMap.smulLeftCLM ℂ (⇑(toSchwartzMapCLM ℂ χ)) u
  have hw : BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ)
      (SchwartzMap.toBesselPotentialSpaceCLM t 2 u) = SchwartzMap.toBesselPotentialSpaceCLM t 2 w :=
    BesselPotentialSpace.ext (by
      rw [BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
        SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
      exact smulLeftCLM_toTemperedDistributionCLM_eq u)
  -- `Op(b) w` vanishes outside `K`, where `θ = 1`, so testing on `θ e_η` is the Fourier transform.
  have hθw (x : CoordinateSpace n) :
      θ.fourierAtomMulSchwartzMap η x • quantizeSchwartzValue b.coefficient w x =
        𝐞 (-⟪x, η⟫) • quantizeSchwartzValue b.coefficient w x := by
    by_cases hx : x ∈ K
    · rw [TestFunction.fourierAtomMulSchwartzMap_apply, hθ x hx, one_mul,
        TauCeti.fourierAtom_eq_fourierChar, Circle.smul_def, smul_eq_mul]
    · simp [quantizeSchwartzValue_def, hbK x hx]
  have hwχ (ζ : CoordinateSpace n) : 𝓕 w ζ =
      (SchwartzMap.toBesselPotentialSpaceCLM t 2 u).toDistr (χ.fourierAtomMulSchwartzMap ζ) := by
    rw [SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      SchwartzMap.toTemperedDistributionCLM_apply_apply volume, SchwartzMap.fourier_coe,
      Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [w, SchwartzMap.smulLeftCLM_apply_apply (toSchwartzMapCLM ℂ χ).hasTemperateGrowth,
      TestFunction.fourierAtomMulSchwartzMap_apply, toSchwartzMapCLM_apply,
      TauCeti.fourierAtom_eq_fourierChar,
      Circle.smul_def, smul_eq_mul]
    ring
  rw [hw, toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  simp only [hθw]
  rw [← Real.fourier_eq, hb.fourier_quantizeSchwartzValue]
  simp only [hwχ]

include hb in
/-- The integrand `b̂(η - ζ, 2πζ) w (χ e_ζ)` is bounded, uniformly over a ball of `H^t`, by an
integrable function of `ζ`. -/
private theorem exists_norm_fourier_apply_toDistr_fourierAtomMulSchwartzMap_le (t : ℝ)
    (η : CoordinateSpace n) :
    ∃ D, 0 ≤ D ∧ ∀ (w : H^{t}(CoordinateSpace n, ℂ)) (ζ : CoordinateSpace n),
      ‖𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ)
          (w.toDistr (χ.fourierAtomMulSchwartzMap ζ))‖ ≤
        D * ‖w‖ * (1 + ‖ζ - η‖) ^ (-((Module.finrank ℝ (CoordinateSpace n) + 1 : ℕ) : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_toDistr_fourierAtomMulSchwartzMap_le t χ
  set M := ⌈|m|⌉₊
  set p := ⌈|t|⌉₊
  set r := Module.finrank ℝ (CoordinateSpace n) + 1
  obtain ⟨A, hA⟩ := hb.exists_one_add_norm_pow_mul_norm_fourier_two_pi_le (r + M + p)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (by simpa using hA 0 0)
  refine ⟨A * C * (1 + ‖η‖) ^ (M + p), by positivity, fun w ζ ↦ ?_⟩
  set k := 𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ)
  have hθpos : 0 < (1 + ‖ζ - η‖) ^ r := by positivity
  have hAζ : (1 + ‖ζ - η‖) ^ (r + M + p) * ‖k‖ ≤ A * (1 + ‖ζ‖) ^ M := by
    simpa only [norm_sub_rev η ζ] using hA (η - ζ) ζ
  have hζ : 1 + ‖ζ‖ ≤ (1 + ‖η‖) * (1 + ‖ζ - η‖) := by
    simpa only [add_sub_cancel] using one_add_norm_add_le η (ζ - η)
  have hmod : ‖w.toDistr (χ.fourierAtomMulSchwartzMap ζ)‖ ≤ C * ‖w‖ * (1 + ‖ζ‖) ^ p :=
    (hC w ζ).trans (by
      gcongr
      exact one_add_norm_sq_rpow_le_one_add_norm_pow_of_le ζ ((neg_le_abs t).trans (Nat.le_ceil _)))
  have hpow : (1 + ‖ζ‖) ^ (M + p) ≤ (1 + ‖η‖) ^ (M + p) * (1 + ‖ζ - η‖) ^ (M + p) := by
    rw [← mul_pow]; gcongr
  rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hθpos]
  calc ‖k (w.toDistr (χ.fourierAtomMulSchwartzMap ζ))‖ * (1 + ‖ζ - η‖) ^ r
      ≤ ‖k‖ * (C * ‖w‖ * (1 + ‖ζ‖) ^ p) * (1 + ‖ζ - η‖) ^ r := by
        gcongr
        exact (k.le_opNorm _).trans (by gcongr)
    _ = C * ‖w‖ * ((1 + ‖ζ - η‖) ^ r * ‖k‖ * (1 + ‖ζ‖) ^ p) := by ring
    _ ≤ C * ‖w‖ * (A * (1 + ‖ζ‖) ^ (M + p) / (1 + ‖ζ - η‖) ^ (M + p)) := by
        gcongr
        rw [le_div_iff₀ (by positivity)]
        calc (1 + ‖ζ - η‖) ^ r * ‖k‖ * (1 + ‖ζ‖) ^ p * (1 + ‖ζ - η‖) ^ (M + p)
            = (1 + ‖ζ - η‖) ^ (r + M + p) * ‖k‖ * (1 + ‖ζ‖) ^ p := by ring
          _ ≤ A * (1 + ‖ζ‖) ^ M * (1 + ‖ζ‖) ^ p := by gcongr
          _ = A * (1 + ‖ζ‖) ^ (M + p) := by ring
    _ ≤ C * ‖w‖ * (A * ((1 + ‖η‖) ^ (M + p) * (1 + ‖ζ - η‖) ^ (M + p)) /
          (1 + ‖ζ - η‖) ^ (M + p)) := by gcongr
    _ = A * C * (1 + ‖η‖) ^ (M + p) * ‖w‖ := by
        rw [← mul_assoc A, mul_div_assoc, div_self (by positivity), mul_one]; ring

include hbK hθ in
/-- **The localized Fourier transform of `Op(b) (χ v)`.** If the symbol `b` vanishes at the
positions outside `K` and the cutoff `θ` equals `1` on `K`, then for every `v ∈ H^t`, testing
`Op(b) (χ v)` on `θ e_η` gives `∫ b̂(η - ζ, 2πζ) v (χ e_ζ) dζ`, where `b̂(·, ξ)` is the Fourier
transform of `b(·, ξ)` and `v (χ e_ζ)` is the localized Fourier transform of `v`. -/
theorem toDistr_quantizeSobolev_smulLeftCLM_fourierAtomMulSchwartzMap (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) (η : CoordinateSpace n) :
    (b.quantizeSobolev hb t (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ) v)).toDistr
        (θ.fourierAtomMulSchwartzMap η) =
      ∫ ζ, 𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ)
        (v.toDistr (χ.fourierAtomMulSchwartzMap ζ)) := by
  -- Both sides are continuous in `v` and agree on Schwartz functions.
  have hLR (u : 𝓢(CoordinateSpace n, ℂ)) :=
    toDistr_quantizeSobolev_smulLeftCLM_toBesselPotentialSpaceCLM hb hbK hθ χ t u η
  have hL : Continuous fun w : H^{t}(CoordinateSpace n, ℂ) ↦
      (b.quantizeSobolev hb t (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ) w)).toDistr
        (θ.fourierAtomMulSchwartzMap η) :=
    ((continuous_eval_const _).comp BesselPotentialSpace.continuous_toDistr).comp
      ((b.quantizeSobolev hb t).continuous.comp (BesselPotentialSpace.smulLeftCLM t _).continuous)
  -- The right side is continuous, by dominated convergence.
  obtain ⟨D, hD0, hD⟩ := exists_norm_fourier_apply_toDistr_fourierAtomMulSchwartzMap_le hb χ t η
  have hk : Continuous fun ζ : CoordinateSpace n ↦
      𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ) :=
    hb.continuous_fourier_slice.comp (f := fun ζ ↦ (η - ζ, (2 * Real.pi) • ζ)) (by fun_prop)
  have hR : Continuous fun w : H^{t}(CoordinateSpace n, ℂ) ↦ ∫ ζ,
      𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ)
        (w.toDistr (χ.fourierAtomMulSchwartzMap ζ)) := by
    refine continuous_iff_continuousAt.2 fun v ↦ ?_
    refine MeasureTheory.continuousAt_of_dominated (bound := fun ζ ↦ D * (‖v‖ + 1) *
        (1 + ‖ζ - η‖) ^ (-((Module.finrank ℝ (CoordinateSpace n) + 1 : ℕ) : ℝ)))
      (Eventually.of_forall fun w ↦ ?_) ?_ ?_ (ae_of_all _ fun ζ ↦ ?_)
    · have hF : Continuous fun ζ ↦ w.toDistr (χ.fourierAtomMulSchwartzMap ζ) :=
        ((toDistribution ⊤ w.toDistr).continuous_localFourier χ).congr
          (localFourier_toDistribution _ χ)
      exact (hk.clm_apply hF).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds v one_pos] with w hw
      refine ae_of_all _ fun ζ ↦ (hD w ζ).trans ?_
      have hw' : ‖w‖ ≤ ‖v‖ + 1 := by
        have := norm_le_norm_add_norm_sub' w v
        rw [mem_ball, dist_eq_norm] at hw
        linarith
      gcongr
    · exact ((integrable_one_add_norm (μ := volume) (E := CoordinateSpace n)
        (by simp)).comp_sub_right η).const_mul _
    · exact ((ContinuousLinearMap.continuous _).comp ((continuous_eval_const
        (χ.fourierAtomMulSchwartzMap ζ)).comp (BesselPotentialSpace.continuous_toDistr
          (E := CoordinateSpace n) (G := ℂ) (s := t) (p := 2)))).continuousAt
  -- Both sides agree on the dense range of Schwartz functions.
  exact congrFun ((SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := (2 : ENNReal)) t
    ENNReal.ofNat_ne_top).equalizer hL hR (funext hLR)) v

include hbK hθ in
/-- **Microlocal smoothness of `Op(b) (θ v)`.** If `b` vanishes outside `K`, the cutoff `θ` equals
`1` on `K` and `θ x₀ ≠ 0`, and the localized Fourier transform `ζ ↦ v (θ e_ζ)` decays rapidly on an
open cone `Γ`, then `Op(b) (θ v)` is microlocally smooth at `(x₀, ξ)` for every `ξ` in an open
cone `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)` lie in `Γ`. -/
private theorem isMicrolocallySmoothAt_toDistribution_quantizeSobolev_smulLeftCLM (t : ℝ)
    (v : H^{t}(CoordinateSpace n, ℂ)) {x₀ ξ : CoordinateSpace n} (hθx₀ : θ x₀ ≠ 0)
    {Γ Γ' : Set (CoordinateSpace n)} (hΓ'o : IsOpen Γ') (hξ : ξ ∈ Γ')
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ', s • η ∈ Γ') {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ η ∈ Γ,
      (1 + ‖η‖) ^ N * ‖v.toDistr (θ.fourierAtomMulSchwartzMap η)‖ ≤ C) :
    (toDistribution ⊤ (b.quantizeSobolev hb t
      (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ θ) v)).toDistr).IsMicrolocallySmoothAt
        x₀ ξ := by
  refine isMicrolocallySmoothAt_iff.2 ⟨θ, hθx₀, Γ', hΓ'o, hξ, hcone, fun N ↦ ?_⟩
  obtain ⟨C₀, k, hC₀⟩ := (toDistribution ⊤ v.toDistr).exists_norm_localFourier_le θ
  simp only [localFourier_toDistribution] at hC₀
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_integral_le (μ := volume)
    (K := fun θ' ζ ↦ 𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) θ')
    (hb.exists_one_add_norm_pow_mul_norm_fourier_two_pi_le) hC₀ hc hΓ' (hdecay _)
  refine ⟨C, fun η hη ↦ ?_⟩
  rw [localFourier_toDistribution,
    toDistr_quantizeSobolev_smulLeftCLM_fourierAtomMulSchwartzMap hb hbK hθ]
  exact hC η hη

omit hb in
/-- The analytic core of microlocality. Let `ψ` be smooth, vanishing outside `K` and equal to `1`
on a neighbourhood `V₀` of `x₀`, and let the cutoff `χ` equal `1` near `K`, with `χ x₀ ≠ 0`. If
the localized Fourier transform `ζ ↦ v (χ e_ζ)` decays rapidly on an open cone `Γ`, then `Op(a) v`
is microlocally smooth at `(x₀, ξ)` for `ξ` in an open cone `Γ'` whose conic neighbourhoods
`closedBall η (c ‖η‖)` lie in `Γ`. -/
private theorem isMicrolocallySmoothAt_toDistribution_quantizeSobolev {a : Symbol n ℂ ℂ m}
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    {x₀ ξ : CoordinateSpace n} {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψK : ∀ x ∉ K, ψ x = 0) {V₀ : Set (CoordinateSpace n)} (hV₀ : IsOpen V₀) (hx₀ : x₀ ∈ V₀)
    (hψ1 : ∀ x ∈ V₀, ψ x = 1) (hχK : ∀ᶠ x in 𝓝ˢ K, χ x = 1) (hχx₀ : χ x₀ ≠ 0)
    (hξ0 : ξ ≠ 0) {Γ Γ' : Set (CoordinateSpace n)} (hΓ'o : IsOpen Γ') (hξ : ξ ∈ Γ')
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ', s • η ∈ Γ') {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ η ∈ Γ,
      (1 + ‖η‖) ^ N * ‖v.toDistr (χ.fourierAtomMulSchwartzMap η)‖ ≤ C) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).IsMicrolocallySmoothAt x₀ ξ := by
  -- `b = ψ a` vanishes outside `K`, and `a - b` vanishes on `V₀`.
  have hψs : ContDiff ℝ ∞ fun x ↦ (ψ x : ℂ) • ContinuousLinearMap.id ℂ ℂ :=
    (ofRealCLM.contDiff.comp hψ).smul contDiff_const
  set Fψ := ofSpatial (fun x ↦ (ψ x : ℂ) • ContinuousLinearMap.id ℂ ℂ) hψs with hFψ
  set b := Fψ.comp a with hbdef
  have hb : b.HasCompactSpatialSupport := ha.comp_left Fψ
  have hbψ (x ξ : CoordinateSpace n) : b.coefficient (x, ξ) =
      ((ψ x : ℂ) • ContinuousLinearMap.id ℂ ℂ).comp (a.coefficient (x, ξ)) := by
    rw [hbdef, coefficient_comp, hFψ, coefficient_ofSpatial]
  have hbK : ∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0 := fun x hx ξ ↦ by
    rw [hbψ, hψK x hx]
    simp
  set a' := Symbol.inclusion (le_of_eq (zero_add m).symm) a
  have ha' : a'.HasCompactSpatialSupport := ha.of_coefficient_eq (coefficient_inclusion _ _)
  have hab : (a' - b).HasCompactSpatialSupport := ha'.sub hb
  have hdsupp : x₀ ∉ dsupport (toDistribution ⊤ ((a' - b).quantizeSobolev hab t v).toDistr) :=
    fun h ↦ (dsupport_toDistribution_quantizeSobolev_subset hab hV₀.isClosed_compl
      (fun x hx ξ ↦ by
        rw [coefficient_sub, Pi.sub_apply, coefficient_inclusion, hbψ, hψ1 x (not_not.1 hx)]
        simp) t v h) hx₀
  -- `Op(b) v = Op(b) (χ v) + Op(e) v` with `e` smoothing.
  obtain ⟨e, he, hesm, hbe⟩ :=
    exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add hb hbK
      (hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) χ) (by rwa [coe_toSchwartzMapCLM])
  have hsplit : toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr =
      toDistribution ⊤ (b.quantizeSobolev hb t
        (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ) v)).toDistr +
        toDistribution ⊤ (e.quantizeSobolev he t v).toDistr +
        toDistribution ⊤ ((a' - b).quantizeSobolev hab t v).toDistr := by
    rw [toDistr_quantizeSobolev_sub_apply ha' hb hab,
      toDistr_quantizeSobolev_congr (coefficient_inclusion _ a) ha' ha rfl, hbe t v]
    simp only [map_sub, map_add]
    abel
  -- The three pieces are microlocally smooth at `(x₀, ξ)`.
  have hA := isMicrolocallySmoothAt_toDistribution_quantizeSobolev_smulLeftCLM hb hbK
    (fun x hx ↦ hχK.self_of_nhdsSet x hx) t v hχx₀ hΓ'o hξ hcone hc hΓ' hdecay
  have hE : (toDistribution ⊤ (e.quantizeSobolev he t v).toDistr).IsMicrolocallySmoothAt x₀ ξ := by
    by_contra h
    have hmem : (x₀, ξ) ∈ (toDistribution ⊤ (e.quantizeSobolev he t v).toDistr).waveFrontSet :=
      mem_waveFrontSet_iff.2 ⟨trivial, hξ0, h⟩
    rwa [waveFrontSet_toDistribution_eq_empty fun s ↦
      hesm.memSobolev_toDistr_quantizeSobolev he t s v] at hmem
  rw [hsplit]
  exact (hA.add hE).add (isMicrolocallySmoothAt_of_notMem_dsupport trivial hdsupp ξ)

omit hb in
/-- **Microlocality of pseudodifferential operators.** For a scalar symbol `a` with compact spatial
support and every `v ∈ H^t`, the wave front set of `Op(a) v` is contained in the wave front set of
`v`: `WF(Op(a) v) ⊆ WF(v)`. -/
theorem waveFrontSet_toDistribution_quantizeSobolev_subset {a : Symbol n ℂ ℂ m}
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ)) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet ⊆
      (toDistribution ⊤ v.toDistr).waveFrontSet := by
  rintro ⟨x₀, ξ₀⟩ hp
  obtain ⟨-, hξ₀, hnot⟩ := mem_waveFrontSet_iff.1 hp
  refine mem_waveFrontSet_iff.2 ⟨trivial, hξ₀, fun hv ↦ hnot ?_⟩
  -- Cones and a neighbourhood `ball x₀ R` on which `v` is microlocally smooth.
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, hdecay⟩ := hv.exists_nhds_cone
  obtain ⟨Γ', hΓ'o, hξΓ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξΓ
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 hU
  -- Cutoffs: `χ = 1` on `ball x₀ (R / 2)` with support in `U`, and `ψ = 1` on `ball x₀ (R / 8)`
  -- with support in `K = closedBall x₀ (R / 4)`.
  let ρ : ContDiffBump x₀ := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  let ψ : ContDiffBump x₀ := ⟨R / 8, R / 4, by positivity, by linarith⟩
  let χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
    ⟨fun x ↦ (ρ x : ℂ), ofRealCLM.contDiff.comp ρ.contDiff,
      ρ.hasCompactSupport.comp_left ofReal_zero, subset_univ _⟩
  have hχx (x : CoordinateSpace n) : χ x = ρ x := (rfl)
  have hχ1 (x : CoordinateSpace n) (hx : x ∈ ball x₀ (R / 2)) : χ x = 1 := by
    simp [hχx, ρ.one_of_mem_closedBall (ball_subset_closedBall hx)]
  have hχU : tsupport χ ⊆ U := by
    refine (tsupport_comp_subset ofReal_zero _).trans ?_
    rw [ρ.tsupport_eq]
    exact (closedBall_subset_ball (by simp [ρ]; linarith)).trans hRU
  exact isMicrolocallySmoothAt_toDistribution_quantizeSobolev (K := closedBall x₀ (R / 4))
    (V₀ := ball x₀ (R / 8)) χ ha t v
    ψ.contDiff (fun x hx ↦ ψ.zero_of_le_dist (le_of_lt (by simpa [ψ] using hx))) isOpen_ball
    (mem_ball_self (by positivity))
    (fun x hx ↦ ψ.one_of_mem_closedBall (ball_subset_closedBall (by simpa [ψ] using hx)))
    (Filter.mem_of_superset (isOpen_ball.mem_nhdsSet.2 (closedBall_subset_ball (by linarith)))
      fun y hy ↦ hχ1 y hy)
    (by simp [hχ1 x₀ (mem_ball_self (by positivity))]) hξ₀ hΓ'o hξΓ' hcone' hc hΓ'
    fun N ↦ by simpa only [localFourier_toDistribution] using hdecay χ hχU N

end Symbol

/-! ### Matrix-valued symbols

A symbol with values in `V →L[ℂ] W` acts on `V`-valued distributions, whose wave front set is the
union of the wave front sets of their components (`Distribution.vectorWaveFrontSet`). The
component of `Op(a) v` along a functional `ℓ` on `W` is a finite sum of scalar operators applied to
the coordinates of `v` in a basis `(e_j)` of `V`: with dual basis `(c_j)`,
`ℓ ∘ Op(a) = ∑ⱼ Op(ℓ ∘ a ∘ e_j) ∘ c_j`. -/

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The map `T ↦ ℓ ∘ T ∘ e` of coefficients, sending an operator `V →L[ℂ] W` to the scalar entry
determined by a vector `e ∈ V` and a functional `ℓ` on `W`. -/
private def entryMap (ℓ : W →L[ℂ] ℂ) (e : V) : (V →L[ℂ] W) →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  ((ContinuousLinearMap.compL ℂ ℂ W ℂ ℓ).comp
    ((ContinuousLinearMap.compL ℂ ℂ V W).flip (ContinuousLinearMap.toSpanSingleton ℂ e))
    ).restrictScalars ℝ

private theorem entryMap_apply (ℓ : W →L[ℂ] ℂ) (e : V) (T : V →L[ℂ] W) :
    entryMap ℓ e T = ℓ ∘L T ∘L ContinuousLinearMap.toSpanSingleton ℂ e :=
  (rfl)

variable [CompleteSpace V] [FiniteDimensional ℂ V] [CompleteSpace W]

/-- **Components of a matrix-valued quantization.** For a functional `ℓ` on `W` and a basis
`(e_j)` of `V` with dual basis `(c_j)`, the component `ℓ ∘ Op(a)` of the quantization of a symbol
`a` with values in `V →L[ℂ] W` is the sum over `j` of the scalar quantizations of the entries
`ℓ ∘ a ∘ e_j`, applied to the coordinates `c_j v`. -/
private theorem postcomp_comp_quantizeSobolev {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V)
    (ℓ : W →L[ℂ] ℂ) (t : ℝ) :
    BesselPotentialSpace.postcomp _ _ 2 ℓ ∘L a.quantizeSobolev ha t =
      ∑ j, (a.map (entryMap ℓ (b j))).quantizeSobolev (ha.map _) t ∘L
        BesselPotentialSpace.postcomp _ t 2 (b.coord j).toContinuousLinearMap := by
  ext1 v
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
    quantizeSobolev_map ha ℓ _ (entryMap_apply ℓ _), ← map_sum,
    BesselPotentialSpace.sum_postcomp_toSpanSingleton_coord]

/-- **Microlocality of matrix-valued pseudodifferential operators.** Let `a` be a symbol of order
`m` with values in `V →L[ℂ] W` and compact spatial support, where `V` is finite-dimensional. For
every `v ∈ H^t(ℝⁿ; V)`, the wave front set of `Op(a) v` is contained in that of `v`:
`WF(Op(a) v) ⊆ WF(v)`, for the wave front sets of vector-valued distributions. -/
theorem vectorWaveFrontSet_toDistribution_quantizeSobolev_subset {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, V)) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).vectorWaveFrontSet ⊆
      (toDistribution ⊤ v.toDistr).vectorWaveFrontSet := by
  let b := Module.finBasis ℂ V
  intro p hp
  obtain ⟨ℓ, hp⟩ := mem_vectorWaveFrontSet_iff.1 hp
  -- The component of `Op(a) v` along `ℓ` is a sum of scalar quantizations of components of `v`.
  have hℓ : mapCLM (ℓ.restrictScalars ℝ) (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr) =
      ∑ j, toDistribution ⊤ ((a.map (entryMap ℓ (b j))).quantizeSobolev (ha.map _) t
        (BesselPotentialSpace.postcomp _ t 2 (b.coord j).toContinuousLinearMap v)
        ).toDistr := by
    have h := congrArg (fun T ↦ toDistribution ⊤ (BesselPotentialSpace.toDistrCLM _ _ _ 2 (T v)))
      (postcomp_comp_quantizeSobolev ha b ℓ t)
    simp only [_root_.sum_apply, map_sum, ContinuousLinearMap.comp_apply,
      BesselPotentialSpace.toDistrCLM_apply] at h
    rw [← h, BesselPotentialSpace.toDistribution_toDistr_postcomp]
  rw [hℓ] at hp
  obtain ⟨j, -, hj⟩ := mem_iUnion₂.1 (waveFrontSet_sum_subset _ _ hp)
  refine waveFrontSet_mapCLM_subset_vectorWaveFrontSet
    (b.coord j).toContinuousLinearMap _ ?_
  -- The coordinates of `v` have wave front sets inside that of `v`.
  rw [← BesselPotentialSpace.toDistribution_toDistr_postcomp]
  exact waveFrontSet_toDistribution_quantizeSobolev_subset _ t _ hj

/-- **Pseudodifferential operators do not enlarge the singular support.** For a symbol `a` with
values in `V →L[ℂ] W` between finite-dimensional spaces and compact spatial support, and every
`v ∈ H^t(ℝⁿ; V)`, the singular support of `Op(a) v` is contained in the singular support of
`v`. -/
theorem singularSupport_toDistribution_quantizeSobolev_subset [FiniteDimensional ℂ W]
    {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (t : ℝ)
    (v : H^{t}(CoordinateSpace n, V)) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).singularSupport ⊆
      (toDistribution ⊤ v.toDistr).singularSupport := by
  rw [← fst_image_vectorWaveFrontSet, ← fst_image_vectorWaveFrontSet]
  exact image_mono (vectorWaveFrontSet_toDistribution_quantizeSobolev_subset ha t v)

end Symbol

end TauCeti
