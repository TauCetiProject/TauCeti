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

The wave front set of `Op(a) v` also avoids every covector near which `a` vanishes conically at
large frequencies: if `a(x, ξ) = 0` for `x` in a neighbourhood `U` of `x₀` and `ξ` of norm at least
`R` in an open cone `Γ` containing `ξ₀`, then `(x₀, ξ₀) ∉ WF(Op(a) v)` for every `v ∈ H^t`
(`TauCeti.Symbol.notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero`). Applied to
`ψ (1 - c)` for a cutoff `ψ` near `x₀`, this shows that an operator `Op(c)` whose symbol equals `1`
at large frequencies on `U × Γ` is microlocally the identity there:
`WF(Op(c) v) ∩ (U × Γ) = WF(v) ∩ (U × Γ)`. This is the step of microlocal elliptic regularity
which recovers the singularities of `v` from those of `Op(c) v`, for `Op(c)` the composition of a
microlocal parametrix with the elliptic operator.

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

If instead `a` vanishes on `U × Γ` at frequencies of norm at least `R`, then `b = ψ a` vanishes on
`Γ` at those frequencies at every position, so `b̂(·, 2πζ) = 0` for such `ζ`, and the same integral
decays rapidly on a smaller cone whatever the regularity of `v`.

## Main results

* `TauCeti.Symbol.toDistr_quantizeSobolev_smulLeftCLM_fourierAtomMulSchwartzMap`: the localized
  Fourier transform of `Op(b) (χ v)`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`: **microlocality**,
  `WF(Op(a) v) ⊆ WF(v)`.
* `TauCeti.Symbol.vectorWaveFrontSet_toDistribution_quantizeSobolev_subset`: microlocality for
  matrix-valued symbols.
* `TauCeti.Symbol.singularSupport_toDistribution_quantizeSobolev_subset`: the singular support of
  `Op(a) v` lies in that of `v`, for matrix-valued symbols between finite-dimensional spaces.
* `TauCeti.Symbol.notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero`,
  `TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset_diff`: **`Op(a)` is smoothing
  where `a` vanishes conically**, `WF(Op(a) v) ⊆ WF(v) \ (U × Γ)`.
* `TauCeti.Symbol.waveFrontSet_toDistribution_inter_subset_quantizeSobolev`,
  `TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_inter_eq`: **`Op(c)` is microlocally
  the identity where `c` is**, `WF(Op(c) v) ∩ (U × Γ) = WF(v) ∩ (U × Γ)`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008, Lecture I,
  Proposition 7.3 (`WF(Pu) ⊆ WF(u)`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (the wave front set and the localization of its decay estimates).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators and wave front sets, including the inclusion
  `WF(Au) ⊆ WF(u) ∩ WF(A)` in terms of the conic support `WF(A)` of the symbol).
-/

public section

noncomputable section

open Complex MeasureTheory Filter Set TopologicalSpace TestFunction TemperedDistribution
  FourierTransform Metric Distribution
open scoped Distributions SchwartzMap BesselPotentialSpace Topology ContDiff RealInnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- The frequencies near a large `η` in a narrower cone. If the closed balls of radius `c ‖η‖`
about the points `η` of `Γ'` lie in `Γ`, then for `‖η‖ ≥ R / π` the closed ball of radius
`min c (1 / 2) * ‖η‖` consists of frequencies `ζ ∈ Γ` with `‖2π ζ‖ ≥ R`. -/
private theorem closedBall_subset_of_le_norm {Γ Γ' : Set (CoordinateSpace n)} {c : ℝ}
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {R : ℝ} :
    ∀ η ∈ Γ' ∩ {η | R / Real.pi ≤ ‖η‖},
      closedBall η (min c (1 / 2) * ‖η‖) ⊆ {ζ | ζ ∈ Γ ∧ R ≤ ‖(2 * Real.pi) • ζ‖} := by
  rintro η ⟨hη, hηR⟩ ζ hζ
  refine ⟨hΓ' η hη (closedBall_subset_closedBall (by gcongr; exact min_le_left _ _) hζ), ?_⟩
  have hζη : ‖ζ - η‖ ≤ ‖η‖ / 2 := (mem_closedBall_iff_norm.1 hζ).trans (by
    nlinarith [min_le_right c (1 / 2), norm_nonneg η])
  have hζ' : ‖η‖ / 2 ≤ ‖ζ‖ := by
    have := norm_sub_norm_le η ζ
    rw [norm_sub_rev] at hζη
    linarith
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [mem_ofPred_eq, div_le_iff₀ Real.pi_pos] at hηR
  nlinarith [Real.pi_pos]

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

section LocalizedSymbol

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

include hbK hθ in
/-- **Microlocal smoothness of `Op(b) (θ v)` where `b` vanishes conically.** If `b` vanishes
outside `K`, the cutoff `θ` equals `1` on `K` and `θ x₀ ≠ 0`, and `b(x, ζ) = 0` for every position
`x` and every frequency `ζ` of norm at least `R` in an open cone `Γ`, then `Op(b) (θ v)` is
microlocally smooth at `(x₀, ξ)` for every `ξ ∈ Γ`, whatever `v ∈ H^t`. -/
private theorem isMicrolocallySmoothAt_toDistribution_quantizeSobolev_smulLeftCLM_of_eq_zero
    (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ)) {x₀ ξ : CoordinateSpace n} (hθx₀ : θ x₀ ≠ 0)
    {Γ : Set (CoordinateSpace n)} (hΓ : IsOpen Γ) (hξ : ξ ∈ Γ)
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (hbΓ : ∀ x, ∀ ζ ∈ Γ, R ≤ ‖ζ‖ → b.coefficient (x, ζ) = 0) :
    (toDistribution ⊤ (b.quantizeSobolev hb t
      (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ θ) v)).toDistr).IsMicrolocallySmoothAt
        x₀ ξ := by
  obtain ⟨Γ', hΓ'o, hξΓ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  refine isMicrolocallySmoothAt_iff.2 ⟨θ, hθx₀, Γ', hΓ'o, hξΓ', hcone', fun N ↦ ?_⟩
  -- The kernel `b̂(·, 2πζ)` vanishes for `ζ ∈ Γ₁`, so the localized Fourier transform `w` of `v`
  -- may be replaced by `F`, which vanishes on `Γ₁` and so decays rapidly there.
  set Γ₁ : Set (CoordinateSpace n) := {ζ | ζ ∈ Γ ∧ R ≤ ‖(2 * Real.pi) • ζ‖}
  set w : CoordinateSpace n → ℂ := fun ζ ↦ v.toDistr (θ.fourierAtomMulSchwartzMap ζ)
  set F := Γ₁ᶜ.indicator w
  have hwF (η ζ : CoordinateSpace n) :
      𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ) (w ζ) =
        𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) (η - ζ) (F ζ) := by
    by_cases hζ : ζ ∈ Γ₁
    · have h0 : (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) = 0 :=
        funext fun x ↦ hbΓ x _ (hcone _ (by positivity) ζ hζ.1) hζ.2
      simp [h0, Real.fourier_eq, Circle.smul_def]
    · simp [F, hζ]
  obtain ⟨C₀, k, hC₀⟩ := (toDistribution ⊤ v.toDistr).exists_norm_localFourier_le θ
  simp only [localFourier_toDistribution] at hC₀
  have hF (ζ : CoordinateSpace n) : ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k :=
    (norm_indicator_le_norm_self w ζ).trans (hC₀ ζ)
  -- Rapid decay on the part of `Γ'` at frequencies of norm at least `R / π`.
  have hsub : ∀ η ∈ Γ' ∩ {η | R / Real.pi ≤ ‖η‖}, closedBall η (min c (1 / 2) * ‖η‖) ⊆ Γ₁ :=
    closedBall_subset_of_le_norm hΓ'
  obtain ⟨C₁, hC₁⟩ := exists_one_add_norm_pow_mul_norm_integral_le (μ := volume)
    (K := fun θ' ζ ↦ 𝓕 (fun x ↦ b.coefficient (x, (2 * Real.pi) • ζ)) θ')
    hb.exists_one_add_norm_pow_mul_norm_fourier_two_pi_le hF (lt_min hc one_half_pos) hsub
    (N := N) ⟨0, fun η hη ↦ by simp [F, hη]⟩
  -- Bounded frequencies are handled by the polynomial growth of the localized Fourier transform.
  obtain ⟨C₂, k₂, hC₂⟩ := exists_norm_localFourier_le (toDistribution ⊤ (b.quantizeSobolev hb t
    (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ θ) v)).toDistr) θ
  refine ⟨max C₁ (|C₂| * (1 + |R / Real.pi|) ^ (N + k₂)), fun η hη ↦ ?_⟩
  by_cases hηR : R / Real.pi ≤ ‖η‖
  · refine le_max_of_le_left ?_
    rw [localFourier_toDistribution,
      toDistr_quantizeSobolev_smulLeftCLM_fourierAtomMulSchwartzMap hb hbK hθ,
      integral_congr_ae (ae_of_all _ (hwF η))]
    exact hC₁ η ⟨hη, hηR⟩
  · refine le_max_of_le_right ?_
    calc _ ≤ (1 + ‖η‖) ^ N * (|C₂| * (1 + ‖η‖) ^ k₂) := by
          gcongr
          exact (hC₂ η).trans (by gcongr; exact le_abs_self _)
      _ = |C₂| * (1 + ‖η‖) ^ (N + k₂) := by ring
      _ ≤ |C₂| * (1 + |R / Real.pi|) ^ (N + k₂) := by
          gcongr
          exact (not_le.1 hηR).le.trans (le_abs_self _)

include hbK in
/-- The splitting behind microlocality. Let `b` vanish outside `K` and agree with `a` on an open
neighbourhood `V₀` of `x₀`, and let the cutoff `χ` equal `1` near `K`. If `Op(b) (χ v)` is
microlocally smooth at `(x₀, ξ)`, then so is `Op(a) v`: the difference consists of a smoothing
operator applied to `v` and of `Op(a - b) v`, which vanishes near `x₀`. -/
private theorem isMicrolocallySmoothAt_toDistribution_quantizeSobolev_of_smulLeftCLM
    {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) {V₀ : Set (CoordinateSpace n)}
    (hV₀ : IsOpen V₀) {x₀ ξ : CoordinateSpace n} (hx₀ : x₀ ∈ V₀)
    (hab : ∀ x ∈ V₀, ∀ ξ, b.coefficient (x, ξ) = a.coefficient (x, ξ))
    (hχK : ∀ᶠ x in 𝓝ˢ K, χ x = 1) (hξ0 : ξ ≠ 0) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    (hA : (toDistribution ⊤ (b.quantizeSobolev hb t
      (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ) v)).toDistr).IsMicrolocallySmoothAt
        x₀ ξ) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).IsMicrolocallySmoothAt x₀ ξ := by
  have hab' : (a - b).HasCompactSpatialSupport := ha.sub hb
  have hdsupp : x₀ ∉ dsupport (toDistribution ⊤ ((a - b).quantizeSobolev hab' t v).toDistr) :=
    fun h ↦ (dsupport_toDistribution_quantizeSobolev_subset hab' hV₀.isClosed_compl
      (fun x hx ξ ↦ by
        rw [coefficient_sub, Pi.sub_apply, hab x (not_not.1 hx), sub_self]) t v h) hx₀
  -- `Op(b) v = Op(b) (χ v) + Op(e) v` with `e` smoothing.
  obtain ⟨e, he, hesm, hbe⟩ :=
    exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add hb hbK
      (hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) χ) (by rwa [coe_toSchwartzMapCLM])
  have hsplit : toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr =
      toDistribution ⊤ (b.quantizeSobolev hb t
        (BesselPotentialSpace.smulLeftCLM t (toSchwartzMapCLM ℂ χ) v)).toDistr +
        toDistribution ⊤ (e.quantizeSobolev he t v).toDistr +
        toDistribution ⊤ ((a - b).quantizeSobolev hab' t v).toDistr := by
    rw [toDistr_quantizeSobolev_sub_apply ha hb hab', hbe t v]
    simp only [map_sub, map_add]
    abel
  -- The smoothing piece lies in every `H^s`, and the last piece vanishes near `x₀`.
  have hE : (toDistribution ⊤ (e.quantizeSobolev he t v).toDistr).IsMicrolocallySmoothAt x₀ ξ := by
    by_contra h
    have hmem : (x₀, ξ) ∈ (toDistribution ⊤ (e.quantizeSobolev he t v).toDistr).waveFrontSet :=
      mem_waveFrontSet_iff.2 ⟨trivial, hξ0, h⟩
    rwa [waveFrontSet_toDistribution_eq_empty fun s ↦
      hesm.memSobolev_toDistr_quantizeSobolev he t s v] at hmem
  rw [hsplit]
  exact (hA.add hE).add (isMicrolocallySmoothAt_of_notMem_dsupport trivial hdsupp ξ)

end LocalizedSymbol

/-! ### Spatial cutoffs and scalar microlocality -/

/-- The cutoffs of the microlocality arguments: inside a neighbourhood `U` of `x₀`, a compact set
`K` with a smooth `ψ` vanishing outside `K` and equal to `1` on an open neighbourhood `V₀` of
`x₀`, and a test function `χ` supported in `U`, equal to `1` near `K`. -/
private theorem exists_cutoffs {x₀ : CoordinateSpace n} {U : Set (CoordinateSpace n)}
    (hU : U ∈ 𝓝 x₀) :
    ∃ (K V₀ : Set (CoordinateSpace n)) (ψ : CoordinateSpace n → ℝ)
      (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)), IsCompact K ∧ K ⊆ U ∧ IsOpen V₀ ∧ x₀ ∈ V₀ ∧
        ContDiff ℝ ∞ ψ ∧ (∀ x ∉ K, ψ x = 0) ∧ (∀ x ∈ V₀, ψ x = 1) ∧
        (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ χ x₀ ≠ 0 ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 hU
  -- `χ = 1` on `ball x₀ (R / 2)` with support in `U`, and `ψ = 1` on `ball x₀ (R / 8)` with
  -- support in `K = closedBall x₀ (R / 4)`.
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
  refine ⟨closedBall x₀ (R / 4), ball x₀ (R / 8), ψ, χ, isCompact_closedBall _ _,
    (closedBall_subset_ball (by linarith)).trans hRU, isOpen_ball, mem_ball_self (by positivity),
    ψ.contDiff, fun x hx ↦ ψ.zero_of_le_dist (le_of_lt (by simpa [ψ] using hx)),
    fun x hx ↦ ψ.one_of_mem_closedBall (ball_subset_closedBall (by simpa [ψ] using hx)),
    Filter.mem_of_superset (isOpen_ball.mem_nhdsSet.2 (closedBall_subset_ball (by linarith)))
      fun y hy ↦ hχ1 y hy, by simp [hχ1 x₀ (mem_ball_self (by positivity))], hχU⟩

/-- The localized symbol of the microlocality arguments: inside a neighbourhood `U` of `x₀`, a
compact set `K` and a symbol `b = ψ a` vanishing outside `K`, vanishing wherever `a` does, and
agreeing with `a` on an open neighbourhood `V₀` of `x₀`, together with a test function `χ`
supported in `U`, equal to `1` near `K`. -/
private theorem exists_localized (a : Symbol n ℂ ℂ m)
    {x₀ : CoordinateSpace n} {U : Set (CoordinateSpace n)} (hU : U ∈ 𝓝 x₀) :
    ∃ (K V₀ : Set (CoordinateSpace n)) (b : Symbol n ℂ ℂ m) (_ : b.HasCompactSpatialSupport)
      (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)), K ⊆ U ∧ IsOpen V₀ ∧ x₀ ∈ V₀ ∧
        (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) ∧
        (∀ x ξ, a.coefficient (x, ξ) = 0 → b.coefficient (x, ξ) = 0) ∧
        (∀ x ∈ V₀, ∀ ξ, b.coefficient (x, ξ) = a.coefficient (x, ξ)) ∧
        (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ χ x₀ ≠ 0 ∧ tsupport χ ⊆ U := by
  obtain ⟨K, V₀, ψ, χ, hK, hKU, hV₀, hx₀, hψ, hψK, hψ1, hχK, hχx₀, hχU⟩ := exists_cutoffs hU
  have hψ' : ContDiff ℝ ∞ fun x ↦ (ψ x : ℂ) := ofRealCLM.contDiff.comp hψ
  have hbK (x) (hx : x ∉ K) (ξ) : (smulLeft hψ' a).coefficient (x, ξ) = 0 := by
    simp [hψK x hx]
  exact ⟨K, V₀, smulLeft hψ' a, hasCompactSpatialSupport_iff.2 ⟨K, hK, hbK⟩, χ, hKU, hV₀, hx₀, hbK,
    fun x ξ h ↦ by simp [h], fun x hx ξ ↦ by simp [hψ1 x hx],
    hχK, hχx₀, hχU⟩

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
  -- Cones and a neighbourhood `U` of `x₀` on which `v` is microlocally smooth.
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, hdecay⟩ := hv.exists_nhds_cone
  obtain ⟨Γ', hΓ'o, hξΓ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξΓ
  -- Split off `b = ψ a`, which agrees with `a` on `V₀`.
  obtain ⟨K, V₀, b, hb, χ, -, hV₀, hx₀, hbK, -, hba, hχK, hχx₀, hχU⟩ := exists_localized a hU
  exact isMicrolocallySmoothAt_toDistribution_quantizeSobolev_of_smulLeftCLM hb hbK χ ha hV₀ hx₀
    hba hχK hξ₀ t v
    (isMicrolocallySmoothAt_toDistribution_quantizeSobolev_smulLeftCLM hb hbK
      (fun x hx ↦ hχK.self_of_nhdsSet x hx) t v hχx₀ hΓ'o hξΓ' hcone' hc hΓ'
      fun N ↦ by simpa only [localFourier_toDistribution] using hdecay χ hχU N)

/-- **Pseudodifferential operators are smoothing where their symbol vanishes conically.** Let `a`
be a scalar symbol with compact spatial support which vanishes at large frequencies conically near
`(x₀, ξ₀)`: `a(x, ξ) = 0` for `x` in a neighbourhood `U` of `x₀` and `ξ` of norm at least `R` in
an open cone `Γ` containing `ξ₀`. Then `(x₀, ξ₀)` does not lie in the wave front set of `Op(a) v`,
for every `v ∈ H^t`. No regularity of `v` is needed. -/
theorem notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero {a : Symbol n ℂ ℂ m}
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    {x₀ ξ₀ : CoordinateSpace n} {U Γ : Set (CoordinateSpace n)} (hU : U ∈ 𝓝 x₀) (hΓ : IsOpen Γ)
    (hξ₀ : ξ₀ ∈ Γ) (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (haΓ : ∀ x ∈ U, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → a.coefficient (x, ξ) = 0) :
    (x₀, ξ₀) ∉ (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet := by
  intro hp
  obtain ⟨-, hξ0, hnot⟩ := mem_waveFrontSet_iff.1 hp
  -- `b = ψ a` agrees with `a` on `V₀` and vanishes on `Γ` at large frequencies, at every position.
  obtain ⟨K, V₀, b, hb, χ, hKU, hV₀, hx₀, hbK, hb0, hba, hχK, hχx₀, -⟩ := exists_localized a hU
  have hbΓ : ∀ x, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → b.coefficient (x, ξ) = 0 := fun x ξ hξ hR ↦ by
    by_cases hx : x ∈ K
    · exact hb0 x ξ (haΓ x (hKU hx) ξ hξ hR)
    · exact hbK x hx ξ
  exact hnot (isMicrolocallySmoothAt_toDistribution_quantizeSobolev_of_smulLeftCLM hb hbK χ ha hV₀
    hx₀ hba hχK hξ0 t v
    (isMicrolocallySmoothAt_toDistribution_quantizeSobolev_smulLeftCLM_of_eq_zero hb hbK
      (fun x hx ↦ hχK.self_of_nhdsSet x hx) t v hχx₀ hΓ hξ₀ hcone hbΓ))

/-- **Microlocality with the conic support of the symbol.** If the scalar symbol `a` with compact
spatial support vanishes at large frequencies on `U × Γ`, for an open set `U` of positions and an
open cone `Γ`, then for every `v ∈ H^t` the wave front set of `Op(a) v` lies in that of `v` and
avoids `U × Γ`. -/
theorem waveFrontSet_toDistribution_quantizeSobolev_subset_diff {a : Symbol n ℂ ℂ m}
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    {U Γ : Set (CoordinateSpace n)} (hU : IsOpen U) (hΓ : IsOpen Γ)
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (haΓ : ∀ x ∈ U, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → a.coefficient (x, ξ) = 0) :
    (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).waveFrontSet ⊆
      (toDistribution ⊤ v.toDistr).waveFrontSet \ U ×ˢ Γ :=
  fun _ hp ↦ ⟨waveFrontSet_toDistribution_quantizeSobolev_subset ha t v hp, fun hpUΓ ↦
    notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero ha t v (hU.mem_nhds hpUΓ.1) hΓ
      hpUΓ.2 hcone haΓ hp⟩

/-- If the scalar symbol `c` equals `1` at large frequencies on `U × Γ`, with `U` a neighbourhood of
`x₀` and `Γ` an open cone containing `ξ₀ ≠ 0`, then for a compactly supported Schwartz function `ψ`
and the symbol `b = ψ c`, the difference `ψ v - Op(b) v = Op(ψ (1 - c)) v` is microlocally smooth
at `(x₀, ξ₀)`. -/
private theorem exists_isMicrolocallySmoothAt_smulLeftCLM_sub (c : Symbol n ℂ ℂ m)
    {ψ : 𝓢(CoordinateSpace n, ℂ)} (hψ : HasCompactSupport ψ)
    (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ)) {x₀ ξ₀ : CoordinateSpace n}
    {U Γ : Set (CoordinateSpace n)} (hU : U ∈ 𝓝 x₀) (hΓ : IsOpen Γ) (hξ₀ : ξ₀ ∈ Γ)
    (hξ0 : ξ₀ ≠ 0) (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (hcΓ : ∀ x ∈ U, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → c.coefficient (x, ξ) = ContinuousLinearMap.id ℂ ℂ) :
    ∃ (b : Symbol n ℂ ℂ m) (hb : b.HasCompactSpatialSupport),
      (∀ x ξ, b.coefficient (x, ξ) = ψ x • c.coefficient (x, ξ)) ∧
      (toDistribution ⊤ ((BesselPotentialSpace.smulLeftCLM t ψ v).toDistr -
        (b.quantizeSobolev hb t v).toDistr)).IsMicrolocallySmoothAt x₀ ξ₀ := by
  -- The symbols `ψ`, `b = ψ c` and `d = ψ - ψ c`, the last two of order `max 0 m`.
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := ℂ) hψ
  have hb := hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ c
  have hF' := hF.of_coefficient_eq (coefficient_inclusion (le_max_left 0 m) _)
  have hb' := hb.of_coefficient_eq (coefficient_inclusion (le_max_right 0 m) _)
  have hd := hF'.sub hb'
  refine ⟨_, hb, fun x ξ ↦ coefficient_smulLeft _ c (x, ξ), ?_⟩
  rw [← toDistr_quantizeSobolev_ofSpatial_smul_id ψ hF,
    ← toDistr_quantizeSobolev_congr (coefficient_inclusion _ _) hF' hF rfl,
    ← toDistr_quantizeSobolev_congr (coefficient_inclusion _ _) hb' hb rfl,
    ← toDistr_quantizeSobolev_sub_apply hF' hb' hd]
  -- `d = ψ (1 - c)` vanishes on `U × Γ` at large frequencies.
  by_contra h
  refine notMem_waveFrontSet_toDistribution_quantizeSobolev_of_eq_zero hd t v hU hΓ hξ₀ hcone
    (R := R) (fun x hx ξ hξ hR ↦ ?_) (mem_waveFrontSet_iff.2 ⟨trivial, hξ0, h⟩)
  simp [hcΓ x hx ξ hξ hR]

/-- **A pseudodifferential operator is microlocally the identity where its symbol is.** If the
scalar symbol `c` with compact spatial support equals `1` at large frequencies on `U × Γ`, for an
open set `U` of positions and an open cone `Γ`, then `Op(c)` does not remove any singularity of
`v ∈ H^t` in `U × Γ`: `WF(v) ∩ (U × Γ) ⊆ WF(Op(c) v)`. -/
theorem waveFrontSet_toDistribution_inter_subset_quantizeSobolev {c : Symbol n ℂ ℂ m}
    (hc : c.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    {U Γ : Set (CoordinateSpace n)} (hU : IsOpen U) (hΓ : IsOpen Γ)
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (hcΓ : ∀ x ∈ U, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → c.coefficient (x, ξ) = ContinuousLinearMap.id ℂ ℂ) :
    (toDistribution ⊤ v.toDistr).waveFrontSet ∩ U ×ˢ Γ ⊆
      (toDistribution ⊤ (c.quantizeSobolev hc t v).toDistr).waveFrontSet := by
  rintro ⟨x₀, ξ₀⟩ ⟨hp, hx₀U, hξ₀Γ⟩
  obtain ⟨-, hξ0, hnot⟩ := mem_waveFrontSet_iff.1 hp
  refine mem_waveFrontSet_iff.2 ⟨trivial, hξ0, fun hcv ↦ hnot ?_⟩
  -- A Schwartz cutoff `ψ` equal to `1` on an open set `O` containing `x₀`.
  obtain ⟨K, V₀, ψ₀, χ, -, -, -, hx₀, -, hψ₀K, hψ₀1, hχK, -, -⟩ :=
    exists_cutoffs (hU.mem_nhds hx₀U)
  obtain ⟨O, hO, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.1 hχK
  have hx₀O : x₀ ∈ O :=
    hKO (by_contra fun h ↦ zero_ne_one ((hψ₀K x₀ h).symm.trans (hψ₀1 x₀ hx₀)))
  set ψ : 𝓢(CoordinateSpace n, ℂ) := toSchwartzMapCLM ℂ χ
  have hψO (x : CoordinateSpace n) (hx : x ∈ O) : ψ x = 1 := by
    simp only [ψ, coe_toSchwartzMapCLM]
    exact hOχ hx
  -- `ψ v - Op(ψ c) v` is smooth microlocally at `(x₀, ξ₀)`, and `e = ψ c - c` vanishes on `O`.
  obtain ⟨b, hb, hbψ, hD⟩ := exists_isMicrolocallySmoothAt_smulLeftCLM_sub c
    (hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) χ) t v (hU.mem_nhds hx₀U) hΓ hξ₀Γ hξ0 hcone hcΓ
  have he := hb.sub hc
  -- `v = Op(c) v + (v - ψ v) + (ψ v - Op(b) v) + Op(e) v`.
  set S := v.toDistr - (BesselPotentialSpace.smulLeftCLM t ψ v).toDistr with hS_def
  have hsplit : toDistribution ⊤ v.toDistr = toDistribution ⊤ (c.quantizeSobolev hc t v).toDistr +
      toDistribution ⊤ S + toDistribution ⊤ ((BesselPotentialSpace.smulLeftCLM t ψ v).toDistr -
        (b.quantizeSobolev hb t v).toDistr) +
      toDistribution ⊤ ((b - c).quantizeSobolev he t v).toDistr := by
    rw [toDistr_quantizeSobolev_sub_apply hb hc he]
    simp only [S, map_sub]
    abel
  have hS : x₀ ∉ dsupport (toDistribution ⊤ S) := fun h ↦ by
    have h' := dsupport_toDistribution_subset S h
    rw [hS_def, BesselPotentialSpace.toDistr_smulLeftCLM] at h'
    exact dsupport_sub_smulLeftCLM_subset v.toDistr ψ.hasTemperateGrowth hO hψO h' hx₀O
  have he0 : x₀ ∉ dsupport (toDistribution ⊤ ((b - c).quantizeSobolev he t v).toDistr) :=
    fun h ↦ (dsupport_toDistribution_quantizeSobolev_subset he hO.isClosed_compl
      (fun x hx ξ ↦ by simp [hbψ, show χ x = 1 from hOχ (not_not.1 hx)]) t v h) hx₀O
  rw [hsplit]
  exact ((hcv.add (isMicrolocallySmoothAt_of_notMem_dsupport trivial hS ξ₀)).add hD).add
    (isMicrolocallySmoothAt_of_notMem_dsupport trivial he0 ξ₀)

/-- **A pseudodifferential operator is microlocally the identity where its symbol is**, as an
equality of wave front sets: if the scalar symbol `c` with compact spatial support equals `1` at
large frequencies on `U × Γ`, then `WF(Op(c) v)` and `WF(v)` agree on `U × Γ`. -/
theorem waveFrontSet_toDistribution_quantizeSobolev_inter_eq {c : Symbol n ℂ ℂ m}
    (hc : c.HasCompactSpatialSupport) (t : ℝ) (v : H^{t}(CoordinateSpace n, ℂ))
    {U Γ : Set (CoordinateSpace n)} (hU : IsOpen U) (hΓ : IsOpen Γ)
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ) {R : ℝ}
    (hcΓ : ∀ x ∈ U, ∀ ξ ∈ Γ, R ≤ ‖ξ‖ → c.coefficient (x, ξ) = ContinuousLinearMap.id ℂ ℂ) :
    (toDistribution ⊤ (c.quantizeSobolev hc t v).toDistr).waveFrontSet ∩ U ×ˢ Γ =
      (toDistribution ⊤ v.toDistr).waveFrontSet ∩ U ×ˢ Γ :=
  (inter_subset_inter_left _ (waveFrontSet_toDistribution_quantizeSobolev_subset hc t v)).antisymm
    (subset_inter (waveFrontSet_toDistribution_inter_subset_quantizeSobolev hc t v hU hΓ hcone hcΓ)
      inter_subset_right)

/-! ### Matrix-valued symbols

A symbol with values in `V →L[ℂ] W` acts on `V`-valued distributions, whose wave front set is the
union of the wave front sets of their components (`Distribution.vectorWaveFrontSet`). The
component of `Op(a) v` along a functional `ℓ` on `W` is a finite sum of scalar operators applied to
the coordinates of `v` in a basis `(e_j)` of `V`: with dual basis `(c_j)`,
`ℓ ∘ Op(a) = ∑ⱼ Op(ℓ ∘ a ∘ e_j) ∘ c_j`. -/

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ V]

/-- **Microlocality of matrix-valued pseudodifferential operators.** Let `a` be a symbol of order
`m` with values in `V →L[ℂ] W` and compact spatial support, where `V` is finite-dimensional. For
every `v ∈ H^t(ℝⁿ; V)`, the wave front set of `Op(a) v` is contained in that of `v`:
`WF(Op(a) v) ⊆ WF(v)`, for the wave front sets of vector-valued distributions. -/
theorem vectorWaveFrontSet_toDistribution_quantizeSobolev_subset [CompleteSpace W]
    {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    haveI : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
    ∀ v : H^{t}(CoordinateSpace n, V),
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).vectorWaveFrontSet ⊆
        (toDistribution ⊤ v.toDistr).vectorWaveFrontSet := by
  intro v
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
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
    {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (t : ℝ) :
    haveI : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
    haveI : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    ∀ v : H^{t}(CoordinateSpace n, V),
      (toDistribution ⊤ (a.quantizeSobolev ha t v).toDistr).singularSupport ⊆
        (toDistribution ⊤ v.toDistr).singularSupport := by
  intro v
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  rw [← fst_image_vectorWaveFrontSet, ← fst_image_vectorWaveFrontSet]
  exact image_mono (vectorWaveFrontSet_toDistribution_quantizeSobolev_subset ha t v)

end Symbol

end TauCeti
