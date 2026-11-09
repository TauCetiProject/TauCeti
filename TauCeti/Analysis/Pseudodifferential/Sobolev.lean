/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Sobolev mapping of pseudodifferential operators with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) that vanishes for positions
outside a compact set, with values in operators between complex Hilbert spaces `V` and `W`. Its
left quantization `Op(a)`, defined on Schwartz functions by `TauCeti.quantizeSchwartzValue`, extends
to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between Mathlib's Bessel-potential spaces,
for every real `s` (`TauCeti.Symbol.quantizeSobolev`). The order `m` of the symbol is thus the
number of derivatives `Op(a)` loses.

The same holds for finite-dimensional complex normed `V` and `W`, whose norms need not come from
inner products (`TauCeti.Symbol.exists_quantizeSobolev`): isomorphisms with `ℂ^k` and `ℂ^l`
induce isomorphisms of the Bessel-potential spaces (`BesselPotentialSpace.postcomp`) and
conjugate `a` to a symbol between Hilbert spaces (`TauCeti.Symbol.map`).

## The Fourier argument

For a fixed frequency `ξ`, the position slice `x ↦ a(x, ξ)` is smooth with support in a fixed
compact set, so its Fourier transform `â(η, ξ)` decays rapidly in `η`; the symbol estimates in
the position give, for every `N`,
`(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C_N ⟨ξ⟩ ^ m`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`), where
`⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. Taking the Fourier transform of
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` in `x` gives the convolution-type formula
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`). Peetre's inequality
`⟨ξ⟩ ^ (s - m) ≤ 2 ^ (|s - m| / 2) ⟨ξ - ζ⟩ ^ |s - m| ⟨ζ⟩ ^ (s - m)` turns this into the bound
`⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(a) u) ξ‖ ≤ C ∫ k(ξ - ζ) ⟨ζ⟩ ^ s ‖𝓕 u ζ‖ dζ` with an integrable kernel
`k(η) = (1 + ‖η‖) ^ (|s - m| - N)`, `N > n + |s - m|`, and Schur's test bounds the right side in
`L²`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le`).
Since the `H^s` norm is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`, this is the estimate
`‖Op(a) u‖_{H^{s-m}} ≤ C ‖u‖_{H^s}` on Schwartz functions, and density of Schwartz functions in
`H^s` gives the bounded extension.

## Main declarations

* `TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`: rapid
  decay of the Fourier transform in the position.
* `TauCeti.Symbol.HasCompactSpatialSupport.fourier_spatialDeriv`: the Fourier transform of a
  position derivative is `2πi θ_j â(θ, ξ)`.
* `TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`: the Fourier transform
  of `Op(a) u`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le`:
  the Sobolev estimate on Schwartz functions, on the Fourier side.
* `TauCeti.Symbol.quantizeSobolev`: the bounded operator `H^s → H^{s - m}`, with
  `TauCeti.Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply` identifying its values
  on Schwartz functions.
* `TauCeti.Symbol.exists_quantizeSobolev`: the mapping property for finite-dimensional normed
  `V` and `W`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace RealInnerProductSpace ContDiff
  LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Decay

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-! ### Rapid decay of the Fourier transform in the position -/

/-- The Schwartz seminorms of the position slices of a symbol with compact spatial support grow
at most like `⟨ξ⟩ ^ m`. -/
private theorem HasCompactSpatialSupport.exists_seminorm_slice_le
    (ha : a.HasCompactSpatialSupport) (k l : ℕ) :
    ∃ D, 0 ≤ D ∧ ∀ ξ, SchwartzMap.seminorm ℂ k l
      ((ha.hasCompactSupport_slice ξ).toSchwartzMap (a.contDiff_coefficient_slice ξ)) ≤
        D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  choose C hC0 hC using fun r : Fin l → Fin n ↦ a.exists_bound K hK (List.ofFn r) []
  have hD : 0 ≤ max R 0 ^ k * ∑ r, C r :=
    mul_nonneg (pow_nonneg (le_max_right _ _) _) (Finset.sum_nonneg fun r _ ↦ hC0 r)
  refine ⟨max R 0 ^ k * ∑ r, C r, hD, fun ξ ↦ ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ k l _ (mul_nonneg hD (by positivity)) fun x ↦ ?_
  have hslice : ⇑((ha.hasCompactSupport_slice ξ).toSchwartzMap (a.contDiff_coefficient_slice ξ)) =
      fun y ↦ a.coefficient (y, ξ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [hslice]
  by_cases hx : x ∈ K
  · have hxR : ‖x‖ ≤ max R 0 := (mem_closedBall_zero_iff.mp (hR hx)).trans (le_max_left _ _)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x‖
        ≤ max R 0 ^ k * ∑ r, C r * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
          gcongr
          refine (norm_iteratedFDeriv_le_sum_coordinateDeriv
            ((a.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)) x).trans
              (Finset.sum_le_sum fun r _ ↦ ?_)
          simpa [mixedDeriv_def, coordinateDeriv_nil] using hC r x hx ξ
      _ = max R 0 ^ k * (∑ r, C r) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
          rw [← Finset.sum_mul, mul_assoc]
  · -- Outside `K` the slice vanishes near `x`, so all its derivatives vanish at `x`.
    have hsupp : Function.support (fun y ↦ a.coefficient (y, ξ)) ⊆ K := fun y hy ↦
      by_contra fun h ↦ hy (hKa y h ξ)
    have hzero : iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x = 0 :=
      Function.notMem_support.mp fun hmem ↦
        hx (closure_minimal hsupp hK.isClosed (support_iteratedFDeriv_subset l hmem))
    rw [hzero, norm_zero, mul_zero]
    positivity

/-- **Rapid decay of the Fourier transform in the position.** For a symbol `a` of order `m` with
compact spatial support and every `N`, the Fourier transform `â(η, ξ)` of the position slice
`x ↦ a(x, ξ)` satisfies `(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, uniformly in `η` and `ξ`. -/
theorem HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le
    (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  set g : CoordinateSpace n → 𝓢(CoordinateSpace n, V →L[ℂ] W) := fun ξ ↦
    (ha.hasCompactSupport_slice ξ).toSchwartzMap (a.contDiff_coefficient_slice ξ)
  choose D hD0 hD using fun i : ℕ × ℕ ↦ ha.exists_seminorm_slice_le i.1 i.2
  -- The Fourier transform is continuous on Schwartz space, so each seminorm of `𝓕 (g ξ)` is
  -- bounded by finitely many seminorms of `g ξ`.
  have key (k : ℕ) : ∃ B, 0 ≤ B ∧ ∀ ξ,
      SchwartzMap.seminorm ℂ k 0 (𝓕 (g ξ)) ≤ B * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    have hq : Continuous ((SchwartzMap.seminorm ℂ k 0).comp
        (fourierCLM ℂ 𝓢(CoordinateSpace n, V →L[ℂ] W)).toLinearMap) :=
      ((schwartz_withSeminorms ℂ _ _).continuous_seminorm (k, 0)).comp (fourierCLM ℂ _).continuous
    obtain ⟨s, c, -, hc⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ _ _) _ hq
    have hsum : 0 ≤ ∑ i ∈ s, D i := Finset.sum_nonneg fun i _ ↦ hD0 i
    refine ⟨c * ∑ i ∈ s, D i, mul_nonneg c.2 hsum, fun ξ ↦ ?_⟩
    have h := hc (g ξ)
    simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, smul_apply, NNReal.smul_def,
      smul_eq_mul] at h
    refine h.trans ?_
    rw [mul_assoc]
    gcongr
    refine Seminorm.finset_sup_apply_le (mul_nonneg hsum (by positivity)) fun i hi ↦
      (hD i ξ).trans ?_
    gcongr
    exact Finset.single_le_sum (fun j _ ↦ hD0 j) hi
  obtain ⟨B₀, hB₀, h₀⟩ := key 0
  obtain ⟨B₁, hB₁, h₁⟩ := key N
  refine ⟨2 ^ N * (B₀ + B₁), by positivity, fun η ξ ↦ ?_⟩
  have hF : 𝓕 (fun x ↦ a.coefficient (x, ξ)) η = 𝓕 (g ξ) η := by
    rw [SchwartzMap.fourier_coe, funext (HasCompactSupport.toSchwartzMap_toFun _ _)]
  have e₀ : ‖𝓕 (g ξ) η‖ ≤ B₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    (SchwartzMap.norm_le_seminorm ℂ _ η).trans (h₀ ξ)
  have e₁ : ‖η‖ ^ N * ‖𝓕 (g ξ) η‖ ≤ B₁ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    simpa using (SchwartzMap.le_seminorm ℂ N 0 (𝓕 (g ξ)) η).trans (h₁ ξ)
  have hpow : (1 + ‖η‖) ^ N ≤ 2 ^ N * (1 + ‖η‖ ^ N) := by
    refine (add_pow_le zero_le_one (norm_nonneg η) N).trans ?_
    rw [one_pow]
    gcongr
    · norm_num
    · exact Nat.sub_le N 1
  rw [hF]
  calc (1 + ‖η‖) ^ N * ‖𝓕 (g ξ) η‖ ≤ 2 ^ N * (1 + ‖η‖ ^ N) * ‖𝓕 (g ξ) η‖ := by gcongr
    _ = 2 ^ N * (‖𝓕 (g ξ) η‖ + ‖η‖ ^ N * ‖𝓕 (g ξ) η‖) := by ring
    _ ≤ 2 ^ N * (B₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) + B₁ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by gcongr
    _ = 2 ^ N * (B₀ + B₁) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

/-- The Fourier transform in the position of the position derivative `∂_{x_j} a` is
`2πi θ_j â(θ, ξ)`. -/
theorem HasCompactSpatialSupport.fourier_spatialDeriv (ha : a.HasCompactSpatialSupport)
    (j : Fin n) (ξ θ : CoordinateSpace n) :
    𝓕 (fun y ↦ (Symbol.spatialDeriv j a).coefficient (y, ξ)) θ =
      (2 * π * Complex.I * θ j) • 𝓕 (fun y ↦ a.coefficient (y, ξ)) θ := by
  set f := (ha.hasCompactSupport_slice ξ).toSchwartzMap (a.contDiff_coefficient_slice ξ)
  have hf : (fun y ↦ a.coefficient (y, ξ)) = ⇑f :=
    (funext (HasCompactSupport.toSchwartzMap_toFun _ _)).symm
  have hdf : (fun y ↦ (Symbol.spatialDeriv j a).coefficient (y, ξ)) =
      ⇑(∂_{EuclideanSpace.single j (1 : ℝ)} f : 𝓢(CoordinateSpace n, V →L[ℂ] W)) := by
    funext y
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, ← hf, ← fderiv_coefficient_single]
  have hg : (fun x : CoordinateSpace n ↦ ⟪x, EuclideanSpace.single j (1 : ℝ)⟫).HasTemperateGrowth :=
    ((innerSL ℝ).flip _).hasTemperateGrowth
  rw [hdf, hf, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe,
    SchwartzMap.fourier_lineDerivOp_eq, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    EuclideanSpace.inner_single_right, smul_comm, ← Complex.coe_smul, smul_smul]
  simp [mul_comm]

end Decay

/-! ### The Fourier transform of the quantization -/

section Quantization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-- The integrand of the double integral giving `𝓕 (Op(a) u) ξ` is integrable in the position
and the frequency: it is dominated by the indicator of the spatial support of `a` times an
integrable function of the frequency. -/
private theorem HasCompactSpatialSupport.integrable_fourierChar_smul_apply
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    Integrable (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪p.1, ξ - p.2⟫) • a.coefficient (p.1, (2 * π) • p.2) (𝓕 u p.2)) (volume.prod volume) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient K hK
  have hFcont : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪p.1, ξ - p.2⟫) • a.coefficient (p.1, (2 * π) • p.2) (𝓕 u p.2) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      ((a.contDiff_coefficient.continuous.comp (by fun_prop)).clm_apply
        ((𝓕 u).continuous.comp continuous_snd))
  have hK1 : Integrable (K.indicator fun _ ↦ (1 : ℝ)) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hg : Integrable fun ζ : CoordinateSpace n ↦
      C * ((2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖)) :=
    (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _).const_mul _
  refine (hK1.mul_prod hg).mono' hFcont.aestronglyMeasurable (.of_forall fun p ↦ ?_)
  by_cases hx : p.1 ∈ K
  · rw [Set.indicator_of_mem hx, one_mul, Circle.norm_smul]
    refine ((a.coefficient _).le_opNorm _).trans ?_
    have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul (c := 2 * π)
      (by linarith [Real.two_le_pi]) m (x := (2 * π) • p.2) (y := p.2)
      (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
    calc ‖a.coefficient (p.1, (2 * π) • p.2)‖ * ‖𝓕 u p.2‖
        ≤ C * (1 + ‖(2 * π) • p.2‖ ^ 2) ^ (m / 2) * ‖𝓕 u p.2‖ := by
          gcongr
          exact hC _ hx _
      _ ≤ C * ((2 * π) ^ |m| * (1 + ‖p.2‖ ^ 2) ^ (m / 2)) * ‖𝓕 u p.2‖ := by gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx, zero_mul]
    simp [hKa p.1 hx]

/-- **The Fourier transform of the quantization.** For a symbol `a` with compact spatial support,
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`, where `â(η, ξ)` is the Fourier transform of the
position slice `x ↦ a(x, ξ)` at `η`. -/
theorem HasCompactSpatialSupport.fourier_quantizeSchwartzValue (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    𝓕 (quantizeSchwartzValue a.coefficient u) ξ =
      ∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  set F : CoordinateSpace n × CoordinateSpace n → W := fun p ↦
    𝐞 (-⟪p.1, ξ - p.2⟫) • a.coefficient (p.1, (2 * π) • p.2) (𝓕 u p.2) with hF
  have hFint : Integrable F (volume.prod volume) := ha.integrable_fourierChar_smul_apply u ξ
  calc 𝓕 (quantizeSchwartzValue a.coefficient u) ξ = ∫ x, ∫ ζ, F (x, ζ) := by
        rw [Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [quantizeSchwartzValue_def, hF]
        rw [Circle.smul_def, ← integral_smul]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [Circle.smul_def, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
        congr 3
        rw [inner_sub_right, real_inner_comm ζ x]
        ring
    _ = ∫ ζ, ∫ x, F (x, ζ) := integral_integral_swap hFint
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        have hint : Integrable fun x ↦ 𝐞 (-⟪x, ξ - ζ⟫) • a.coefficient (x, (2 * π) • ζ) :=
          ((Real.continuous_fourierChar.comp (by fun_prop)).smul
            (a.contDiff_coefficient_slice _).continuous).integrable_of_hasCompactSupport
              (HasCompactSupport.intro hK fun x hx ↦ by simp [hKa x hx, Circle.smul_def])
        dsimp only
        rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hint]
        simp only [hF, Circle.smul_def, smul_apply]

/-- The pointwise kernel bound behind the Sobolev estimate: Peetre's inequality and the decay of
`â` give `⟨ξ⟩ ^ (s - m) ‖â(ξ - ζ, 2πζ) v‖ ≤ B k(ξ - ζ) ⟨ζ⟩ ^ s ‖v‖` with
`k(η) = (1 + ‖η‖) ^ (|s - m| - N)`. -/
private theorem rpow_mul_norm_fourier_apply_le {s C₀ : ℝ} {N : ℕ} (hC₀ : 0 ≤ C₀)
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (ξ ζ : CoordinateSpace n) (v : V) :
    (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
      2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| * (1 + ‖ξ - ζ‖) ^ (-((N : ℝ) - |s - m|)) *
        ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖) := by
  set A := 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ)
  set t := 1 + ‖ξ - ζ‖
  have ht : 0 < t := by positivity
  have hA : ‖A‖ ≤ C₀ * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * (t ^ N)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm]
    exact hdecay _ _
  have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul (c := 2 * π)
    (by linarith [Real.two_le_pi]) m (x := (2 * π) • ζ) (y := ζ)
    (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub (s - m) ξ ζ
  -- The bracket `⟨η⟩ ^ |s - m|` is at most `(1 + ‖η‖) ^ |s - m|`.
  have hbr : (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) ≤ t ^ |s - m| := by
    calc (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) ≤ (t ^ 2) ^ (|s - m| / 2) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg (ξ - ζ)]) (by positivity)
      _ = t ^ |s - m| := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
          norm_num
          ring_nf
  have hk : t ^ |s - m| * (t ^ N)⁻¹ = t ^ (-((N : ℝ) - |s - m|)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    ring_nf
  have hw : (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (m / 2) = (1 + ‖ζ‖ ^ 2) ^ (s / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  calc (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖A v‖
      ≤ (2 ^ (|s - m| / 2) * (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) * (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2)) *
          ((C₀ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * (t ^ N)⁻¹) * ‖v‖) := by
        gcongr
        refine (A.le_opNorm v).trans ?_
        gcongr
        exact hA.trans (by gcongr)
    _ ≤ (2 ^ (|s - m| / 2) * t ^ |s - m| * (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2)) *
          ((C₀ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * (t ^ N)⁻¹) * ‖v‖) := by gcongr
    _ = 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| * (t ^ |s - m| * (t ^ N)⁻¹) *
          (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * ‖v‖) := by ring
    _ = _ := by rw [hk, hw]

/-- The pointwise form of the Sobolev estimate: `⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(a) u) ξ‖` is bounded by the
integral of the kernel `B k(ξ - ζ)` of `rpow_mul_norm_fourier_apply_le` against
`⟨ζ⟩ ^ s ‖𝓕 u ζ‖`. -/
private theorem HasCompactSpatialSupport.enorm_smul_fourier_quantizeSchwartzValue_le
    (ha : a.HasCompactSpatialSupport) {s C₀ : ℝ} {N : ℕ} (hC₀ : 0 ≤ C₀)
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) • 𝓕 (quantizeSchwartzValue a.coefficient u) ξ‖ₑ ≤
      ∫⁻ ζ, ENNReal.ofReal (2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| *
          (1 + ‖ξ - ζ‖) ^ (-((N : ℝ) - |s - m|))) *
        ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ‖ₑ := by
  rw [ha.fourier_quantizeSchwartzValue, enorm_smul]
  calc ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)‖ₑ *
        ‖∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖ₑ
      ≤ ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)‖ₑ *
        ∫⁻ ζ, ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖ₑ := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ζ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) *
          ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖) := by
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun ζ ↦ ?_
        rw [ENNReal.ofReal_mul (by positivity), ofReal_norm, ← ofReal_norm, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
    _ ≤ _ := by
        refine lintegral_mono fun ζ ↦ ?_
        rw [enorm_smul, ← ofReal_norm, ← ofReal_norm, Complex.norm_real,
          Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (rpow_mul_norm_fourier_apply_le hC₀ hdecay ξ ζ (𝓕 u ζ))

/-- **The Sobolev estimate on Schwartz functions.** For a symbol `a` of order `m` with compact
spatial support and every real `s`, there is a constant `C` with
`‖⟨ξ⟩ ^ (s - m) 𝓕 (Op(a) u)‖_{L²} ≤ C ‖⟨ξ⟩ ^ s 𝓕 u‖_{L²}` for every Schwartz function `u`, that
is, `‖Op(a) u‖_{H^{s-m}} ≤ C ‖u‖_{H^s}`. -/
theorem HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
          𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  set N : ℕ := ⌈|s - m|⌉₊ + n + 1
  obtain ⟨C₀, hC₀, hdecay⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le N
  set k : CoordinateSpace n → ℝ := fun η ↦ (1 + ‖η‖) ^ (-((N : ℝ) - |s - m|))
  have hk_int : Integrable k := integrable_one_add_norm (by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    have := Nat.le_ceil |s - m|
    push_cast [N]
    linarith)
  set B := 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m|
  have hB : 0 ≤ B := by positivity
  set A := ENNReal.ofReal (B * ∫ η, k η)
  refine ⟨B * ∫ η, k η, mul_nonneg hB (integral_nonneg fun η ↦ by positivity), fun u ↦ ?_⟩
  -- The pointwise bound by the kernel `B k(ξ - ζ)` acting on `⟨ζ⟩ ^ s ‖𝓕 u ζ‖`.
  have hpt := ha.enorm_smul_fourier_quantizeSchwartzValue_le (s := s) hC₀ hdecay u
  -- Schur's test for the kernel `B k(ξ - ζ)`, whose row and column integrals are `A`.
  have hint : ∫⁻ η, ENNReal.ofReal (B * k η) = A := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hk_int.const_mul B)
      (.of_forall fun η ↦ mul_nonneg hB (Real.rpow_nonneg (by positivity) _)), integral_const_mul]
  have hkcont : Continuous k :=
    (continuous_const.add continuous_norm).rpow_const fun x ↦
      Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)).ne'
  have hkmeas : AEMeasurable (Function.uncurry fun x y : CoordinateSpace n ↦
      ENNReal.ofReal (B * k (x - y))) (volume.prod volume) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul
      (hkcont.comp (continuous_fst.sub continuous_snd)))).measurable.aemeasurable
  have hw (r : ℝ) : Continuous fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) :=
    (by fun_prop : (fun x : CoordinateSpace n ↦
      (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth).1.continuous
  have hgmeas : AEStronglyMeasurable
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ) :=
    ((hw s).smul (𝓕 u).continuous).aestronglyMeasurable
  have hschur := TauCeti.eLpNorm_lintegral_mul_le hkmeas hgmeas.enorm
    (p := 2) one_le_two (A := A) (B := A)
    (.of_forall fun x ↦ (lintegral_sub_left_eq_self (fun η ↦ ENNReal.ofReal (B * k η)) x).trans
      hint |>.le)
    (.of_forall fun y ↦ (lintegral_sub_right_eq_self (fun η ↦ ENNReal.ofReal (B * k η)) y).trans
      hint |>.le)
  calc _ ≤ eLpNorm (fun ξ ↦ ∫⁻ ζ, ENNReal.ofReal (B * k (ξ - ζ)) *
          ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ‖ₑ) 2 volume :=
        eLpNorm_mono_enorm ((hw (s - m)).smul
          (ha.integrable_quantizeSchwartzValue u).continuous_fourier).aestronglyMeasurable
          fun ξ ↦ by rw [enorm_eq_self]; exact hpt ξ
    _ ≤ _ := hschur
    _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), eLpNorm_enorm _ hgmeas,
          sub_add_cancel, ENNReal.rpow_one]

end Quantization

/-! ### The bounded operator on Bessel-potential spaces -/

section Sobolev

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- The quantization of a symbol with compact spatial support, as a linear map from Schwartz
functions to `L²`. -/
private def HasCompactSpatialSupport.quantizeLp (ha : a.HasCompactSpatialSupport) :
    𝓢(CoordinateSpace n, V) →ₗ[ℂ] Lp W 2 (volume : Measure (CoordinateSpace n)) where
  toFun u := (ha.memLp_quantizeSchwartzValue u 2).toLp _
  map_add' u v := by
    obtain ⟨C, -, hC⟩ := isUniform_iff.mp ha.isUniform [] []
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (.of_forall fun x ↦ ?_)
    exact quantizeSchwartzValue_add_right (a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (fun ξ ↦ by simpa using hC x ξ) u v
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ quantizeSchwartzValue_smul_right c u)

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.quantizeLp_apply (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) :
    ha.quantizeLp u = (ha.memLp_quantizeSchwartzValue u 2).toLp _ :=
  (rfl)

omit [CompleteSpace V] in
/-- The weighted Fourier transform of the quantization is the tempered distribution of the
`L²` function `⟨ξ⟩ ^ r 𝓕 (Op(a) u)`, whenever the latter lies in `L²`. -/
private theorem HasCompactSpatialSupport.smulLeftCLM_fourier_quantizeLp
    (ha : a.HasCompactSpatialSupport) (r : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (hG : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) •
      𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2) :
    smulLeftCLM W (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
        (𝓕 (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W))) =
      (hG.toLp _ : 𝓢'(CoordinateSpace n, W)) := by
  ext φ
  rw [smulLeftCLM_apply_apply, ha.quantizeLp_apply,
    Lp.fourier_toTemperedDistribution_apply _ (ha.integrable_quantizeSchwartzValue u)
      (MemLp.coeFn_toLp _),
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ((hG.coeFn_toLp).mono fun ξ hξ ↦ ?_)
  dsimp only
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), smul_eq_mul, mul_comm, mul_smul]

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.memLp_smul_fourier_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
      𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 := by
  obtain ⟨C, -, hC⟩ := ha.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le s
  exact (hC u).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier s u 2))

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.memSobolev_quantizeLp (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    MemSobolev (s - m) 2 (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W)) :=
  memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨_, ha.smulLeftCLM_fourier_quantizeLp (s - m) u
    (ha.memLp_smul_fourier_quantizeSchwartzValue s u)⟩

omit [CompleteSpace V] in
/-- The quantization of a symbol of order `m` with compact spatial support, as a linear map from
Schwartz functions to `H^{s - m}`. -/
private def HasCompactSpatialSupport.quantizeBessel (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    𝓢(CoordinateSpace n, V) →ₗ[ℂ] H^{s - m}(CoordinateSpace n, W) where
  toFun u := (ha.memSobolev_quantizeLp s u).toBesselPotentialSpace
  map_add' u v := BesselPotentialSpace.ext (by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, BesselPotentialSpace.toDistr_add,
      map_add]
    exact (Lp.toTemperedDistributionCLM W volume 2).map_add _ _)
  map_smul' c u := BesselPotentialSpace.ext (by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, BesselPotentialSpace.toDistr_smul,
      map_smul, RingHom.id_apply]
    exact (Lp.toTemperedDistributionCLM W volume 2).map_smul _ _)

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.toDistr_quantizeBessel (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    (ha.quantizeBessel s u).toDistr = (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W)) :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- On Schwartz functions the quantization is bounded from `H^s` to `H^{s - m}`. -/
private theorem HasCompactSpatialSupport.exists_norm_quantizeBessel_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖ha.quantizeBessel s u‖ ≤ C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le s
  refine ⟨C, fun u ↦ ?_⟩
  have hG := ha.memLp_smul_fourier_quantizeSchwartzValue s u
  rw [BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq
      ((ha.toDistr_quantizeBessel s u).symm ▸ ha.smulLeftCLM_fourier_quantizeLp (s - m) u hG),
    Lp.norm_toLp, SchwartzMap.norm_toBesselPotentialSpaceCLM, ← ENNReal.toReal_ofReal hC0,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier s u 2).eLpNorm_ne_top) (hC u)

/-- **Sobolev mapping of pseudodifferential operators with compact spatial support.** The left
quantization `Op(a)` of a symbol `a` of order `m` with compact spatial support extends from
Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between Bessel-potential
spaces, for every real `s`. On a Schwartz function `u` it is the tempered distribution of the
function `Op(a) u` (`TauCeti.Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply`), and
it is the unique continuous linear map with this property
(`BesselPotentialSpace.continuousLinearMap_ext`). -/
def quantizeSobolev (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  (ha.quantizeBessel s).extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

/-- On a Schwartz function `u`, the operator `Op(a) : H^s → H^{s - m}` gives the tempered
distribution of the function `Op(a) u = quantizeSchwartzValue a.coefficient u`. -/
@[simp]
theorem toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  obtain ⟨C, hC⟩ := ha.exists_norm_quantizeBessel_le s
  have h := LinearMap.extendOfNorm_eq (f := ha.quantizeBessel s)
    (e := (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap)
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM s ENNReal.ofNat_ne_top) ⟨C, hC⟩ u
  rw [ContinuousLinearMap.coe_coe] at h
  rw [quantizeSobolev, h, ha.toDistr_quantizeBessel, ha.quantizeLp_apply,
    Lp.toTemperedDistribution_apply]
  exact integral_congr_ae ((ha.memLp_quantizeSchwartzValue u 2).coeFn_toLp.mono fun x hx ↦ by
    simp only [hx])

end Sobolev

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev mapping of pseudodifferential operators with compact spatial support.** For a
symbol `a` of order `m` with compact spatial support between finite-dimensional complex normed
spaces and every real `s`, the quantization `Op(a)` extends from Schwartz functions to a bounded
operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`.

The norms of `V` and `W` need not come from inner products: isomorphisms `e₁ : V ≃L[ℂ] ℂ^k`,
`e₂ : W ≃L[ℂ] ℂ^l` induce isomorphisms of the Bessel-potential spaces
(`BesselPotentialSpace.postcomp`), and the operator is `e₂⁻¹ ∘ Op(e₂ a e₁⁻¹) ∘ e₁` with the
Hilbert-space operator `TauCeti.Symbol.quantizeSobolev`
(`TauCeti.quantizeSchwartzValue_arrowCongr`). -/
theorem exists_quantizeSobolev (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  refine ⟨BesselPotentialSpace.postcomp _ _ 2 (e₂.symm : _ →L[ℂ] W) ∘L
    (a.map Φ).quantizeSobolev (ha.map Φ) s ∘L BesselPotentialSpace.postcomp _ s 2 (e₁ : V →L[ℂ] _),
    fun u φ ↦ ?_⟩
  have hc : (a.map Φ).coefficient = fun p ↦ e₁.arrowCongr e₂ (a.coefficient p) :=
    funext fun p ↦ by simp [Φ]
  have hq (x : CoordinateSpace n) :
      quantizeSchwartzValue (a.map Φ).coefficient (u.postcompCLM (e₁ : V →L[ℂ] _)) x =
        e₂ (quantizeSchwartzValue a.coefficient u x) := by
    rw [hc, quantizeSchwartzValue_arrowCongr]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    BesselPotentialSpace.toDistr_postcomp_apply,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  simp only [hq, ← map_smul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

end FiniteDimensional

end Symbol

end TauCeti
