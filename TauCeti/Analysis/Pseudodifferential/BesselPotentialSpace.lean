/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.Fourier.MihlinHormander
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# Pseudodifferential operators with compact spatial support on `H^{s,p}`

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) that vanishes for positions
outside a compact set, with values in operators between finite-dimensional complex normed spaces
`V` and `W`, and let `1 < p < ∞`. Its left quantization `Op(a)` extends from Schwartz functions to
a bounded operator `H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)` between Mathlib's Bessel-potential spaces,
for every real `s` (`TauCeti.Symbol.quantizeBesselPotentialSpace`). This is the `Lᵖ` form
of the Sobolev mapping theorem `TauCeti.Symbol.exists_quantizeSobolev` for `p = 2`; it is the
estimate behind the `Lᵖ` versions of local elliptic regularity
(`TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace`).

## The argument

Plancherel's theorem, which gives the case `p = 2`, is not available for `p ≠ 2`; the
Mihlin–Hörmander multiplier theorem replaces it. Composition with a frequency multiplier on the
right is exact in the left quantization, so `Op(a) J^{-s} = Op(b)` for the symbol
`b = a ⟨ξ⟩^(-s)` of order `t = m - s` with compact spatial support, where `J^r` is the Bessel
potential. Composition on the left is given by the composition symbol `TauCeti.Symbol.sharp`, so
the estimate to prove is the `Lᵖ` bound for `Op(⟨ξ⟩^(-t) # b) = J^{-t} Op(b)`.

Expanding `b` in its Fourier transform `b̂(η, ξ)` in the position writes this operator as a
superposition of modulated Fourier multipliers,

`Op(⟨ξ⟩^(-t) # b) w (x) = ∫ exp(2πi ⟪η, x⟫) 𝓕⁻ (N_η 𝓕 w) (x) dη`, with
`N_η(ζ) = ⟨ζ + η⟩ ^ (-t) b̂(η, 2πζ)`.

The rapid decay of `b̂` in `η`, its symbol estimates in the frequency
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_le`) and
Peetre's inequality give Mihlin's condition `‖D^k N_η(ζ)‖ ≤ A_η / ‖ζ‖ ^ k` with
`A_η = C ⟨η⟩ ^ (-(n + 1))` integrable in `η`. The operator-valued Mihlin–Hörmander theorem
(`TauCeti.exists_eLpNorm_fourierInv_apply_le_of_norm_iteratedFDeriv_le`) bounds each multiplier
by `C A_η` on `Lᵖ`, and Minkowski's integral inequality
(`TauCeti.eLpNorm_integral_le_lintegral_eLpNorm_of_ne_top`) sums these bounds over `η`.

## Main declarations

* `TauCeti.Symbol.quantizeBesselPotentialSpace`: the bounded operator `H^{s,p} → H^{s - m,p}`,
  which extends `Op(a)` from Schwartz functions
  (`TauCeti.Symbol.quantizeBesselPotentialSpace_toBesselPotentialSpaceCLM`).
* `TauCeti.Symbol.quantizeBesselPotentialSpace_add`,
  `TauCeti.Symbol.quantizeBesselPotentialSpace_smul` and their consequences: the operator is linear
  in the symbol.
* `TauCeti.Symbol.quantizeBesselPotentialSpace_inclusion`,
  `TauCeti.Symbol.quantizeBesselPotentialSpace_comp_inclusion`: compatibility with raising the order
  of the symbol and with the inclusions `H^{s,p} ⊆ H^{r,p}`.
* `TauCeti.Symbol.toDistr_quantizeBesselPotentialSpace_congr`: the operators for different orders
  `s` and for symbols with the same coefficient agree as maps of tempered distributions.
* `TauCeti.Symbol.toDistr_quantizeBesselPotentialSpace_ofSpatial_smul_id`: the symbol `φ(x)`
  quantizes to multiplication by `φ`.
* `TauCeti.Symbol.toDistr_quantizeBesselPotentialSpace_sharp`: `Op(a # b) = Op(a) ∘ Op(b)`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31)
  (the Fourier transform in the position of a symbol with compact spatial support, used there
  for `p = 2`).
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Theorem 6.2.7 (Mihlin–Hörmander).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.19 (Minkowski's integral inequality).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform SchwartzMap
open scoped ContDiff RealInnerProductSpace SchwartzMap ENNReal NNReal BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {t : ℝ} {b : Symbol n V W t}

/-- The multiplier `ζ ↦ ⟨ζ + η⟩ ^ (-t) b̂(η, 2πζ)`. -/
private def shiftedMultiplier (b : Symbol n V W t) (η ζ : CoordinateSpace n) :
    V →L[ℂ] W :=
  (1 + ‖ζ + η‖ ^ 2) ^ (-t / 2) • 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) η

/-- The weight `ζ ↦ ⟨ζ + η⟩ ^ (-t)` of the shifted multiplier is smooth. -/
private theorem contDiff_shiftedWeight (t : ℝ) (η : CoordinateSpace n) :
    ContDiff ℝ ∞ fun ζ : CoordinateSpace n ↦ (1 + ‖ζ + η‖ ^ 2) ^ (-t / 2) :=
  (Function.hasTemperateGrowth_one_add_norm_sq_rpow (CoordinateSpace n) _).1.comp
    (contDiff_id.add contDiff_const)

private theorem HasCompactSpatialSupport.contDiff_shiftedMultiplier
    (hb : b.HasCompactSpatialSupport) (η : CoordinateSpace n) :
    ContDiff ℝ ∞ (shiftedMultiplier b η) :=
  (contDiff_shiftedWeight t η).smul (hb.contDiff_fourier_slice_smul η)

/-- **Mihlin bounds of the shifted multiplier.** `‖D^k N_η(ζ)‖ ≤ C ⟨ζ⟩ ^ (-k) ⟨η⟩ ^ (-r)`, for
every `k` and `r`. -/
private theorem HasCompactSpatialSupport.exists_norm_iteratedFDeriv_shiftedMultiplier_le
    (hb : b.HasCompactSpatialSupport) (k : ℕ) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ η ζ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
        C * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  choose A hA0 hA using fun i : ℕ ↦ exists_norm_iteratedFDeriv_one_add_norm_add_sq_rpow_le
    (E := CoordinateSpace n) (-t) i
  choose B hB0 hB using fun j : ℕ ↦
    hb.exists_norm_iteratedFDeriv_fourier_slice_smul_le j (r + |-t| + k)
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i),
    Finset.sum_nonneg fun i _ ↦ by have := hA0 i; have := hB0 (k - i); positivity,
    fun η ζ ↦ ?_⟩
  refine (norm_iteratedFDeriv_smul_le (contDiff_shiftedWeight t η)
    (hb.contDiff_fourier_slice_smul η) ζ (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hη : 1 ≤ 1 + ‖η‖ ^ 2 := by nlinarith [sq_nonneg ‖η‖]
  have hA0 := hA0 i
  have hB0 := hB0 (k - i)
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun ζ ↦ (1 + ‖ζ + η‖ ^ 2) ^ (-t / 2)) ζ‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun ζ ↦ 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) η) ζ‖
      ≤ (k.choose i : ℝ) *
          (A i * (1 + ‖ζ‖ ^ 2) ^ ((-t - i) / 2) * (1 + ‖η‖ ^ 2) ^ ((|-t| + i) / 2)) *
          (B (k - i) * (1 + ‖ζ‖ ^ 2) ^ ((t - ↑(k - i)) / 2) *
            (1 + ‖η‖ ^ 2) ^ (-(r + |-t| + k) / 2)) := by
        gcongr
        exacts [hA i ζ η, hB (k - i) η ζ]
    _ = (k.choose i : ℝ) * A i * B (k - i) *
          ((1 + ‖ζ‖ ^ 2) ^ ((-t - i) / 2) * (1 + ‖ζ‖ ^ 2) ^ ((t - ↑(k - i)) / 2)) *
          ((1 + ‖η‖ ^ 2) ^ ((|-t| + i) / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |-t| + k) / 2)) := by ring
    _ = (k.choose i : ℝ) * A i * B (k - i) * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) *
          (1 + ‖η‖ ^ 2) ^ ((i - k - r) / 2) := by
        rw [← one_add_norm_sq_rpow_add, ← one_add_norm_sq_rpow_add, Nat.cast_sub hik]
        congr 2 <;> ring_nf
    _ ≤ (k.choose i : ℝ) * A i * B (k - i) * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
        gcongr
        have : (i : ℝ) ≤ k := mod_cast hik
        linarith

/-- The shifted multiplier is bounded by `C ⟨η⟩ ^ (-r)`, uniformly in `ζ`. -/
private theorem HasCompactSpatialSupport.exists_norm_shiftedMultiplier_le
    (hb : b.HasCompactSpatialSupport) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ η ζ : CoordinateSpace n,
      ‖shiftedMultiplier b η ζ‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_iteratedFDeriv_shiftedMultiplier_le 0 r
  exact ⟨C, hC0, fun η ζ ↦ by simpa using hC η ζ⟩

private theorem HasCompactSpatialSupport.continuous_shiftedMultiplier
    (hb : b.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ shiftedMultiplier b q.2 q.1 := by
  have h := hb.continuous_fourier_slice.comp
    ((continuous_snd).prodMk (continuous_const_smul (2 * π) |>.comp continuous_fst))
  have hw : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (1 + ‖q.1 + q.2‖ ^ 2) ^ (-t / 2) :=
    (by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      1 + ‖q.1 + q.2‖ ^ 2).rpow_const fun _ ↦ Or.inl (by positivity)
  exact hw.smul h

/-- The composition symbol of the Bessel weight of order `-t` with `b`, at the angular frequency
`2πζ`, is the superposition `∫ exp(2πi ⟪η, x⟫) N_η(ζ) dη`. -/
private theorem coefficient_besselPotential_sharp (hb : b.HasCompactSpatialSupport)
    (x ζ : CoordinateSpace n) :
    ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient (x, (2 * π) • ζ) =
      ∫ η, (𝐞 ⟪η, x⟫ : ℂ) • shiftedMultiplier b η ζ := by
  rw [coefficient_sharp]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have h : (2 * π)⁻¹ • ((2 * π) • ζ + (2 * π) • η) = ζ + η := by
    rw [← smul_add, inv_smul_smul₀ (by positivity)]
  simp only [coefficient_besselPotential, h, shiftedMultiplier]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, Complex.coe_smul]

/-- **The superposition formula.** The quantization of the composition symbol of the Bessel
weight of order `-t` with `b` is a superposition of modulated Fourier multipliers:
`Op(⟨ξ⟩^(-t) # b) w (x) = ∫ exp(2πi ⟪η, x⟫) 𝓕⁻ (N_η 𝓕 w) (x) dη`. -/
private theorem quantizeSchwartzValue_besselPotential_sharp_eq_integral
    (hb : b.HasCompactSpatialSupport) (w : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient w x =
      ∫ η, (𝐞 ⟪η, x⟫ : ℂ) • 𝓕⁻ (fun ζ ↦ shiftedMultiplier b η ζ (𝓕 w ζ)) x := by
  obtain ⟨C, -, hC⟩ := hb.exists_norm_shiftedMultiplier_le ((n : ℝ) + 1)
  exact quantizeSchwartzValue_eq_integral_smul_fourierInv (C := C) (M := 0)
    (hb.continuous_shiftedMultiplier.comp continuous_swap)
    integrable_one_add_norm_sq_rpow_neg_succ_div_two (fun η ζ ↦ (hC η ζ).trans_eq (by simp))
    (coefficient_besselPotential_sharp hb x) w

/-- In dimension `0` every quantization is bounded on `Lᵖ`: positions and frequencies range over
a single point, so `Op(a) w = a(0, 0) (w 0)` up to the total mass of the point. -/
private theorem exists_eLpNorm_quantizeSchwartzValue_le_of_dim_zero {m : ℝ} (a : Symbol 0 V W m)
    (p : ℝ≥0∞) : ∃ C : ℝ≥0, ∀ w : 𝓢(CoordinateSpace 0, V),
      eLpNorm (quantizeSchwartzValue a.coefficient w) p volume ≤ C * eLpNorm w p volume := by
  set μ : ℝ := (volume : Measure (CoordinateSpace 0)).real Set.univ
  refine ⟨(μ * (‖a.coefficient (0, 0)‖ * μ)).toNNReal, fun w ↦ ?_⟩
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (a.contDiff_quantizeSchwartzValue w).continuous.aestronglyMeasurable
    (.of_forall fun x ↦ ?_) p
  rw [quantizeSchwartzValue_def]
  refine (norm_integral_le_of_norm_le_const (C := ‖a.coefficient (0, 0)‖ * (μ * ‖w x‖))
    (.of_forall fun ζ ↦ ?_)).trans (le_of_eq (by ring))
  rw [Circle.norm_smul, Subsingleton.elim (x, (2 * π) • ζ) (0, 0)]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  gcongr
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  refine (norm_integral_le_of_norm_le_const (C := ‖w x‖) (.of_forall fun y ↦ ?_)).trans
    (le_of_eq (by ring))
  rw [Circle.norm_smul, Subsingleton.elim y x]

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **The `Lᵖ` estimate.** For `1 < p < ∞` and a symbol `b` of order `t` with compact spatial
support, the quantization of the composition symbol `⟨ξ⟩ ^ (-t) # b` is bounded on `Lᵖ`, on
Schwartz functions. -/
private theorem HasCompactSpatialSupport.exists_eLpNorm_quantizeSchwartzValue_sharp_le
    (hb : b.HasCompactSpatialSupport) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ w : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue
        ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient w) p volume ≤
        C * eLpNorm w p volume := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · exact exists_eLpNorm_quantizeSchwartzValue_le_of_dim_zero _ p
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fourierInv_apply_le_of_norm_iteratedFDeriv_le
    (V := CoordinateSpace n) (G := V) (H := W) (N := n + 1) (by simp; omega) hp hp_top
  choose D hD0 hD using fun k : ℕ ↦ hb.exists_norm_iteratedFDeriv_shiftedMultiplier_le k
    ((n : ℝ) + 1)
  set S : ℝ := ∑ k ∈ Finset.range (n + 2), D k
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ hD0 k
  set ρ : CoordinateSpace n → ℝ := fun η ↦ (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hρ0 (η : CoordinateSpace n) : 0 ≤ ρ η := by positivity
  set I : ℝ≥0∞ := ∫⁻ η, ENNReal.ofReal (ρ η)
  have hI : I ≠ (∞ : ℝ≥0∞) := integrable_one_add_norm_sq_rpow_neg_succ_div_two.lintegral_lt_top.ne
  refine ⟨C₀ * (ENNReal.ofReal S).toNNReal * I.toNNReal, fun w ↦ ?_⟩
  obtain ⟨T, hTdef⟩ : ∃ T : CoordinateSpace n → CoordinateSpace n → W,
      T = fun η x ↦ 𝓕⁻ (fun ζ ↦ shiftedMultiplier b η ζ (𝓕 w ζ)) x := ⟨_, rfl⟩
  -- For each `η`, the Mihlin–Hörmander theorem bounds the multiplier `N_η` on `Lᵖ`.
  have hT (η : CoordinateSpace n) :
      eLpNorm (T η) p volume ≤ C₀ * ENNReal.ofReal (S * ρ η) * eLpNorm w p volume := by
    have hA : ∀ k ≤ n + 1, ∀ ζ ≠ 0, ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
        ((S * ρ η).toNNReal : ℝ) / ‖ζ‖ ^ k := by
      intro k hk ζ hζ
      rw [Real.coe_toNNReal _ (mul_nonneg hS0 (hρ0 η))]
      calc _ ≤ D k * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * ρ η := hD k η ζ
        _ ≤ S * (‖ζ‖ ^ k)⁻¹ * ρ η := by
            gcongr
            · exact Finset.single_le_sum (fun i _ ↦ hD0 i) (Finset.mem_range.2 (by omega))
            · exact one_add_norm_sq_rpow_neg_le_inv_norm_pow hζ k
        _ = _ := by ring
    have hgrowth : (shiftedMultiplier b η).HasTemperateGrowth :=
      Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow (m := 0)
        (hb.contDiff_shiftedMultiplier η) fun k ↦ ⟨D k * ρ η, fun ζ ↦ by
          rw [zero_sub, mul_right_comm]
          exact hD k η ζ⟩
    rw [hTdef]
    -- `ENNReal.ofReal x` is by definition the coercion of `x.toNNReal`.
    exact hC₀ hgrowth hA w
  -- `T` is jointly continuous, by dominated convergence.
  obtain ⟨C', -, hC'⟩ := hb.exists_norm_shiftedMultiplier_le 0
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ T q.2 q.1 := by
    simp only [hTdef, Real.fourierInv_eq]
    refine continuous_of_dominated (bound := fun ζ ↦ C' * ‖𝓕 w ζ‖) (fun q ↦ ?_)
      (fun q ↦ .of_forall fun ζ ↦ ?_) ((𝓕 w).integrable.norm.const_mul C')
      (.of_forall fun ζ ↦ ?_)
    · exact (((Real.continuous_fourierChar.comp (by fun_prop)).smul
        ((hb.continuous_shiftedMultiplier.comp (continuous_id.prodMk continuous_const)).clm_apply
          (𝓕 w).continuous))).aestronglyMeasurable
    · rw [Circle.norm_smul]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      gcongr
      simpa using hC' q.2 ζ
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).smul
        ((hb.continuous_shiftedMultiplier.comp (continuous_const.prodMk continuous_snd)).clm_apply
          continuous_const)
  have hsup : quantizeSchwartzValue
      ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient w =
        fun x ↦ ∫ η, (𝐞 ⟪η, x⟫ : ℂ) • T η x := by
    rw [hTdef]
    exact funext (quantizeSchwartzValue_besselPotential_sharp_eq_integral hb w)
  have he : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪q.2, q.1⟫ : ℂ) :=
    Real.continuous_fourierChar_inner.comp continuous_swap
  have hF := he.smul hcont
  rw [hsup]
  calc eLpNorm (fun x ↦ ∫ η, (𝐞 ⟪η, x⟫ : ℂ) • T η x) p volume
      ≤ ∫⁻ η, eLpNorm (fun x ↦ (𝐞 ⟪η, x⟫ : ℂ) • T η x) p volume :=
        eLpNorm_integral_le_lintegral_eLpNorm_of_ne_top
          (F := fun x η ↦ (𝐞 ⟪η, x⟫ : ℂ) • T η x) hF.aestronglyMeasurable hp.le hp_top
    _ = ∫⁻ η, eLpNorm (T η) p volume :=
        lintegral_congr fun η ↦ eLpNorm_congr_norm_ae
          (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
          (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
          (.of_forall fun x ↦ by simp [norm_smul])
    _ ≤ ∫⁻ η, C₀ * ENNReal.ofReal (S * ρ η) * eLpNorm w p volume := lintegral_mono hT
    _ = C₀ * ENNReal.ofReal S * I * eLpNorm w p volume := by
        simp only [ENNReal.ofReal_mul hS0, ← mul_assoc]
        rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top,
          ENNReal.coe_toNNReal hI]

variable [CompleteSpace V] [CompleteSpace W]

/-- On Schwartz functions, `Op(a) : H^{s,p} → H^{s - m,p}` is bounded. -/
private theorem HasCompactSpatialSupport.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {m : ℝ} {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha.isUniform u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s p u‖ := by
  -- Write `u = J^{-s} w` with `w = J^s u`, so that `Op(a) u = Op(b) w` for the symbol
  -- `b = a ⟨ξ⟩^(-s)` of order `m - s`, and `J^{s-m} Op(b) = Op(⟨ξ⟩^(s - m) # b)`.
  set b : Symbol n V W (m + -s) := a.comp (besselPotential (-s))
  have hb : b.HasCompactSpatialSupport := ha.comp_right _
  obtain ⟨C, hC⟩ := hb.exists_eLpNorm_quantizeSchwartzValue_sharp_le hp hp_top
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : 𝓢(CoordinateSpace n, V), w = fourierMultiplierCLM V
      (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u := ⟨_, rfl⟩
  have hu : fourierMultiplierCLM V
      (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) w = u := by
    rw [hw]
    simpa using fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg (-s) u
  have hg : (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow (CoordinateSpace n) _)
  have hbw : quantizeSchwartzValue b.coefficient w = quantizeSchwartzValue a.coefficient u := by
    funext y
    rw [← hu, quantizeSchwartzValue_fourierMultiplierCLM hg]
    congr 1
    funext q
    simp only [b, coefficient_comp, coefficient_besselPotential, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id]
  have key : ⇑(fourierMultiplierCLM W
      (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha.isUniform u)) =
      quantizeSchwartzValue ((besselPotential (-(m + -s)) : Symbol n W W _).sharp b hb).coefficient
        w := by
    funext x
    rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue, quantizeSchwartzValue_besselPotential]
    have hexp : (-(m + -s)) / 2 = (s - m) / 2 := by ring
    have hv : (hb.hasCompactSupport_quantizeSchwartzValue w).toSchwartzMap
        (b.contDiff_quantizeSchwartzValue w) = quantizeUniformCLM a ha.isUniform u := by
      ext y
      rw [HasCompactSupport.toSchwartzMap_toFun, hbw, quantizeUniformCLM_apply]
    rw [hexp, hv]
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.norm_toLp_eq,
    toLp_toBesselPotentialSpaceCLM, toLp_toBesselPotentialSpaceCLM, norm_toLp, norm_toLp, key,
    ← ENNReal.coe_toReal C, ← ENNReal.toReal_mul]
  rw [← hw]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (w.memLp p).eLpNorm_ne_top)
    (hC w)

/-! ### The operator on `H^{s,p}` -/

/-- **Pseudodifferential operators with compact spatial support on `H^{s,p}`.** For a symbol `a`
of order `m` with compact spatial support between finite-dimensional complex normed spaces, the
left quantization `Op(a)` as a bounded operator `H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)`. For
`1 < p < ∞` it extends `Op(a)` from Schwartz functions: on a Schwartz function `u` it is the
Schwartz function `Op(a) u`
(`TauCeti.Symbol.quantizeBesselPotentialSpace_toBesselPotentialSpaceCLM`), and by density of the
Schwartz functions it is the unique continuous linear map with this property
(`BesselPotentialSpace.continuousLinearMap_ext`). For other exponents its value is unspecified.
Its counterpart on `H^s = H^{s,2}` for Hilbert fibres is `TauCeti.Symbol.quantizeSobolev`. -/
def quantizeBesselPotentialSpace {m : ℝ} (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    H^{s, p}(CoordinateSpace n, V) →L[ℂ] H^{s - m, p}(CoordinateSpace n, W) :=
  ((toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) p).comp
    (quantizeUniformCLM a ha.isUniform)).toLinearMap.extendOfNorm
      (toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s p).toLinearMap

section Operator

variable {m m' : ℝ} {a : Symbol n V W m} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Mapping of pseudodifferential operators with compact spatial support on `H^{s,p}`.** Let
`1 < p < ∞`. On a Schwartz function `u`, the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the
Schwartz function `Op(a) u`. -/
@[simp]
theorem quantizeBesselPotentialSpace_toBesselPotentialSpaceCLM (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha.isUniform u) := by
  obtain ⟨C, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
  rw [quantizeBesselPotentialSpace]
  set f := ((toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) p).comp
    (quantizeUniformCLM a ha.isUniform)).toLinearMap
  set e := (toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s p).toLinearMap
  simpa [f, e] using LinearMap.extendOfNorm_eq (f := f) (e := e)
    (denseRange_toBesselPotentialSpaceCLM s hp_top) ⟨C, fun u ↦ by simpa [f, e] using hC u⟩ u

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is additive in the symbol. -/
theorem quantizeBesselPotentialSpace_add {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : (a + b).HasCompactSpatialSupport) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a + b).quantizeBesselPotentialSpace hab s p =
      a.quantizeBesselPotentialSpace ha s p + b.quantizeBesselPotentialSpace hb s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, quantizeUniformCLM_add ha.isUniform hb.isUniform]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is homogeneous in the symbol. -/
theorem quantizeBesselPotentialSpace_smul (ha : a.HasCompactSpatialSupport) (c : ℂ)
    (hca : (c • a).HasCompactSpatialSupport) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (c • a).quantizeBesselPotentialSpace hca s p = c • a.quantizeBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, quantizeUniformCLM_smul ha.isUniform]

/-- The zero symbol quantizes to the zero operator `H^{s,p} → H^{s - m,p}`. -/
@[simp]
theorem quantizeBesselPotentialSpace_zero (h : (0 : Symbol n V W m).HasCompactSpatialSupport)
    (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (0 : Symbol n V W m).quantizeBesselPotentialSpace h s p = 0 := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes the negated symbol to the negated
operator. -/
theorem quantizeBesselPotentialSpace_neg (ha : a.HasCompactSpatialSupport)
    (hna : (-a).HasCompactSpatialSupport) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (-a).quantizeBesselPotentialSpace hna s p = -a.quantizeBesselPotentialSpace ha s p := by
  have hq : quantizeUniformCLM (-a) hna.isUniform = -quantizeUniformCLM a ha.isUniform := by
    rw [quantizeUniformCLM_congr hna.isUniform (ha.isUniform.smul (-1)) (by simp),
      quantizeUniformCLM_smul, neg_one_smul]
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, hq]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes differences of symbols to differences of
operators. -/
theorem quantizeBesselPotentialSpace_sub {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : (a - b).HasCompactSpatialSupport) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a - b).quantizeBesselPotentialSpace hab s p =
      a.quantizeBesselPotentialSpace ha s p - b.quantizeBesselPotentialSpace hb s p := by
  rw [eq_sub_iff_add_eq, ← quantizeBesselPotentialSpace_add hab hb (by rwa [sub_add_cancel]) s hp
    hp_top]
  simp_rw [sub_add_cancel]

/-- **Changing the order of the symbol.** Let `1 < p < ∞`. Viewing a symbol of order `m` as a
symbol of order `m' ≥ m` gives the operator `H^{s,p} → H^{s - m,p}` followed by the inclusion
`H^{s - m,p} ⊆ H^{s - m',p}`. -/
theorem quantizeBesselPotentialSpace_inclusion (h : m ≤ m') (ha : a.HasCompactSpatialSupport)
    (ha' : (inclusion h a).HasCompactSpatialSupport) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (inclusion h a).quantizeBesselPotentialSpace ha' s p =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
    quantizeUniformCLM_congr ha'.isUniform ha.isUniform (coefficient_inclusion h a)]

/-- **Changing the Sobolev order.** Let `1 < p < ∞`. The operators
`Op(a) : H^{s,p} → H^{s - m,p}` for the different orders `s` are compatible with the inclusions
`H^{s,p} ⊆ H^{r,p}`. -/
theorem quantizeBesselPotentialSpace_comp_inclusion (ha : a.HasCompactSpatialSupport) {r s : ℝ}
    (h : r ≤ s) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    a.quantizeBesselPotentialSpace ha r p ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]

/-- **Compatibility of the extensions.** The operator `Op(a) : H^{s,p} → H^{s - m,p}` only depends
on the coefficient of `a` and on the tempered distribution of its argument: symbols `a` and `b` of
orders `m` and `m'` with the same coefficient give the same tempered distribution on
`u ∈ H^{s,p}` and `v ∈ H^{t,p}` whenever `u` and `v` have the same tempered distribution. -/
theorem toDistr_quantizeBesselPotentialSpace_congr {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s t : ℝ}
    {u : H^{s, p}(CoordinateSpace n, V)} {v : H^{t, p}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeBesselPotentialSpace ha s p u).toDistr =
      (b.quantizeBesselPotentialSpace hb t p v).toDistr :=
  SchwartzMap.toDistr_apply_congr_of_comp_eq hp_top (A := quantizeUniformCLM a ha.isUniform)
    (ContinuousLinearMap.ext fun u ↦ by simp [hp, hp_top])
    (ContinuousLinearMap.ext fun u ↦ by
      simp [hp, hp_top, quantizeUniformCLM_congr ha.isUniform hb.isUniform hab]) huv

/-- **Multiplication operators.** For a Schwartz function `φ` such that the symbol `φ(x) id` of
order `0` has compact spatial support, for instance a compactly supported `φ`
(`TauCeti.Symbol.hasCompactSpatialSupport_ofSpatial_smul_id`), this symbol quantizes to
multiplication by `φ` on `H^{s,p}`. -/
theorem toDistr_quantizeBesselPotentialSpace_ofSpatial_smul_id (φ : 𝓢(CoordinateSpace n, ℂ))
    (h : (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      ((φ.smooth ⊤).smul contDiff_const)).HasCompactSpatialSupport)
    (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    ((ofSpatial _ _).quantizeBesselPotentialSpace h s p u).toDistr =
      TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) u.toDistr := by
  have hc : (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      ((φ.smooth ⊤).smul contDiff_const)).coefficient =
        fun p ↦ φ p.1 • ContinuousLinearMap.id ℂ V :=
    coefficient_ofSpatial_eq _ _
  have hq : quantizeUniformCLM _ h.isUniform = SchwartzMap.smulLeftCLM V (φ : _ → ℂ) := by
    ext v x
    rw [quantizeUniformCLM_apply, hc, SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth]
    simpa using quantizeSchwartzValue_comp_fst (fun y ↦ φ y • ContinuousLinearMap.id ℂ V) v x
  have key : BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
        (ofSpatial _ _).quantizeBesselPotentialSpace h s p =
      TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) ∘L
        BesselPotentialSpace.toDistrCLM _ _ _ _ := by
    refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun v ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply,
      quantizeBesselPotentialSpace_toBesselPotentialSpaceCLM h s hp hp_top, hq,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
    exact (TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq v).symm
  simpa using congrArg (fun T ↦ T u) key

/-- **Composition of quantizations on `H^{s,p}`.** For symbols `a` and `b` with compact spatial
support, the operator `Op(a # b) : H^{s,p} → H^{s - (m' + m),p}` is the composition of
`Op(b) : H^{s,p} → H^{s - m,p}` and `Op(a) : H^{s - m,p} → H^{s - m - m',p}`. -/
theorem toDistr_quantizeBesselPotentialSpace_sharp {U : Type*} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [FiniteDimensional ℂ U] [CompleteSpace U] {a : Symbol n W U m'}
    {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport)
    (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    ((a.sharp b hb).quantizeBesselPotentialSpace (ha.sharp hb) s p u).toDistr =
      (a.quantizeBesselPotentialSpace ha (s - m) p
        (b.quantizeBesselPotentialSpace hb s p u)).toDistr := by
  -- On a Schwartz function `v`, `Op(a # b) v = Op(a) (Op(b) v)`, and `Op(b) v` is Schwartz.
  have hq (v : 𝓢(CoordinateSpace n, V)) :
      quantizeUniformCLM (a.sharp b hb) (ha.sharp hb).isUniform v =
      quantizeUniformCLM a ha.isUniform (quantizeUniformCLM b hb.isUniform v) := by
    ext x
    rw [quantizeUniformCLM_apply, quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb,
      quantizeUniformCLM_apply]
    congr 1
    ext y
    simp
  have key : BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
        (a.sharp b hb).quantizeBesselPotentialSpace (ha.sharp hb) s p =
      BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L a.quantizeBesselPotentialSpace ha (s - m) p ∘L
        b.quantizeBesselPotentialSpace hb s p := by
    refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun v ↦ ?_
    simp [hp, hp_top, hq]
  simpa using congrArg (fun T ↦ T u) key

end Operator

end Symbol

end TauCeti
