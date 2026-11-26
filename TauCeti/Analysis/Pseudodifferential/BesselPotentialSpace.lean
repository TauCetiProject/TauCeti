/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.MulLeft
public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform.Sharp
public import TauCeti.Analysis.Pseudodifferential.Symbol.Map
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.Fourier.MihlinHormander
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.SobolevEmbedding
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Regularization
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
for every real `s`. This file defines this extension for every symbol whose estimates are uniform
in the position (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace`) and proves that it extends
`Op(a)` for symbols with compact spatial support; for complex Hilbert fibres and uniform symbols
this is proved in `TauCeti/Analysis/Pseudodifferential/Lp/BesselPotentialSpace.lean`. This is the
`Lᵖ` form of the Sobolev mapping theorem `TauCeti.Symbol.exists_quantizeSobolev` for `p = 2`; it is
the estimate behind the `Lᵖ` versions of local elliptic regularity
(`TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeUniformBesselPotentialSpace`).

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

Every constant in this argument is linear in the bounds on the Fourier slices of `b`, and those are
controlled by continuous seminorms of `a` uniformly over the symbols vanishing outside a fixed
compact set (`TauCeti.Symbol.exists_norm_iteratedFDeriv_fourier_slice_le_seminorm`). So the
operator norm of `Op(a) : H^{s,p} → H^{s - m,p}` is at most a continuous seminorm of `a` on such
symbols (`TauCeti.Symbol.exists_norm_quantizeUniformBesselPotentialSpace_le_seminorm`), and a
continuous family of them has quantizations that depend continuously on the parameter in the
operator norm
(`TauCeti.Symbol.continuous_quantizeUniformBesselPotentialSpace`). Unlike the case `p = 2`
(`TauCeti.Symbol.exists_norm_quantizeSobolev_le_sum_seminorm`), the seminorm involves frequency
derivatives of `a` of order up to `n + 1`, through Mihlin's condition.

## Main declarations

All in the namespace `TauCeti.Symbol`:

* `quantizeUniformBesselPotentialSpace`: the bounded operator `H^{s,p} → H^{s - m,p}`, which for
  symbols with compact spatial support extends `Op(a)` from Schwartz functions
  (`HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`).
  For `p = 2`, complex Hilbert spaces as fibres and compact spatial support it is
  `quantizeSobolev` (`HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_two`).
* `HasBesselPotentialSpaceExtension`: the property that the operator extends `Op(a)` from Schwartz
  functions for every `s`. For `p < ∞` it is closed under the linear operations on symbols, under
  raising the order, and under `uniformSharp` (`HasBesselPotentialSpaceExtension.add`,
  `HasBesselPotentialSpaceExtension.uniformSharp`, and the lemmas after them). The linearity of the
  operator in the symbol, its compatibility with the inclusions, with composition
  (`HasBesselPotentialSpaceExtension.quantizeUniformBesselPotentialSpace_uniformSharp`,
  `HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_uniformSharp`), and
  across exponents
  (`HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_congr_exponent`),
  and the multiplication operators of symbols `f(x)`
  (`HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_ofSpatial`) are
  proved once from this property
  (`HasBesselPotentialSpaceExtension.quantizeUniformBesselPotentialSpace_add` and the lemmas after
  it), through the density lemma
  `HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall`, and
  specialized to symbols with compact spatial support
  (`HasCompactSpatialSupport.hasBesselPotentialSpaceExtension`).
* `IsUniformlySmoothing.exists_toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall`,
  `IsUniformlySmoothing.memSobolev_toDistr_quantizeUniformBesselPotentialSpace_of_forall`: if
  uniform symbols have the `H^{·,p}` extension property (`p < ∞`), uniformly smoothing symbols gain
  every order of `H^{·,p}` regularity.
* `hasBesselPotentialSpaceExtension_const`, `quantizeUniformBesselPotentialSpace_const`,
  `hasBesselPotentialSpaceExtension_besselPotential`,
  `quantizeUniformBesselPotentialSpace_besselPotential`,
  `toDistr_quantizeUniformBesselPotentialSpace_besselPotential`: for `p < ∞`, constant symbols and
  Bessel-potential symbols have the extension property over arbitrary complete complex normed
  fibres, quantizing to `BesselPotentialSpace.postcomp` and the canonical isometric isomorphism
  `H^{s,p} → H^{s - m,p}` (`TemperedDistribution.besselPotential` on tempered distributions).
* `exists_norm_quantizeUniformBesselPotentialSpace_le_seminorm`: for symbols vanishing outside a
  fixed compact set, the operator norm is at most a continuous seminorm of the symbol.
* `continuous_quantizeUniformBesselPotentialSpace`: continuity of `Op(a)` in the operator norm
  along a continuous family of such symbols.
* `HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_sub`: the operator takes
  differences of symbols to differences of operators.
* `HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_congr`: the operators for
  different orders `s` and for symbols with the same coefficient agree as maps of tempered
  distributions;
  `HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_congr_exponent` is the same
  for different exponents `p` and `q`, through the Sobolev embedding `H^{s,p} ⊆ H^{s - δ,q}` for
  `p < q`.
* `HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_smulLeft`: the symbol
  `ψ(x) a(x, ξ)` quantizes to `ψ Op(a)`.
* `toDistr_quantizeUniformBesselPotentialSpace_ofSpatial_smul_id`: the symbol `φ(x)` quantizes to
  multiplication by `φ`.
* `toDistr_quantizeUniformBesselPotentialSpace_sharp`: `Op(a # b) = Op(a) ∘ Op(b)`.

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

/-- The constants of a family of nonnegative per-order bounds combine into one bound: their sum
over `Finset.range N` is nonnegative and dominates each of its terms. -/
private theorem sum_range_nonneg_and_le {B : ℕ → ℝ} (hB0 : ∀ j, 0 ≤ B j) (N : ℕ) :
    0 ≤ ∑ j ∈ Finset.range N, B j ∧ ∀ j < N, B j ≤ ∑ i ∈ Finset.range N, B i :=
  ⟨Finset.sum_nonneg fun j _ ↦ hB0 j,
    fun _ hj ↦ Finset.single_le_sum (fun i _ ↦ hB0 i) (Finset.mem_range.2 hj)⟩

/-- **Mihlin bounds of the shifted multiplier.** There is a constant `M`, depending only on `n`,
`t`, `k` and `r`, with the following property. If the derivatives of order at most `k` of
`ξ ↦ b̂(η, ξ)` are bounded by `B ⟨ξ⟩ ^ (t - j) ⟨η⟩ ^ (-(r + |t| + k))`, then
`‖D^k N_η(ζ)‖ ≤ M B ⟨ζ⟩ ^ (-k) ⟨η⟩ ^ (-r)`. -/
private theorem exists_norm_iteratedFDeriv_shiftedMultiplier_le_mul (k : ℕ) (r : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ b : Symbol n V W t, b.HasCompactSpatialSupport → ∀ B, 0 ≤ B →
      (∀ j ≤ k, ∀ η ξ : CoordinateSpace n,
        ‖iteratedFDeriv ℝ j (fun ξ ↦ 𝓕 (fun y ↦ b.coefficient (y, ξ)) η) ξ‖ ≤
          B * (1 + ‖ξ‖ ^ 2) ^ ((t - j) / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |-t| + k) / 2)) →
      ∀ η ζ : CoordinateSpace n, ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
        M * B * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  choose A hA0 hA using fun i : ℕ ↦ exists_norm_iteratedFDeriv_one_add_norm_add_sq_rpow_le
    (E := CoordinateSpace n) (-t) i
  -- The factor by which rescaling the frequency by `2π` changes the bound of order `j`.
  set E : ℕ → ℝ := fun j ↦ (2 * π) ^ j * (2 * π) ^ |t - j|
  have hE0 (j : ℕ) : 0 ≤ E j := by positivity
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * E (k - i),
    Finset.sum_nonneg fun i _ ↦ by have := hA0 i; have := hE0 (k - i); positivity,
    fun b hb B hB0 hB η ζ ↦ ?_⟩
  refine (norm_iteratedFDeriv_smul_le (contDiff_shiftedWeight t η)
    (hb.contDiff_fourier_slice_smul η) ζ (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hη : 1 ≤ 1 + ‖η‖ ^ 2 := by nlinarith [sq_nonneg ‖η‖]
  have hA0 := hA0 i
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun ζ ↦ (1 + ‖ζ + η‖ ^ 2) ^ (-t / 2)) ζ‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun ζ ↦ 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) η) ζ‖
      ≤ (k.choose i : ℝ) *
          (A i * (1 + ‖ζ‖ ^ 2) ^ ((-t - i) / 2) * (1 + ‖η‖ ^ 2) ^ ((|-t| + i) / 2)) *
          (E (k - i) * B * (1 + ‖ζ‖ ^ 2) ^ ((t - ↑(k - i)) / 2) *
            (1 + ‖η‖ ^ 2) ^ (-(r + |-t| + k) / 2)) := by
        gcongr
        exacts [hA i ζ η, hb.norm_iteratedFDeriv_fourier_slice_smul_le hB0
          (hB (k - i) (Nat.sub_le k i)) η ζ]
    _ = (k.choose i : ℝ) * A i * E (k - i) * B *
          ((1 + ‖ζ‖ ^ 2) ^ ((-t - i) / 2) * (1 + ‖ζ‖ ^ 2) ^ ((t - ↑(k - i)) / 2)) *
          ((1 + ‖η‖ ^ 2) ^ ((|-t| + i) / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |-t| + k) / 2)) := by ring
    _ = (k.choose i : ℝ) * A i * E (k - i) * B * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) *
          (1 + ‖η‖ ^ 2) ^ ((i - k - r) / 2) := by
        rw [← one_add_norm_sq_rpow_add, ← one_add_norm_sq_rpow_add, Nat.cast_sub hik]
        congr 2 <;> ring_nf
    _ ≤ (k.choose i : ℝ) * A i * E (k - i) * B * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
        gcongr
        have : (i : ℝ) ≤ k := mod_cast hik
        linarith

/-- **Mihlin bounds of the shifted multiplier.** `‖D^k N_η(ζ)‖ ≤ C ⟨ζ⟩ ^ (-k) ⟨η⟩ ^ (-r)`, for
every `k` and `r`. -/
private theorem HasCompactSpatialSupport.exists_norm_iteratedFDeriv_shiftedMultiplier_le
    (hb : b.HasCompactSpatialSupport) (k : ℕ) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ η ζ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
        C * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨M, hM0, hM⟩ :=
    exists_norm_iteratedFDeriv_shiftedMultiplier_le_mul (V := V) (W := W) (n := n) (t := t) k r
  choose B hB0 hB using fun j : ℕ ↦
    hb.exists_norm_iteratedFDeriv_fourier_slice_le j (r + |-t| + k)
  obtain ⟨hS0, hS⟩ := sum_range_nonneg_and_le hB0 (k + 1)
  refine ⟨M * ∑ j ∈ Finset.range (k + 1), B j, mul_nonneg hM0 hS0,
    hM b hb _ hS0 fun j hj η ξ ↦ (hB j η ξ).trans ?_⟩
  gcongr
  exact hS j (by omega)

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
a single point of mass `μ`, so `Op(a) w = μ a(0, 0) (w 0)` up to that mass, and
`‖Op(a) w‖_p ≤ μ ‖a(0, 0)‖ μ ‖w‖_p`. -/
private theorem eLpNorm_quantizeSchwartzValue_le_of_dim_zero {m : ℝ} (a : Symbol 0 V W m)
    (p : ℝ≥0∞) (w : 𝓢(CoordinateSpace 0, V)) :
    eLpNorm (quantizeSchwartzValue a.coefficient w) p volume ≤
      ENNReal.ofReal ((volume : Measure (CoordinateSpace 0)).real Set.univ *
        (‖a.coefficient (0, 0)‖ * (volume : Measure (CoordinateSpace 0)).real Set.univ)) *
        eLpNorm w p volume := by
  set μ : ℝ := (volume : Measure (CoordinateSpace 0)).real Set.univ
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

/-- In dimension `0`, the value at the single point of the composition symbol of the Bessel
weight of order `-t` with `b` is at most `μ B`, where `μ` is the mass of the point and `B` bounds
the Fourier transform `b̂` of the position slice. -/
private theorem norm_coefficient_besselPotential_sharp_le_of_dim_zero {b : Symbol 0 V W t}
    (hb : b.HasCompactSpatialSupport) {B : ℝ}
    (hB : ‖𝓕 (fun y ↦ b.coefficient (y, 0)) 0‖ ≤ B) :
    ‖((besselPotential (-t) : Symbol 0 W W (-t)).sharp b hb).coefficient (0, 0)‖ ≤
      B * (volume : Measure (CoordinateSpace 0)).real Set.univ := by
  have h := coefficient_besselPotential_sharp hb 0 0
  rw [smul_zero] at h
  rw [h]
  refine norm_integral_le_of_norm_le_const (.of_forall fun η ↦ ?_)
  rw [norm_smul, Circle.norm_coe, one_mul, Subsingleton.elim η 0, shiftedMultiplier, smul_zero,
    zero_add, norm_zero]
  simpa using hB

/-- The modulated multipliers `(η, x) ↦ 𝓕⁻ (N_η 𝓕 w) (x)` of the superposition formula are jointly
continuous, by dominated convergence. -/
private theorem HasCompactSpatialSupport.continuous_fourierInv_shiftedMultiplier
    (hb : b.HasCompactSpatialSupport) (w : 𝓢(CoordinateSpace n, V)) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕⁻ (fun ζ ↦ shiftedMultiplier b q.2 ζ (𝓕 w ζ)) q.1 := by
  obtain ⟨C', -, hC'⟩ := hb.exists_norm_shiftedMultiplier_le 0
  simp only [Real.fourierInv_eq]
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

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **The Mihlin–Hörmander bound for each multiplier.** Let `1 < p < ∞` in positive dimension.
There is a constant `C₀`, depending only on `n`, `p`, `V` and `W`, such that if the multipliers
`N_η` satisfy Mihlin's condition `‖D^k N_η(ζ)‖ ≤ S ⟨ζ⟩ ^ (-k) ⟨η⟩ ^ (-(n + 1))` for `k ≤ n + 1`,
then `‖𝓕⁻ (N_η 𝓕 w)‖_p ≤ C₀ S ⟨η⟩ ^ (-(n + 1)) ‖w‖_p`. -/
private theorem exists_eLpNorm_fourierInv_shiftedMultiplier_le_mul [NeZero n] {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C₀ : ℝ≥0, ∀ (b : Symbol n V W t), b.HasCompactSpatialSupport → ∀ S : ℝ, 0 ≤ S →
      (∀ k ≤ n + 1, ∀ η ζ : CoordinateSpace n,
        ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
          S * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) →
      ∀ (η : CoordinateSpace n) (w : 𝓢(CoordinateSpace n, V)),
        eLpNorm (fun x ↦ 𝓕⁻ (fun ζ ↦ shiftedMultiplier b η ζ (𝓕 w ζ)) x) p volume ≤
          C₀ * ENNReal.ofReal (S * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) * eLpNorm w p volume := by
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fourierInv_apply_le_of_norm_iteratedFDeriv_le
    (V := CoordinateSpace n) (G := V) (H := W) (N := n + 1) (by simp; omega) hp hp_top
  refine ⟨C₀, fun b hb S hS0 hS η w ↦ ?_⟩
  set ρ : ℝ := (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hρ0 : 0 ≤ ρ := by positivity
  choose D _ hD using fun k : ℕ ↦ hb.exists_norm_iteratedFDeriv_shiftedMultiplier_le k
    ((n : ℝ) + 1)
  have hA : ∀ k ≤ n + 1, ∀ ζ ≠ 0, ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
      ((S * ρ).toNNReal : ℝ) / ‖ζ‖ ^ k := by
    intro k hk ζ hζ
    rw [Real.coe_toNNReal _ (mul_nonneg hS0 hρ0)]
    calc _ ≤ S * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * ρ := hS k hk η ζ
      _ ≤ S * (‖ζ‖ ^ k)⁻¹ * ρ := by
          gcongr
          simpa [add_comm] using
            norm_sq_add_rpow_div_two_le zero_le_one hζ (neg_nonpos.2 (Nat.cast_nonneg k))
      _ = _ := by ring
  have hgrowth : (shiftedMultiplier b η).HasTemperateGrowth :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow (m := 0)
      (hb.contDiff_shiftedMultiplier η) fun k ↦ ⟨D k * ρ, fun ζ ↦ by
        rw [zero_sub, mul_right_comm]
        exact hD k η ζ⟩
  rw [← ENNReal.ofNNReal_toNNReal]
  exact hC₀ hgrowth hA w

/-- **The `Lᵖ` estimate in positive dimension.** Let `1 < p < ∞`. There is a constant `L`,
depending only on `n`, `p`, `V` and `W`, such that if the multipliers `N_η` satisfy Mihlin's
condition `‖D^k N_η(ζ)‖ ≤ S ⟨ζ⟩ ^ (-k) ⟨η⟩ ^ (-(n + 1))` for `k ≤ n + 1`, then the quantization
of the composition symbol `⟨ξ⟩ ^ (-t) # b` satisfies `‖Op(⟨ξ⟩ ^ (-t) # b) w‖_p ≤ L S ‖w‖_p` on
Schwartz functions: the superposition formula and Minkowski's integral inequality sum the bounds
for the single multipliers over `η`. -/
private theorem exists_eLpNorm_quantizeSchwartzValue_sharp_le_mul_of_shiftedMultiplier [NeZero n]
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ L : ℝ≥0, ∀ (b : Symbol n V W t) (hb : b.HasCompactSpatialSupport) (S : ℝ), 0 ≤ S →
      (∀ k ≤ n + 1, ∀ η ζ : CoordinateSpace n,
        ‖iteratedFDeriv ℝ k (shiftedMultiplier b η) ζ‖ ≤
          S * (1 + ‖ζ‖ ^ 2) ^ (-(k : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) →
      ∀ w : 𝓢(CoordinateSpace n, V),
        eLpNorm (quantizeSchwartzValue
          ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient w) p volume ≤
          L * ENNReal.ofReal S * eLpNorm w p volume := by
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fourierInv_shiftedMultiplier_le_mul (V := V) (W := W)
    (n := n) (t := t) hp hp_top
  set ρ : CoordinateSpace n → ℝ := fun η ↦ (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  set I : ℝ≥0∞ := ∫⁻ η, ENNReal.ofReal (ρ η)
  have hI : I ≠ (∞ : ℝ≥0∞) := integrable_one_add_norm_sq_rpow_neg_succ_div_two.lintegral_lt_top.ne
  refine ⟨C₀ * I.toNNReal, fun b hb S hS0 hS w ↦ ?_⟩
  obtain ⟨T, hTdef⟩ : ∃ T : CoordinateSpace n → CoordinateSpace n → W,
      T = fun η x ↦ 𝓕⁻ (fun ζ ↦ shiftedMultiplier b η ζ (𝓕 w ζ)) x := ⟨_, rfl⟩
  have hT (η : CoordinateSpace n) :
      eLpNorm (T η) p volume ≤ C₀ * ENNReal.ofReal (S * ρ η) * eLpNorm w p volume := by
    rw [hTdef]
    exact hC₀ b hb S hS0 hS η w
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ T q.2 q.1 := by
    rw [hTdef]
    exact hb.continuous_fourierInv_shiftedMultiplier w
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
    _ = C₀ * I * ENNReal.ofReal S * eLpNorm w p volume := by
        simp only [ENNReal.ofReal_mul hS0, ← mul_assoc]
        rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
          mul_right_comm (C₀ : ℝ≥0∞)]
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hI]

/-- **The `Lᵖ` estimate.** Let `1 < p < ∞`. There is a constant `L`, depending only on `n`, `t`,
`p`, `V` and `W`, with the following property. If `b` is a symbol of order `t` with compact spatial
support and the derivatives of order at most `n + 1` of `ξ ↦ b̂(η, ξ)` are bounded by
`B ⟨ξ⟩ ^ (t - j) ⟨η⟩ ^ (-R)`, where `R = (n + 1) + |t| + (n + 1)`, then the quantization of the
composition symbol `⟨ξ⟩ ^ (-t) # b` satisfies `‖Op(⟨ξ⟩ ^ (-t) # b) w‖_p ≤ L B ‖w‖_p` on Schwartz
functions. -/
private theorem exists_eLpNorm_quantizeSchwartzValue_sharp_le_mul {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ L : ℝ≥0, ∀ (b : Symbol n V W t) (hb : b.HasCompactSpatialSupport) (B : ℝ), 0 ≤ B →
      (∀ j ≤ n + 1, ∀ η ξ : CoordinateSpace n,
        ‖iteratedFDeriv ℝ j (fun ξ ↦ 𝓕 (fun y ↦ b.coefficient (y, ξ)) η) ξ‖ ≤
          B * (1 + ‖ξ‖ ^ 2) ^ ((t - j) / 2) *
            (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1 + |-t| + ((n + 1 : ℕ) : ℝ)) / 2)) →
      ∀ w : 𝓢(CoordinateSpace n, V),
        eLpNorm (quantizeSchwartzValue
          ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient w) p volume ≤
          L * ENNReal.ofReal B * eLpNorm w p volume := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · -- In dimension `0` the estimate is explicit.
    set μ : ℝ := (volume : Measure (CoordinateSpace 0)).real Set.univ
    refine ⟨(μ * (μ * μ)).toNNReal, fun b hb B _ hB w ↦ ?_⟩
    have hc := norm_coefficient_besselPotential_sharp_le_of_dim_zero hb
      (by simpa using hB 0 (Nat.zero_le _) 0 0)
    have hc' : μ * (‖((besselPotential (-t) : Symbol 0 W W (-t)).sharp b hb).coefficient
        (0, 0)‖ * μ) ≤ μ * (μ * μ) * B :=
      calc _ ≤ μ * (B * μ * μ) := by gcongr
        _ = _ := by ring
    refine (eLpNorm_quantizeSchwartzValue_le_of_dim_zero _ p w).trans ?_
    calc _ ≤ ENNReal.ofReal (μ * (μ * μ) * B) * eLpNorm w p volume := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofNNReal_toNNReal]
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨L, hL⟩ := exists_eLpNorm_quantizeSchwartzValue_sharp_le_mul_of_shiftedMultiplier
    (V := V) (W := W) (n := n) (t := t) hp hp_top
  choose M hM0 hM using fun k : ℕ ↦
    exists_norm_iteratedFDeriv_shiftedMultiplier_le_mul (V := V) (W := W) (n := n) (t := t) k
      ((n : ℝ) + 1)
  set M' : ℝ := ∑ k ∈ Finset.range (n + 2), M k
  obtain ⟨hM'0, hM'⟩ := sum_range_nonneg_and_le hM0 (n + 2)
  refine ⟨L * M'.toNNReal, fun b hb B hB0 hB w ↦ ?_⟩
  refine (hL b hb (M' * B) (mul_nonneg hM'0 hB0) (fun k hk η ζ ↦ ?_) w).trans_eq ?_
  · refine (hM k b hb B hB0 (fun j hj η ξ ↦ (hB j (hj.trans hk) η ξ).trans ?_) η ζ).trans ?_
    · have hη : 1 ≤ 1 + ‖η‖ ^ 2 := by nlinarith [sq_nonneg ‖η‖]
      have hk' : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hk
      gcongr
    · gcongr
      exact hM' k (by omega)
  · rw [ENNReal.ofReal_mul hM'0, ENNReal.coe_mul, ← mul_assoc, ENNReal.ofNNReal_toNNReal]

variable [CompleteSpace V] [CompleteSpace W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- **From `Lᵖ` to `H^{s,p}`.** Let `b = a ⟨ξ⟩ ^ (-s)`, of order `m - s`. A constant `C` in the
`Lᵖ` estimate for `Op(⟨ξ⟩ ^ (s - m) # b)` on Schwartz functions bounds
`Op(a) : H^{s,p} → H^{s - m,p}` on Schwartz functions. -/
private theorem HasCompactSpatialSupport.norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {m : ℝ} {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {C : ℝ≥0}
    (hC : ∀ w : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue ((besselPotential (-(m + -s)) : Symbol n W W _).sharp
        (a.comp (besselPotential (-s))) (ha.comp_right _)).coefficient w) p volume ≤
        C * eLpNorm w p volume)
    (u : 𝓢(CoordinateSpace n, V)) :
    ‖toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha.isUniform u)‖ ≤
      C * ‖toBesselPotentialSpaceCLM s p u‖ := by
  -- Write `u = J^{-s} w` with `w = J^s u`, so that `Op(a) u = Op(b) w` for the symbol
  -- `b = a ⟨ξ⟩^(-s)` of order `m - s`, and `J^{s-m} Op(b) = Op(⟨ξ⟩^(s - m) # b)`.
  set b : Symbol n V W (m + -s) := a.comp (besselPotential (-s))
  have hb : b.HasCompactSpatialSupport := ha.comp_right _
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

/-- On Schwartz functions, `Op(a) : H^{s,p} → H^{s - m,p}` is bounded. -/
private theorem HasCompactSpatialSupport.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {m : ℝ} {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha.isUniform u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s p u‖ := by
  have hb := ha.comp_right (besselPotential (-s) : Symbol n V V (-s))
  obtain ⟨L, hL⟩ := exists_eLpNorm_quantizeSchwartzValue_sharp_le_mul (V := V) (W := W) (n := n)
    (t := m + -s) hp hp_top
  choose B hB0 hB using fun j : ℕ ↦ hb.exists_norm_iteratedFDeriv_fourier_slice_le j
    ((n : ℝ) + 1 + |-(m + -s)| + ((n + 1 : ℕ) : ℝ))
  set B' : ℝ := ∑ j ∈ Finset.range (n + 2), B j
  obtain ⟨hB'0, hB'⟩ := sum_range_nonneg_and_le hB0 (n + 2)
  refine ⟨L * B'.toNNReal, ha.norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s fun w ↦
    (hL _ hb B' hB'0 (fun j hj η ξ ↦ (hB j η ξ).trans ?_) w).trans_eq ?_⟩
  · gcongr
    exact hB' j (by omega)
  · rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]

/-! ### The operator on `H^{s,p}` -/

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- **Pseudodifferential operators on `H^{s,p}`.** For a symbol `a` of order `m` whose estimates
are uniform in the position, the left quantization `Op(a)` as a bounded operator
`H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)`. Let `1 < p < ∞`. If `a` has compact spatial support and
`V` and `W` are finite-dimensional, or if `V` and `W` are complex Hilbert spaces, it extends
`Op(a)` from Schwartz functions: on a Schwartz function `u` it is the Schwartz function `Op(a) u`
(`HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM` and
`quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM` in the namespace `TauCeti.Symbol`),
and by density of the Schwartz functions it is the unique continuous linear map with this property
(`BesselPotentialSpace.continuousLinearMap_ext`). Otherwise its value is unspecified. For `p = 2`,
complex Hilbert spaces `V` and `W` and compact spatial support it is
`TauCeti.Symbol.quantizeSobolev`
(`HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_two` in the namespace
`TauCeti.Symbol`). -/
def quantizeUniformBesselPotentialSpace {m : ℝ} (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    H^{s, p}(CoordinateSpace n, V) →L[ℂ] H^{s - m, p}(CoordinateSpace n, W) :=
  ((toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) p).comp
    (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
      (toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s p).toLinearMap

section Operator

variable {m m' : ℝ} {a : Symbol n V W m} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- **The extension property from the `H^{s,p}` estimate.** Let `p < ∞`. If
`‖Op(a) u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}` for every Schwartz function `u`, then on a Schwartz
function `u` the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the Schwartz function `Op(a) u`. -/
theorem quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le
    (ha : a.IsUniform) {s : ℝ} (hp_top : p ≠ (∞ : ℝ≥0∞)) {C : ℝ}
    (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s p u‖)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u) := by
  rw [quantizeUniformBesselPotentialSpace,
    ← ContinuousLinearMap.coe_coe (toBesselPotentialSpaceCLM s p),
    LinearMap.extendOfNorm_eq (denseRange_toBesselPotentialSpaceCLM s hp_top)]
  · simp
  · exact ⟨C, by simpa using hC⟩

section Extension

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **The extension property.** `a.HasBesselPotentialSpaceExtension ha p` states that for every
real `s` the operator `Op(a) : H^{s,p} → H^{s - m,p}` extends `Op(a)` from Schwartz functions: on a
Schwartz function `u` it is the Schwartz function `Op(a) u`. For `1 < p < ∞` this holds if `a` has
compact spatial support and `V` and `W` are finite-dimensional
(`TauCeti.Symbol.HasCompactSpatialSupport.hasBesselPotentialSpaceExtension`), and if `V` and `W`
are complex Hilbert spaces (`TauCeti.Symbol.IsUniform.hasBesselPotentialSpaceExtension`). The
linearity of the operator in the symbol and its compatibility with the inclusions and with
composition follow from this property alone. -/
def HasBesselPotentialSpaceExtension (a : Symbol n V W m) (ha : a.IsUniform) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : Prop :=
  ∀ (s : ℝ) (u : 𝓢(CoordinateSpace n, V)),
    a.quantizeUniformBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u)

/-- Unfolding `TauCeti.Symbol.HasBesselPotentialSpaceExtension`. -/
theorem hasBesselPotentialSpaceExtension_iff {ha : a.IsUniform} :
    a.HasBesselPotentialSpaceExtension ha p ↔
      ∀ (s : ℝ) (u : 𝓢(CoordinateSpace n, V)),
        a.quantizeUniformBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
          toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u) :=
  Iff.rfl

namespace HasBesselPotentialSpaceExtension

variable {ha : a.IsUniform}

/-- On a Schwartz function `u`, the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the Schwartz
function `Op(a) u`. -/
theorem quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM
    (h : a.HasBesselPotentialSpaceExtension ha p) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u) :=
  h s u

/-- **Identities of tempered distributions by density.** Let `p < ∞`. If a continuous linear map
`T : H^{s,p} → 𝓢'` takes each Schwartz function `u` to the Schwartz function `Op(a) u`, then it
takes every `u ∈ H^{s,p}` to the tempered distribution of `Op(a) u`. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall
    (h : a.HasBesselPotentialSpaceExtension ha p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ}
    (T : H^{s, p}(CoordinateSpace n, V) →L[ℂ] 𝓢'(CoordinateSpace n, W))
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (toBesselPotentialSpaceCLM s p u) = (quantizeUniformCLM a ha u : 𝓢'(CoordinateSpace n, W)))
    (u : H^{s, p}(CoordinateSpace n, V)) :
    (a.quantizeUniformBesselPotentialSpace ha s p u).toDistr = T u := by
  have key : BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
      a.quantizeUniformBesselPotentialSpace ha s p = T :=
    BesselPotentialSpace.continuousLinearMap_ext hp_top fun v ↦ by simp [h s v, hT v]
  simpa using congr($key u)

/-- **The extension property from comparison operators.** Let `p < ∞`. If for every real `s`
some continuous linear map `H^{s,p} → H^{s - m,p}` takes each Schwartz function `u` to the Schwartz
function `Op(a) u`, then `a` has the extension property. -/
private theorem of_forall_exists (hp_top : p ≠ (∞ : ℝ≥0∞))
    (h : ∀ s, ∃ T : H^{s, p}(CoordinateSpace n, V) →L[ℂ] H^{s - m, p}(CoordinateSpace n, W),
      ∀ u, T (toBesselPotentialSpaceCLM s p u) =
        toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u)) :
    a.HasBesselPotentialSpaceExtension ha p := fun s u ↦ by
  obtain ⟨T, hT⟩ := h s
  exact quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le ha hp_top
    (C := ‖T‖) (fun v ↦ hT v ▸ T.le_opNorm _) u

/-- Let `p < ∞`. The extension property is preserved by sums of symbols. -/
theorem add {b : Symbol n V W m} {hb : b.IsUniform} (ha' : a.HasBesselPotentialSpaceExtension ha p)
    (hb' : b.HasBesselPotentialSpaceExtension hb p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a + b).HasBesselPotentialSpaceExtension (ha.add hb) p :=
  of_forall_exists hp_top fun s ↦ ⟨a.quantizeUniformBesselPotentialSpace ha s p +
    b.quantizeUniformBesselPotentialSpace hb s p,
    fun u ↦ by simp [ha' s u, hb' s u, quantizeUniformCLM_add ha hb]⟩

/-- Let `p < ∞`. The extension property is preserved by scalar multiples of symbols. -/
theorem smul (ha' : a.HasBesselPotentialSpaceExtension ha p) (c : ℂ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (c • a).HasBesselPotentialSpaceExtension (ha.smul c) p :=
  of_forall_exists hp_top fun s ↦ ⟨c • a.quantizeUniformBesselPotentialSpace ha s p,
    fun u ↦ by simp [ha' s u, quantizeUniformCLM_smul ha]⟩

/-- Let `p < ∞`. The extension property is preserved by negating the symbol. -/
theorem neg (ha' : a.HasBesselPotentialSpaceExtension ha p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (-a).HasBesselPotentialSpaceExtension ha.neg p :=
  of_forall_exists hp_top fun s ↦ ⟨-a.quantizeUniformBesselPotentialSpace ha s p,
    fun u ↦ by simp [ha' s u, quantizeUniformCLM_neg ha]⟩

/-- Let `p < ∞`. The extension property is preserved by differences of symbols. -/
theorem sub {b : Symbol n V W m} {hb : b.IsUniform} (ha' : a.HasBesselPotentialSpaceExtension ha p)
    (hb' : b.HasBesselPotentialSpaceExtension hb p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a - b).HasBesselPotentialSpaceExtension (ha.sub hb) p :=
  of_forall_exists hp_top fun s ↦ ⟨a.quantizeUniformBesselPotentialSpace ha s p -
    b.quantizeUniformBesselPotentialSpace hb s p,
    fun u ↦ by simp [ha' s u, hb' s u, quantizeUniformCLM_sub ha hb]⟩

/-- Let `p < ∞`. The extension property is preserved by viewing a symbol of order `m` as a symbol
of order `m' ≥ m`. -/
theorem inclusion (ha' : a.HasBesselPotentialSpaceExtension ha p) (h : m ≤ m')
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (Symbol.inclusion h a).HasBesselPotentialSpaceExtension (ha.inclusion h) p :=
  of_forall_exists hp_top fun s ↦ ⟨BesselPotentialSpace.inclusion (by linarith) ∘L
      a.quantizeUniformBesselPotentialSpace ha s p,
    fun u ↦ by simp [ha' s u, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
      quantizeUniformCLM_inclusion ha h]⟩

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is additive in the symbol. -/
theorem quantizeUniformBesselPotentialSpace_add {b : Symbol n V W m} {hb : b.IsUniform}
    (ha' : a.HasBesselPotentialSpaceExtension ha p) (hb' : b.HasBesselPotentialSpaceExtension hb p)
    (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a + b).quantizeUniformBesselPotentialSpace (ha.add hb) s p =
      a.quantizeUniformBesselPotentialSpace ha s p +
        b.quantizeUniformBesselPotentialSpace hb s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [ha' s u, hb' s u, ha'.add hb' hp_top s u, quantizeUniformCLM_add ha hb]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is homogeneous in the symbol. -/
theorem quantizeUniformBesselPotentialSpace_smul (ha' : a.HasBesselPotentialSpaceExtension ha p)
    (c : ℂ) (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (c • a).quantizeUniformBesselPotentialSpace (ha.smul c) s p =
      c • a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [ha' s u, ha'.smul c hp_top s u, quantizeUniformCLM_smul ha]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes the negated symbol to the negated
operator. -/
theorem quantizeUniformBesselPotentialSpace_neg (ha' : a.HasBesselPotentialSpaceExtension ha p)
    (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (-a).quantizeUniformBesselPotentialSpace ha.neg s p =
      -a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [ha' s u, ha'.neg hp_top s u, quantizeUniformCLM_neg ha]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes differences of symbols to differences of
operators. -/
theorem quantizeUniformBesselPotentialSpace_sub {b : Symbol n V W m} {hb : b.IsUniform}
    (ha' : a.HasBesselPotentialSpaceExtension ha p) (hb' : b.HasBesselPotentialSpaceExtension hb p)
    (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a - b).quantizeUniformBesselPotentialSpace (ha.sub hb) s p =
      a.quantizeUniformBesselPotentialSpace ha s p -
        b.quantizeUniformBesselPotentialSpace hb s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [ha' s u, hb' s u, ha'.sub hb' hp_top s u, quantizeUniformCLM_sub ha hb]

/-- **Changing the order of the symbol.** Viewing a symbol of order `m` as a symbol of order
`m' ≥ m` gives the operator `H^{s,p} → H^{s - m,p}` followed by the inclusion
`H^{s - m,p} ⊆ H^{s - m',p}`. -/
theorem quantizeUniformBesselPotentialSpace_inclusion
    (ha' : a.HasBesselPotentialSpaceExtension ha p) (h : m ≤ m') (s : ℝ)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (Symbol.inclusion h a).quantizeUniformBesselPotentialSpace (ha.inclusion h) s p =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [ha' s u, ha'.inclusion h hp_top s u,
    BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM, quantizeUniformCLM_inclusion ha h]

/-- **Changing the Sobolev order.** The operators `Op(a) : H^{s,p} → H^{s - m,p}` for the different
orders `s` are compatible with the inclusions `H^{s,p} ⊆ H^{r,p}`. -/
theorem quantizeUniformBesselPotentialSpace_comp_inclusion
    (ha' : a.HasBesselPotentialSpaceExtension ha p) {r s : ℝ} (h : r ≤ s)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    a.quantizeUniformBesselPotentialSpace ha r p ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [ha' r u, ha' s u, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]

/-- **Compatibility of the extensions.** The operator `Op(a) : H^{s,p} → H^{s - m,p}` only depends
on the coefficient of `a` and on the tempered distribution of its argument: symbols `a` and `b` of
orders `m` and `m'` with the same coefficient give the same tempered distribution on
`u ∈ H^{s,p}` and `v ∈ H^{t,p}` whenever `u` and `v` have the same tempered distribution. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_congr {b : Symbol n V W m'} {hb : b.IsUniform}
    (ha' : a.HasBesselPotentialSpaceExtension ha p) (hb' : b.HasBesselPotentialSpaceExtension hb p)
    (hab : a.coefficient = b.coefficient) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s t : ℝ}
    {u : H^{s, p}(CoordinateSpace n, V)} {v : H^{t, p}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformBesselPotentialSpace ha s p u).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb t p v).toDistr :=
  SchwartzMap.toDistr_apply_congr_of_comp_eq hp_top (A := quantizeUniformCLM a ha)
    (ContinuousLinearMap.ext fun u ↦ by simp [ha' s u])
    (ContinuousLinearMap.ext fun u ↦ by simp [hb' t u, quantizeUniformCLM_congr ha hb hab]) huv

/-- **Composition of quantizations on `H^{s,p}`.** If the symbol `c` of order `m''` quantizes to
the composition `Op(a) ∘ Op(b)` of symbols of orders `m'` and `m` on Schwartz space, then
`Op(c) : H^{s,p} → H^{s - m'',p}` is the composition of `Op(b) : H^{s,p} → H^{s - m,p}` and
`Op(a) : H^{s - m,p} → H^{s - m - m',p}`, as maps of tempered distributions. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_comp {U : Type*} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [CompleteSpace U] {m'' : ℝ} {a : Symbol n W U m'} {b : Symbol n V W m}
    {c : Symbol n V U m''} {ha : a.IsUniform} {hb : b.IsUniform} {hc : c.IsUniform}
    (ha' : a.HasBesselPotentialSpaceExtension ha p) (hb' : b.HasBesselPotentialSpaceExtension hb p)
    (hc' : c.HasBesselPotentialSpaceExtension hc p)
    (habc : quantizeUniformCLM a ha ∘L quantizeUniformCLM b hb = quantizeUniformCLM c hc) (s : ℝ)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    (c.quantizeUniformBesselPotentialSpace hc s p u).toDistr =
      (a.quantizeUniformBesselPotentialSpace ha (s - m) p
        (b.quantizeUniformBesselPotentialSpace hb s p u)).toDistr := by
  simpa using hc'.toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall hp_top
    (BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
      a.quantizeUniformBesselPotentialSpace ha (s - m) p ∘L
        b.quantizeUniformBesselPotentialSpace hb s p)
    (fun v ↦ by simp [ha' (s - m) (quantizeUniformCLM b hb v), hb' s v, ← habc]) u

/-- If `a` and `b` have the `H^{s,p}` extension property (`p < ∞`), so does their explicit
composition `a.uniformSharp b hb`. -/
theorem uniformSharp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    {a : Symbol n W U m'} {b : Symbol n V W m} {ha : a.IsUniform} {hb : b.IsUniform}
    (ha' : a.HasBesselPotentialSpaceExtension ha p) (hb' : b.HasBesselPotentialSpaceExtension hb p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a.uniformSharp b hb).HasBesselPotentialSpaceExtension (ha.uniformSharp hb) p :=
  of_forall_exists hp_top fun s ↦
    ⟨BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - (m' + m) ≤ s - m - m') ∘L
        a.quantizeUniformBesselPotentialSpace ha (s - m) p ∘L
          b.quantizeUniformBesselPotentialSpace hb s p, fun v ↦ by
      simp [hb' s v, ha' (s - m) (quantizeUniformCLM b hb v),
        BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
        quantizeUniformCLM_uniformSharp ha hb]⟩

/-- **Composition of uniform quantizations on `H^{s,p}`**: `Op(a # b) = Op(a) ∘ Op(b)` up to the
order-associativity inclusion `s - (m' + m) = s - m - m'`. -/
theorem quantizeUniformBesselPotentialSpace_uniformSharp {U : Type*} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [CompleteSpace U] {a : Symbol n W U m'} {b : Symbol n V W m}
    {ha : a.IsUniform} {hb : b.IsUniform} (ha' : a.HasBesselPotentialSpaceExtension ha p)
    (hb' : b.HasBesselPotentialSpaceExtension hb p) (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a.uniformSharp b hb).quantizeUniformBesselPotentialSpace (ha.uniformSharp hb) s p =
      BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - (m' + m) ≤ s - m - m') ∘L
        (a.quantizeUniformBesselPotentialSpace ha (s - m) p ∘L
          b.quantizeUniformBesselPotentialSpace hb s p) :=
  BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ by
    have hab' := ha'.uniformSharp hb' hp_top
    simp [hab' s u, hb' s u, ha' (s - m) (quantizeUniformCLM b hb u),
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
      quantizeUniformCLM_uniformSharp ha hb]

/-- **Composition of uniform quantizations on `H^{s,p}`**, as tempered distributions. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_uniformSharp {U : Type*} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [CompleteSpace U] {a : Symbol n W U m'} {b : Symbol n V W m}
    {ha : a.IsUniform} {hb : b.IsUniform} (ha' : a.HasBesselPotentialSpaceExtension ha p)
    (hb' : b.HasBesselPotentialSpaceExtension hb p) (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : H^{s, p}(CoordinateSpace n, V)) :
    ((a.uniformSharp b hb).quantizeUniformBesselPotentialSpace (ha.uniformSharp hb) s p u).toDistr =
      (a.quantizeUniformBesselPotentialSpace ha (s - m) p
        (b.quantizeUniformBesselPotentialSpace hb s p u)).toDistr :=
  toDistr_quantizeUniformBesselPotentialSpace_comp ha' hb' (ha'.uniformSharp hb' hp_top)
    (quantizeUniformCLM_uniformSharp ha hb).symm s hp_top u

/-- **Compatibility of the extensions for different exponents, the case `p < q`.** The Sobolev
embedding `H^{s,p} ⊆ H^{s - δ,q}`, `δ = n (1 / p - 1 / q)`, keeps the tempered distribution and
commutes with `Op(a)`. -/
private theorem toDistr_quantizeUniformBesselPotentialSpace_congr_of_lt [NeZero n]
    {b : Symbol n V W m'} {hb : b.IsUniform} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] (hap : a.HasBesselPotentialSpaceExtension ha p)
    (haq : a.HasBesselPotentialSpaceExtension ha q) (hbq : b.HasBesselPotentialSpaceExtension hb q)
    (hab : a.coefficient = b.coefficient) (hp : 1 < p) (hpq : p < q) {s t : ℝ}
    {u : H^{s, p}(CoordinateSpace n, V)} {v : H^{t, q}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformBesselPotentialSpace ha s p u).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb t q v).toDistr := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans hp
  set δ : ℝ := n * ((p : ℝ)⁻¹ - (q : ℝ)⁻¹)
  have hδ : 0 < δ := mul_pos (by exact_mod_cast Nat.pos_of_neZero n)
    (sub_pos.2 (inv_strictAnti₀ hp0 (by exact_mod_cast hpq)))
  have hpq' : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ (CoordinateSpace n) := by
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [finrank_euclideanSpace_fin]
    simp only [δ]
    field_simp
    ring
  set ι := (BesselPotentialSpace.sobolevEmbedding (CoordinateSpace n) V (s - δ) hδ hp hpq').comp
    (BesselPotentialSpace.inclusion (s := s) (p := p) (r := s - δ + δ) (sub_add_cancel s δ).le)
  have hι (w : H^{s, p}(CoordinateSpace n, V)) : (ι w).toDistr = w.toDistr := by
    simp [ι]
  have hu := hap.toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall ENNReal.coe_ne_top
    (BesselPotentialSpace.toDistrCLM _ W _ _ ∘L
      a.quantizeUniformBesselPotentialSpace ha (s - δ) q ∘L ι) (fun w ↦ by
        have hw : ι (toBesselPotentialSpaceCLM s p w) = toBesselPotentialSpaceCLM (s - δ) q w :=
          BesselPotentialSpace.ext (by rw [hι]; simp)
        simp [hw, haq (s - δ) w]) u
  simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply] at hu
  rw [hu]
  exact haq.toDistr_quantizeUniformBesselPotentialSpace_congr hbq hab ENNReal.coe_ne_top
    ((hι u).trans huv)

/-- **Compatibility of the extensions for different exponents.** For `1 < p, q < ∞` in positive
dimension, the operators `Op(a)` on `H^{s,p}` and `Op(b)` on `H^{t,q}`, for symbols with the same
coefficient, agree on any `u ∈ H^{s,p}` and `v ∈ H^{t,q}` with the same tempered distribution. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_congr_exponent [NeZero n]
    {b : Symbol n V W m'} {hb : b.IsUniform} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] (hap : a.HasBesselPotentialSpaceExtension ha p)
    (haq : a.HasBesselPotentialSpaceExtension ha q) (hbp : b.HasBesselPotentialSpaceExtension hb p)
    (hbq : b.HasBesselPotentialSpaceExtension hb q) (hab : a.coefficient = b.coefficient)
    (hp : 1 < p) (hq : 1 < q) {s t : ℝ} {u : H^{s, p}(CoordinateSpace n, V)}
    {v : H^{t, q}(CoordinateSpace n, V)} (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformBesselPotentialSpace ha s p u).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb t q v).toDistr := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · exact hap.toDistr_quantizeUniformBesselPotentialSpace_congr_of_lt haq hbq hab hp hpq huv
  · exact hap.toDistr_quantizeUniformBesselPotentialSpace_congr hbp hab ENNReal.coe_ne_top huv
  · exact (hbq.toDistr_quantizeUniformBesselPotentialSpace_congr_of_lt hbp hap hab.symm hq hqp
      huv.symm).symm

open scoped ContDiff in
/-- **Multiplication operators.** Let `p < ∞` and let `V` and `W` be finite-dimensional. For a
smooth `f : ℝⁿ → (V →L[ℂ] W)` such that the symbol `f(x)` of order `0` is uniform
(`TauCeti.Symbol.isUniform_ofSpatial_iff`) and has the extension property, this symbol quantizes to
multiplication by `f` on `H^{s,p}`. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_ofSpatial [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] {f : CoordinateSpace n → V →L[ℂ] W} {hf : ContDiff ℝ ∞ f}
    {ha : (ofSpatial f hf).IsUniform} (h : (ofSpatial f hf).HasBesselPotentialSpaceExtension ha p)
    (s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    ((ofSpatial f hf).quantizeUniformBesselPotentialSpace ha s p u).toDistr =
      TemperedDistribution.mulLeftCLM f u.toDistr := by
  have hA : f.HasTemperateGrowth := by
    simpa [coefficient_ofSpatial] using ha.hasTemperateGrowth_coefficient_slice 0
  refine (h.toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall hp_top
    (TemperedDistribution.mulLeftCLM f ∘L BesselPotentialSpace.toDistrCLM _ _ _ _)
    (fun v ↦ ?_) u).trans (by simp)
  simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
  rw [TemperedDistribution.mulLeftCLM_toTemperedDistributionCLM_eq hA]
  congr 1
  ext x
  simp only [quantizeUniformCLM_ofSpatial_apply, SchwartzMap.bilinLeftCLM_apply,
    ContinuousLinearMap.apply_apply]

end HasBesselPotentialSpaceExtension

/-- Let `p < ∞`. The zero symbol has the extension property. -/
theorem hasBesselPotentialSpaceExtension_zero {h : (0 : Symbol n V W m).IsUniform}
    (hp_top : p ≠ (∞ : ℝ≥0∞)) : (0 : Symbol n V W m).HasBesselPotentialSpaceExtension h p :=
  fun s u ↦ quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le h hp_top
    (C := 0) (fun v ↦ by simp [quantizeUniformCLM_zero h]) u

/-- The zero symbol quantizes to the zero operator `H^{s,p} → H^{s - m,p}`. -/
@[simp]
theorem quantizeUniformBesselPotentialSpace_zero {h : (0 : Symbol n V W m).IsUniform} (s : ℝ)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (0 : Symbol n V W m).quantizeUniformBesselPotentialSpace h s p = 0 := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hasBesselPotentialSpaceExtension_zero hp_top s u, quantizeUniformCLM_zero h]

/-- Every constant symbol `T : V →L[ℂ] W` has the `H^{s,p}` extension property (`p < ∞`),
unconditionally over arbitrary complete complex normed fibres. -/
theorem hasBesselPotentialSpaceExtension_const (T : V →L[ℂ] W) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (const T : Symbol n V W 0).HasBesselPotentialSpaceExtension (isUniform_const T) p :=
  HasBesselPotentialSpaceExtension.of_forall_exists hp_top fun s ↦
    ⟨BesselPotentialSpace.inclusion (sub_zero s).le ∘L
        BesselPotentialSpace.postcomp (CoordinateSpace n) s p T, fun v ↦ by
      rw [ContinuousLinearMap.comp_apply, ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
        BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM, quantizeUniformCLM_const]⟩

/-- A constant symbol `T : V →L[ℂ] W` quantizes on `H^{s,p}` (`p < ∞`) to
`BesselPotentialSpace.postcomp`, unconditionally over arbitrary complete complex normed fibres. -/
theorem quantizeUniformBesselPotentialSpace_const (T : V →L[ℂ] W) (s : ℝ)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (const T : Symbol n V W 0).quantizeUniformBesselPotentialSpace (isUniform_const T) s p =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L
        BesselPotentialSpace.postcomp (CoordinateSpace n) s p T :=
  BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ by
    rw [(hasBesselPotentialSpaceExtension_const T
        hp_top).quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM s u,
      ContinuousLinearMap.comp_apply, ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM, quantizeUniformCLM_const]

private theorem toLpₗᵢ_symm_toLpₗᵢ_eq_quantizeUniformCLM_besselPotential (m s : ℝ)
    (u : 𝓢(CoordinateSpace n, V)) :
    (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V (s - m) p).symm
        (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V s p
          (toBesselPotentialSpaceCLM s p u)) =
      toBesselPotentialSpaceCLM (s - m) p
        (quantizeUniformCLM (besselPotential m) (isUniform_besselPotential m) u) :=
  BesselPotentialSpace.ext <| by
    simp [quantizeUniformCLM_besselPotential,
      ← TemperedDistribution.besselPotential_toTemperedDistributionCLM_eq]

/-- The Bessel-potential symbol `⟨ξ / 2π⟩ ^ m` has the `H^{s,p}` extension property (`p < ∞`),
unconditionally over arbitrary complete complex normed fibres. -/
theorem hasBesselPotentialSpaceExtension_besselPotential (m : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (besselPotential m : Symbol n V V m).HasBesselPotentialSpaceExtension
      (isUniform_besselPotential m) p :=
  HasBesselPotentialSpaceExtension.of_forall_exists hp_top fun s ↦
    ⟨((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V (s - m) p).symm.toContinuousLinearEquiv :
        Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ]
          H^{s - m, p}(CoordinateSpace n, V)) ∘L
      ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V s p).toContinuousLinearEquiv :
        H^{s, p}(CoordinateSpace n, V) →L[ℂ] Lp V p (volume : Measure (CoordinateSpace n))),
      toLpₗᵢ_symm_toLpₗᵢ_eq_quantizeUniformCLM_besselPotential m s⟩

/-- **Action of `Symbol.besselPotential` on `H^{s,p}`** (`p < ∞`) as the canonical isometric
isomorphism `H^{s,p} → H^{s - m,p}`, unconditionally over arbitrary complete complex normed
fibres. -/
theorem quantizeUniformBesselPotentialSpace_besselPotential (m s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (besselPotential m : Symbol n V V m).quantizeUniformBesselPotentialSpace
        (isUniform_besselPotential m) s p =
      ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V (s - m) p).symm.toContinuousLinearEquiv :
          Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ]
            H^{s - m, p}(CoordinateSpace n, V)) ∘L
        ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V s p).toContinuousLinearEquiv :
          H^{s, p}(CoordinateSpace n, V) →L[ℂ] Lp V p (volume : Measure (CoordinateSpace n))) :=
  BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ by
    rw [(hasBesselPotentialSpaceExtension_besselPotential m
        hp_top).quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM s u,
      ← toLpₗᵢ_symm_toLpₗᵢ_eq_quantizeUniformCLM_besselPotential m s u]
    rfl

/-- On tempered distributions, `Op(⟨ξ / 2π⟩ ^ m)` acts on `H^{s,p}` (`p < ∞`) as
`TemperedDistribution.besselPotential`. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_besselPotential (m s : ℝ)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    ((besselPotential m : Symbol n V V m).quantizeUniformBesselPotentialSpace
        (isUniform_besselPotential m) s p u).toDistr =
      TemperedDistribution.besselPotential (CoordinateSpace n) V m u.toDistr := by
  rw [quantizeUniformBesselPotentialSpace_besselPotential m s hp_top,
    ContinuousLinearMap.comp_apply]
  simpa [sub_sub_cancel] using BesselPotentialSpace.toDistr_toLpₗᵢ_symm_toLpₗᵢ (r := s - m) u

/-- **Uniformly smoothing operators gain every number of derivatives.** If uniform symbols between
`V` and `W` have the `H^{·,p}` extension property (`p < ∞`), a uniformly smoothing symbol `a`
quantizes to a bounded operator `T : H^{r,p} →L[ℂ] H^{s,p}` agreeing with `Op(a)` on tempered
distributions across all orders `t`. -/
theorem IsUniformlySmoothing.exists_toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall
    (ha : a.IsUniformlySmoothing) (r s : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hext : ∀ ⦃μ : ℝ⦄ ⦃b : Symbol n V W μ⦄ (hb : b.IsUniform),
      b.HasBesselPotentialSpaceExtension hb p) :
    ∃ T : H^{r, p}(CoordinateSpace n, V) →L[ℂ] H^{s, p}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t, p}(CoordinateSpace n, V)} {u : H^{r, p}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr →
          (a.quantizeUniformBesselPotentialSpace ha.isUniform t p v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb, hba⟩ := isUniformlySmoothing_iff.mp ha (r - s)
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L
    b.quantizeUniformBesselPotentialSpace hb r p, fun {t _ _} huv ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
  exact (hext ha.isUniform).toDistr_quantizeUniformBesselPotentialSpace_congr (hext hb)
    hba.symm hp_top huv

/-- **Uniformly smoothing operators gain every order of regularity.** If uniform symbols between
`V` and `W` have the `H^{·,p}` extension property (`p < ∞`),
`(a.quantizeUniformBesselPotentialSpace ha.isUniform s p u).toDistr` belongs to `H^{t,p}`
(`TemperedDistribution.MemSobolev t p`) for every real `t`. -/
theorem IsUniformlySmoothing.memSobolev_toDistr_quantizeUniformBesselPotentialSpace_of_forall
    (ha : a.IsUniformlySmoothing) (s t : ℝ) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hext : ∀ ⦃μ : ℝ⦄ ⦃b : Symbol n V W μ⦄ (hb : b.IsUniform),
      b.HasBesselPotentialSpaceExtension hb p)
    (u : H^{s, p}(CoordinateSpace n, V)) :
    TemperedDistribution.MemSobolev t p
      (a.quantizeUniformBesselPotentialSpace ha.isUniform s p u).toDistr := by
  obtain ⟨T, hT⟩ :=
    ha.exists_toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall s t hp_top hext
  rw [hT (u := u) rfl]
  exact (T u).memSobolev_toDistr

end Extension

/-- **Mapping of pseudodifferential operators with compact spatial support on `H^{s,p}`.** Let
`1 < p < ∞`. On a Schwartz function `u`, the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the
Schwartz function `Op(a) u`. -/
@[simp]
theorem HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformBesselPotentialSpace ha.isUniform s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha.isUniform u) := by
  obtain ⟨C, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
  exact quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le ha.isUniform
    hp_top hC u

/-- For `1 < p < ∞`, a symbol with compact spatial support has the extension property
`TauCeti.Symbol.HasBesselPotentialSpaceExtension`. -/
theorem HasCompactSpatialSupport.hasBesselPotentialSpaceExtension (ha : a.HasCompactSpatialSupport)
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) : a.HasBesselPotentialSpaceExtension ha.isUniform p :=
  fun s ↦ ha.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM s hp hp_top

/-- For `p = 2`, complex Hilbert spaces as fibres and a symbol `a` of order `m` with compact
spatial support, the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the operator
`TauCeti.Symbol.quantizeSobolev` on `H^s`. -/
theorem HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_two {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {a : Symbol n H₁ H₂ m}
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    a.quantizeUniformBesselPotentialSpace ha.isUniform s 2 = a.quantizeSobolev ha s := by
  -- Both operators extend `Op(a)` from Schwartz functions, and `quantizeSobolev` bounds it.
  have h (u : 𝓢(CoordinateSpace n, H₁)) :
      a.quantizeSobolev ha s (toBesselPotentialSpaceCLM s 2 u) =
        toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha.isUniform u) := by
    refine BesselPotentialSpace.ext ?_
    ext φ
    rw [toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply, toDistr_toBesselPotentialSpaceCLM]
    simp [quantizeUniformCLM_apply]
  rw [quantizeUniformBesselPotentialSpace]
  refine LinearMap.extendOfNorm_unique
    (denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top)
    ‖a.quantizeSobolev ha s‖ (fun u ↦ ?_) _ (LinearMap.ext h)
  simpa [h] using (a.quantizeSobolev ha s).le_opNorm (toBesselPotentialSpaceCLM s 2 u)

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes differences of symbols to differences of
operators. -/
theorem HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_sub {b : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (a - b).quantizeUniformBesselPotentialSpace (ha.sub hb).isUniform s p =
      a.quantizeUniformBesselPotentialSpace ha.isUniform s p -
        b.quantizeUniformBesselPotentialSpace hb.isUniform s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_sub
    (hb.hasBesselPotentialSpaceExtension hp hp_top) s hp_top

/-- **The operator norm is controlled by a continuous seminorm of the symbol.** Let `1 < p < ∞`.
For a compact set `K` and a real `s` there is a continuous seminorm `q` on the symbols of order
`m` such that every symbol `a` vanishing at positions outside `K` satisfies
`‖Op(a)‖_{H^{s,p} → H^{s - m,p}} ≤ q(a)`. Frequency derivatives of `a` up to order `n + 1` enter
`q`, through Mihlin's condition. -/
theorem exists_norm_quantizeUniformBesselPotentialSpace_le_seminorm
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ q : Seminorm ℂ (Symbol n V W m), Continuous q ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          ‖a.quantizeUniformBesselPotentialSpace ha.isUniform s p‖ ≤ q a := by
  obtain ⟨L, hL⟩ := exists_eLpNorm_quantizeSchwartzValue_sharp_le_mul (V := V) (W := W) (n := n)
    (t := m + -s) hp hp_top
  choose q hq hqa using fun j : ℕ ↦ exists_norm_iteratedFDeriv_fourier_slice_le_seminorm
    (V := V) (W := W) (m := m + -s) K j ((n : ℝ) + 1 + |-(m + -s)| + ((n + 1 : ℕ) : ℝ))
  -- `T a = a ⟨ξ⟩ ^ (-s)`, the symbol whose Fourier slices enter the `Lᵖ` estimate.
  obtain ⟨T, hT⟩ : ∃ T : Symbol n V W m →L[ℂ] Symbol n V W (m + -s),
      T = compRightCLM (besselPotential (-s) : Symbol n V V (-s)) := ⟨_, rfl⟩
  have hqT (j : ℕ) : Continuous ((q j).comp T.toLinearMap) := by
    rw [Seminorm.coe_comp, ContinuousLinearMap.coe_coe]
    exact (hq j).comp T.continuous
  refine ⟨L • ∑ j ∈ Finset.range (n + 2), (q j).comp T.toLinearMap, ?_, fun a ha haK ↦ ?_⟩
  · simpa using (Seminorm.continuous_finsetSum fun j _ ↦ hqT j).const_smul L
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ j ∈ Finset.range (n + 2), q j (T a) := ⟨_, rfl⟩
  obtain ⟨hB0, hBj⟩ := sum_range_nonneg_and_le (fun j ↦ apply_nonneg (q j) (T a)) (n + 2)
  rw [← hB] at hB0 hBj
  have hqB : (L • ∑ j ∈ Finset.range (n + 2), (q j).comp T.toLinearMap :
      Seminorm ℂ (Symbol n V W m)) a = L * B := by
    simp [hB, NNReal.smul_def]
  have hTa : T a = a.comp (besselPotential (-s)) := by rw [hT, compRightCLM_apply]
  have hbK (x : CoordinateSpace n) (hx : x ∉ K) (ξ : CoordinateSpace n) :
      (a.comp (besselPotential (-s) : Symbol n V V (-s))).coefficient (x, ξ) = 0 := by
    rw [coefficient_comp, haK x hx ξ, ContinuousLinearMap.zero_comp]
  have hslice : ∀ j ≤ n + 1, ∀ η ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ j
        (fun ξ ↦ 𝓕 (fun y ↦ (a.comp (besselPotential (-s))).coefficient (y, ξ)) η) ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m + -s - j) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1 + |-(m + -s)| + ((n + 1 : ℕ) : ℝ)) / 2) :=
    fun j hj η ξ ↦ (hqa j _ hbK η ξ).trans (by
      gcongr
      rw [← hTa]
      exact hBj j (by omega))
  have hu := ha.norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s (C := L * B.toNNReal)
    fun w ↦ (hL _ (ha.comp_right _) B hB0 hslice w).trans_eq (by
      rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal])
  rw [hqB, quantizeUniformBesselPotentialSpace]
  refine LinearMap.opNorm_extendOfNorm_le (denseRange_toBesselPotentialSpaceCLM s hp_top)
    (mul_nonneg L.property hB0) fun u ↦ ?_
  simpa [NNReal.coe_mul, Real.coe_toNNReal _ hB0] using hu u

/-- **Continuity in the symbol.** Let `1 < p < ∞`. If `t ↦ a t` is a continuous family of symbols
of order `m` that all vanish at positions outside a fixed compact set `K`, then `t ↦ Op(a t)` is
continuous into the bounded operators `H^{s,p} → H^{s - m,p}` with the operator norm. -/
theorem continuous_quantizeUniformBesselPotentialSpace {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (hcont : Continuous a)
    {K : TopologicalSpace.Compacts (CoordinateSpace n)}
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    Continuous fun t ↦ (a t).quantizeUniformBesselPotentialSpace
      (hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩).isUniform s p := by
  obtain ⟨q, hq, hbound⟩ := exists_norm_quantizeUniformBesselPotentialSpace_le_seminorm (V := V)
    (W := W) (m := m) K s hp hp_top
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  have hK (t : X) : (a t).HasCompactSpatialSupport :=
    hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_) (g := fun t ↦ q (a t - a t₀)) ?_
  · rw [← (hK t).quantizeUniformBesselPotentialSpace_sub (hK t₀) s hp hp_top]
    exact hbound _ ((hK t).sub (hK t₀)) fun x hx ξ ↦ by simp [haK t x hx ξ, haK t₀ x hx ξ]
  · simpa [Function.comp_def] using
      (hq.comp (hcont.sub (continuous_const (y := a t₀)))).tendsto t₀

/-- **Compatibility of the extensions.** The operator `Op(a) : H^{s,p} → H^{s - m,p}` only depends
on the coefficient of `a` and on the tempered distribution of its argument: symbols `a` and `b` of
orders `m` and `m'` with the same coefficient give the same tempered distribution on
`u ∈ H^{s,p}` and `v ∈ H^{t,p}` whenever `u` and `v` have the same tempered distribution. -/
theorem HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_congr
    {b : Symbol n V W m'} (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport)
    (hab : a.coefficient = b.coefficient) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s t : ℝ}
    {u : H^{s, p}(CoordinateSpace n, V)} {v : H^{t, p}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformBesselPotentialSpace ha.isUniform s p u).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb.isUniform t p v).toDistr :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).toDistr_quantizeUniformBesselPotentialSpace_congr
    (hb.hasBesselPotentialSpaceExtension hp hp_top) hab hp_top huv

/-- **Multiplication operators.** For a Schwartz function `φ` such that the symbol `φ(x) id` of
order `0` has compact spatial support, for instance a compactly supported `φ`
(`TauCeti.Symbol.hasCompactSpatialSupport_ofSpatial_smul_id`), this symbol quantizes to
multiplication by `φ` on `H^{s,p}`. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_ofSpatial_smul_id (φ : 𝓢(CoordinateSpace n, ℂ))
    (h : (ofSpatial (fun x ↦ φ x • ContinuousLinearMap.id ℂ V)
      ((φ.smooth ⊤).smul contDiff_const)).HasCompactSpatialSupport)
    (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    ((ofSpatial _ _).quantizeUniformBesselPotentialSpace h.isUniform s p u).toDistr =
      TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) u.toDistr := by
  rw [HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_ofSpatial
    (h.hasBesselPotentialSpaceExtension hp hp_top) s hp_top,
    TemperedDistribution.mulLeftCLM_smul_id φ.hasTemperateGrowth]

/-- **Composition of quantizations on `H^{s,p}`.** For symbols `a` and `b` with compact spatial
support, the operator `Op(a # b) : H^{s,p} → H^{s - (m' + m),p}` is the composition of
`Op(b) : H^{s,p} → H^{s - m,p}` and `Op(a) : H^{s - m,p} → H^{s - m - m',p}`. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_sharp {U : Type*} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [FiniteDimensional ℂ U] [CompleteSpace U] {a : Symbol n W U m'}
    {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport)
    (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : H^{s, p}(CoordinateSpace n, V)) :
    ((a.sharp b hb).quantizeUniformBesselPotentialSpace (ha.sharp hb).isUniform s p u).toDistr =
      (a.quantizeUniformBesselPotentialSpace ha.isUniform (s - m) p
        (b.quantizeUniformBesselPotentialSpace hb.isUniform s p u)).toDistr := by
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
  exact HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_comp
    (ha.hasBesselPotentialSpaceExtension hp hp_top) (hb.hasBesselPotentialSpaceExtension hp hp_top)
    ((ha.sharp hb).hasBesselPotentialSpaceExtension hp hp_top)
    (ContinuousLinearMap.ext fun v ↦ (hq v).symm) s hp_top u

/-- **Compatibility of the extensions for different exponents.** For `1 < p, q < ∞` in positive
dimension, the operators `Op(a)` on `H^{s,p}` and `Op(b)` on `H^{t,q}`, for symbols with the same
coefficient, agree on any `u ∈ H^{s,p}` and `v ∈ H^{t,q}` with the same tempered distribution. -/
theorem HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_congr_exponent
    [NeZero n] {b : Symbol n V W m'} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : a.coefficient = b.coefficient) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hp : 1 < p) (hq : 1 < q) {s t : ℝ}
    {u : H^{s, p}(CoordinateSpace n, V)} {v : H^{t, q}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformBesselPotentialSpace ha.isUniform s p u).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb.isUniform t q v).toDistr :=
  HasBesselPotentialSpaceExtension.toDistr_quantizeUniformBesselPotentialSpace_congr_exponent
    (ha.hasBesselPotentialSpaceExtension (mod_cast hp) ENNReal.coe_ne_top)
    (ha.hasBesselPotentialSpaceExtension (mod_cast hq) ENNReal.coe_ne_top)
    (hb.hasBesselPotentialSpaceExtension (mod_cast hp) ENNReal.coe_ne_top)
    (hb.hasBesselPotentialSpaceExtension (mod_cast hq) ENNReal.coe_ne_top) hab hp hq huv

/-- **Spatial cutoffs.** For a smooth function `ψ` of temperate growth, the symbol `ψ(x) a(x, ξ)`
(`TauCeti.Symbol.smulLeft`) quantizes on `H^{s,p}` to `ψ` times the quantization of `a`. -/
theorem HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_smulLeft
    (ha : a.HasCompactSpatialSupport) {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψt : ψ.HasTemperateGrowth) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : H^{s, p}(CoordinateSpace n, V)) :
    ((Symbol.smulLeft hψ a).quantizeUniformBesselPotentialSpace (ha.smulLeft hψ).isUniform s p
        u).toDistr =
      TemperedDistribution.smulLeftCLM W ψ
        (a.quantizeUniformBesselPotentialSpace ha.isUniform s p u).toDistr := by
  have hq : quantizeUniformCLM _ (ha.smulLeft hψ).isUniform =
      (SchwartzMap.smulLeftCLM W ψ).comp (quantizeUniformCLM a ha.isUniform) := by
    ext v x
    rw [quantizeUniformCLM_apply, ContinuousLinearMap.comp_apply,
      SchwartzMap.smulLeftCLM_apply_apply hψt, quantizeUniformCLM_apply,
      quantizeSchwartzValue_congr_left (b := ψ x • a.coefficient) (fun ξ ↦ by simp),
      quantizeSchwartzValue_smul_left]
  simpa using ((ha.smulLeft hψ).hasBesselPotentialSpaceExtension hp
    hp_top).toDistr_quantizeUniformBesselPotentialSpace_eq_of_forall hp_top
    (TemperedDistribution.smulLeftCLM W ψ ∘L BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
      a.quantizeUniformBesselPotentialSpace ha.isUniform s p) (fun v ↦ by
      simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply,
        ha.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM s hp hp_top, hq,
        SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
      exact TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq _) u

end Operator

end Symbol

end TauCeti
