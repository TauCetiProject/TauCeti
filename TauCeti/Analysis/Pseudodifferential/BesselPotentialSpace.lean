/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
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

Every constant in this argument is linear in the bounds on the Fourier slices of `b`, and those are
controlled by continuous seminorms of `a` uniformly over the symbols vanishing outside a fixed
compact set (`TauCeti.Symbol.exists_norm_iteratedFDeriv_fourier_slice_le_seminorm`). So the
operator norm of `Op(a) : H^{s,p} → H^{s - m,p}` is at most a continuous seminorm of `a` on such
symbols (`TauCeti.Symbol.exists_norm_quantizeBesselPotentialSpace_le_seminorm`), and a continuous
family of them has quantizations that depend continuously on the parameter in the operator norm
(`TauCeti.Symbol.continuous_quantizeBesselPotentialSpace`). Unlike the case `p = 2`
(`TauCeti.Symbol.exists_norm_quantizeSobolev_le_sum_seminorm`), the seminorm involves frequency
derivatives of `a` of order up to `n + 1`, through Mihlin's condition.

## Main declarations

* `TauCeti.Symbol.quantizeBesselPotentialSpace`: the bounded operator `H^{s,p} → H^{s - m,p}`,
  which extends `Op(a)` from Schwartz functions
  (`TauCeti.Symbol.quantizeBesselPotentialSpace_toBesselPotentialSpaceCLM`).
* `TauCeti.Symbol.exists_norm_quantizeBesselPotentialSpace_le_seminorm`: for symbols vanishing
  outside a fixed compact set, the operator norm is at most a continuous seminorm of the symbol.
* `TauCeti.Symbol.continuous_quantizeBesselPotentialSpace`: continuity of `Op(a)` in the operator
  norm along a continuous family of such symbols.
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
          exact one_add_norm_sq_rpow_neg_le_inv_norm_pow hζ k
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

/-- **The operator norm is controlled by a continuous seminorm of the symbol.** Let `1 < p < ∞`.
For a compact set `K` and a real `s` there is a continuous seminorm `q` on the symbols of order
`m` such that every symbol `a` vanishing at positions outside `K` satisfies
`‖Op(a)‖_{H^{s,p} → H^{s - m,p}} ≤ q(a)`. Frequency derivatives of `a` up to order `n + 1` enter
`q`, through Mihlin's condition. -/
theorem exists_norm_quantizeBesselPotentialSpace_le_seminorm
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ q : Seminorm ℂ (Symbol n V W m), Continuous q ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          ‖a.quantizeBesselPotentialSpace ha s p‖ ≤ q a := by
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
  rw [hqB, quantizeBesselPotentialSpace]
  refine LinearMap.opNorm_extendOfNorm_le (denseRange_toBesselPotentialSpaceCLM s hp_top)
    (mul_nonneg L.property hB0) fun u ↦ ?_
  simpa [NNReal.coe_mul, Real.coe_toNNReal _ hB0] using hu u

/-- **Continuity in the symbol.** Let `1 < p < ∞`. If `t ↦ a t` is a continuous family of symbols
of order `m` that all vanish at positions outside a fixed compact set `K`, then `t ↦ Op(a t)` is
continuous into the bounded operators `H^{s,p} → H^{s - m,p}` with the operator norm. -/
theorem continuous_quantizeBesselPotentialSpace {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (hcont : Continuous a)
    {K : TopologicalSpace.Compacts (CoordinateSpace n)}
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    Continuous fun t ↦ (a t).quantizeBesselPotentialSpace
      (hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩) s p := by
  obtain ⟨q, hq, hbound⟩ := exists_norm_quantizeBesselPotentialSpace_le_seminorm (V := V)
    (W := W) (m := m) K s hp hp_top
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  have hK (t : X) : (a t).HasCompactSpatialSupport :=
    hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_) (g := fun t ↦ q (a t - a t₀)) ?_
  · rw [← quantizeBesselPotentialSpace_sub (hK t) (hK t₀) ((hK t).sub (hK t₀)) s hp hp_top]
    exact hbound _ _ fun x hx ξ ↦ by simp [haK t x hx ξ, haK t₀ x hx ξ]
  · simpa [Function.comp_def] using
      (hq.comp (hcont.sub (continuous_const (y := a t₀)))).tendsto t₀

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
  have hq : quantizeUniformCLM _ h.isUniform = SchwartzMap.smulLeftCLM V (φ : _ → ℂ) := by
    ext v x
    rw [quantizeUniformCLM_apply, quantizeSchwartzValue_ofSpatial,
      SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, _root_.smul_apply,
      ContinuousLinearMap.id_apply]
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
