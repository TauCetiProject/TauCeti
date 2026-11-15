/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Fourier.MihlinHormander
import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
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
for every real `s` (`TauCeti.Symbol.exists_quantizeBesselPotentialSpace`). This is the `Lᵖ` form
of the Sobolev mapping theorem `TauCeti.Symbol.exists_quantizeSobolev` for `p = 2`; it is the
estimate behind the `Lᵖ` versions of local elliptic regularity.

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
by `C A_η` on `Lᵖ`, and Minkowski's integral inequality (`TauCeti.lintegral_Lp_lintegral_le`) sums
these bounds over `η`.

## Main declarations

* `TauCeti.Symbol.exists_quantizeBesselPotentialSpace`: the bounded operator
  `H^{s,p} → H^{s - m,p}` extending `Op(a)` from Schwartz functions.

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

/-- The rescaled slice `ζ ↦ b̂(η, 2πζ)` has derivatives `‖D^j‖ ≤ B ⟨ζ⟩ ^ (t - j) ⟨η⟩ ^ (-r)`. -/
private theorem HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_smul_le
    (hb : b.HasCompactSpatialSupport) (j : ℕ) (r : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ η ζ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ j (fun ζ ↦ 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) η) ζ‖ ≤
        B * (1 + ‖ζ‖ ^ 2) ^ ((t - j) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_iteratedFDeriv_fourier_slice_le j r
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  refine ⟨C * (2 * π) ^ j * (2 * π) ^ |t - j|, by positivity, fun η ζ ↦ ?_⟩
  have hw := one_add_norm_smul_sq_rpow_le h2π (t - j) ζ
  rw [iteratedFDeriv_comp_const_smul (2 * π)
    ((hb.contDiff_fourier_slice η).of_le (mod_cast le_top)), norm_smul, norm_pow,
    Real.norm_of_nonneg (by positivity)]
  calc (2 * π) ^ j * ‖iteratedFDeriv ℝ j (fun ξ ↦ 𝓕 (fun y ↦ b.coefficient (y, ξ)) η)
        ((2 * π) • ζ)‖
      ≤ (2 * π) ^ j * (C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((t - j) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-r / 2)) := by
        gcongr
        exact hC η _
    _ ≤ (2 * π) ^ j * (C * ((2 * π) ^ |t - j| * (1 + ‖ζ‖ ^ 2) ^ ((t - j) / 2)) *
          (1 + ‖η‖ ^ 2) ^ (-r / 2)) := by gcongr
    _ = _ := by ring

/-- The multiplier `ζ ↦ ⟨ζ + η⟩ ^ (-t) b̂(η, 2πζ)`. -/
private def shiftedMultiplier (b : Symbol n V W t) (η ζ : CoordinateSpace n) :
    V →L[ℂ] W :=
  (1 + ‖ζ + η‖ ^ 2) ^ (-t / 2) • 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) η

private theorem HasCompactSpatialSupport.contDiff_fourier_slice_smul
    (hb : b.HasCompactSpatialSupport) (η : CoordinateSpace n) :
    ContDiff ℝ ∞ fun ζ : CoordinateSpace n ↦ 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) η :=
  (hb.contDiff_fourier_slice η).comp (contDiff_const_smul _)

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
  have hζ : 0 < 1 + ‖ζ‖ ^ 2 := by positivity
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
        rw [← Real.rpow_add hζ, ← Real.rpow_add (by positivity), Nat.cast_sub hik]
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
  have hN := hb.continuous_shiftedMultiplier
  have he : Continuous fun y : CoordinateSpace n ↦ (𝐞 ⟪y, x⟫ : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  -- The integrand of the double integral is dominated by `‖𝓕 w ζ‖ C ⟨η⟩ ^ (-(n + 1))`.
  set F : CoordinateSpace n × CoordinateSpace n → W := fun q ↦
    (𝐞 ⟪q.1, x⟫ : ℂ) • (𝐞 ⟪q.2, x⟫ : ℂ) • shiftedMultiplier b q.2 q.1 (𝓕 w q.1) with hF
  have hFint : Integrable F (volume.prod volume) := by
    refine ((𝓕 w).integrable.norm.mul_prod
      (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul C)).mono' ?_
      (.of_forall fun q ↦ ?_)
    · exact ((he.comp continuous_fst).smul ((he.comp continuous_snd).smul
        (hN.clm_apply ((𝓕 w).continuous.comp continuous_fst)))).aestronglyMeasurable
    · simp only [hF, norm_smul, Circle.norm_coe, one_mul]
      calc ‖shiftedMultiplier b q.2 q.1 (𝓕 w q.1)‖ ≤ ‖shiftedMultiplier b q.2 q.1‖ * ‖𝓕 w q.1‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * (1 + ‖q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖𝓕 w q.1‖ := by gcongr; exact hC _ _
        _ = _ := by ring
  have hint (ζ : CoordinateSpace n) :
      Integrable fun η ↦ (𝐞 ⟪η, x⟫ : ℂ) • shiftedMultiplier b η ζ := by
    refine (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul C).mono'
      (he.smul (hN.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
      (.of_forall fun η ↦ ?_)
    simpa only [norm_smul, Circle.norm_coe, one_mul] using hC η ζ
  calc quantizeSchwartzValue ((besselPotential (-t) : Symbol n W W (-t)).sharp b hb).coefficient
        w x = ∫ ζ, ∫ η, F (ζ, η) := by
        rw [quantizeSchwartzValue_def]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [hF, coefficient_besselPotential_sharp,
          ContinuousLinearMap.integral_apply (hint ζ), Circle.smul_def]
        rw [← integral_smul]
        simp only [smul_apply]
    _ = ∫ η, ∫ ζ, F (ζ, η) := integral_integral_swap hFint
    _ = _ := by
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        simp only [hF, Real.fourierInv_eq, Circle.smul_def]
        rw [← integral_smul]
        simp only [smul_comm (𝐞 ⟪η, x⟫ : ℂ)]

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
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hp1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp_top hp.le
    rwa [ENNReal.toReal_one] at this
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
  have hg : AEMeasurable (Function.uncurry fun x η ↦ ‖T η x‖ₑ) (volume.prod volume) := by
    simpa only [Function.uncurry_def] using hcont.eNorm.measurable.aemeasurable
  have hsm : AEStronglyMeasurable (fun x ↦ ∫ η, (𝐞 ⟪η, x⟫ : ℂ) • T η x) volume := by
    have he : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪q.2, q.1⟫ : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
    exact (he.smul hcont).aestronglyMeasurable.integral_prod_right'
  have hTm (η : CoordinateSpace n) : AEStronglyMeasurable (T η) volume :=
    (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  rw [hsup, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hsm]
  calc (∫⁻ x, ‖∫ η, (𝐞 ⟪η, x⟫ : ℂ) • T η x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ (∫⁻ x, (∫⁻ η, ‖T η x‖ₑ) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr with x
        refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
        simp [eNorm_smul]
    _ ≤ ∫⁻ η, (∫⁻ x, ‖T η x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := lintegral_Lp_lintegral_le hg hp1
    _ = ∫⁻ η, eLpNorm (T η) p volume := by
        simp only [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top (hTm _)]
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

/-- **Mapping of pseudodifferential operators with compact spatial support on `H^{s,p}`.** Let
`1 < p < ∞`. For a symbol `a` of order `m` with compact spatial support between finite-dimensional
complex normed spaces and every real `s`, the quantization `Op(a)` extends from Schwartz functions
to a bounded operator `H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)`: on a Schwartz function `u` it is the
Schwartz function `Op(a) u` (`TauCeti.Symbol.quantizeUniformCLM`). By density of the Schwartz
functions such an operator is unique (`BesselPotentialSpace.continuousLinearMap_ext`). For `p = 2`
this is `TauCeti.Symbol.exists_quantizeSobolev`. -/
theorem exists_quantizeBesselPotentialSpace {m : ℝ} (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) (s : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ T : H^{s, p}(CoordinateSpace n, V) →L[ℂ] H^{s - m, p}(CoordinateSpace n, W),
      ∀ u : 𝓢(CoordinateSpace n, V), T (toBesselPotentialSpaceCLM s p u) =
        toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha.isUniform u) := by
  obtain ⟨C, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
  set f := ((toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) p).comp
    (quantizeUniformCLM a ha.isUniform)).toLinearMap
  set e := (toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s p).toLinearMap
  refine ⟨f.extendOfNorm e, fun u ↦ ?_⟩
  simpa [f, e] using LinearMap.extendOfNorm_eq (f := f) (e := e)
    (denseRange_toBesselPotentialSpaceCLM s hp_top) ⟨C, fun u ↦ by simpa [f, e] using hC u⟩ u

end Symbol

end TauCeti
