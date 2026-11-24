/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.DyadicSymbol
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Zygmund estimates for pseudodifferential operators with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) that vanishes for positions
outside a compact set, with values in operators between finite-dimensional complex normed spaces.
The Hölder–Zygmund space `𝒞^r = B^r_{∞,∞}` (`TauCeti.BesovSpace V φ r ∞ ∞`) is measured by the
Littlewood–Paley blocks `Δⱼ` through `supⱼ 2^{jr} ‖Δⱼ u‖_∞`. This file proves that `Op(a)` maps
`𝒞^r` to `𝒞^{r - m}`, losing at most `m` orders of smoothness, for every real `r`: on Schwartz
functions,

`‖Op(a) u‖_{𝒞^{r - m}} ≤ C ‖u‖_{𝒞^r}`

(`HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional`),
in the blockwise form `2^{(r - m) j} ‖Δⱼ Op(a) u‖_∞ ≤ C supₖ 2^{rk} ‖Δₖ u‖_∞`
(`Symbol.HasCompactSpatialSupport.exists_rpow_mul_norm_fourierMultiplierCLM_quantizeUniformCLM_le`).
The constant does not depend on `u`. These are the Zygmund estimates of the Euclidean calculus,
the input for the Zygmund mapping of localized operators and for Schauder-type elliptic
regularity. The space `𝒞^r` contains bounded functions with no decay, so Schwartz functions are
not dense in it; extending the estimate from Schwartz functions to distributions is a separate
step.

For scalar symbols (`TauCeti.Symbol n ℂ ℂ m`, acting on complex-valued functions) the estimate
holds more generally on `B^r_{p,∞}` for every `1 ≤ p ≤ ∞`, which includes `𝒞^r` at `p = ∞`:
that is `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le`
in `TauCeti.Analysis.Pseudodifferential.Besov`. This file treats operator-valued symbols
`TauCeti.Symbol n V W m` between finite-dimensional spaces, for `p = q = ∞` only.

## The argument

Write `â(θ, ξ)` for the Fourier transform of the position slice `x ↦ a(x, ξ)` at `θ`. Since `a`
has compact spatial support, `â(θ, ξ)` decays faster than any power of `⟨θ⟩`, with symbol
estimates of order `m` in `ξ`. Expanding `a` in its Fourier transform in the position writes
`Op(a)` as the superposition `∫ 𝐞 ⟪θ, ·⟫ â(θ, D) dθ` of modulated Fourier multipliers. A frequency
cutoff `ψ` of `Op(a) u` is then the superposition of `𝐞 ⟪θ, ·⟫ 𝓕⁻ (ψ (· + θ) â(θ, 2π ·) 𝓕 u)`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourierInv_smul_fourier_quantizeSchwartzValue`).

For `ψ = ψⱼ`, the translate `ψⱼ (· + θ)` meets only the pieces `ψₖ` with
`2^{|j - k|} ≤ c (1 + ‖θ‖)` (`ContDiffBump.two_pow_le_of_inhomogeneousLittlewoodPaley_add_ne_zero`),
so it sees only `O(⟨θ⟩)` blocks `Δₖ u`. On each of them, the modulated multiplier is a convolution
with `𝓕⁻ ψⱼ (· + θ)`, whose `L¹` norm is that of `𝓕⁻ ψⱼ`, after a convolution with the kernel of
`Ψₖ(ζ) â(θ, 2πζ)`, for the enlarged cutoff `Ψₖ` equal to `1` on the support of `ψₖ`. That kernel
has `L¹` norm `O(2^{km} ⟨θ⟩ ^ (-ρ))` for every `ρ`
(`TauCeti.exists_integral_norm_fourierInv_cutoff_smul_le_of_finiteDimensional`, applied
uniformly in `θ`). Since `2^{(r - m)(j - k)} ≤ (c (1 + ‖θ‖)) ^ |r - m|` for the pieces met, the
contribution of `θ` to `2^{(r - m) j} ‖Δⱼ Op(a) u‖_∞` is `O(⟨θ⟩ ^ (-(n + 1)))` times
`supₖ 2^{rk} ‖Δₖ u‖_∞`, which is integrable in `θ`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (3.31)–(3.34).
* M. Taylor, *Pseudodifferential Operators and Nonlinear PDE*, Birkhäuser, 1991, Chapter 2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap RealInnerProductSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} {a : Symbol n V W m}

section Superposition

/-- The integrands of the superposition formula are integrable on the product: with
`G θ ζ = â(θ, 2πζ) 𝓕 u ζ`, both `(η, ζ) ↦ 𝐞 ⟪η, x⟫ ψ(η) G(η - ζ, ζ)` and
`(θ, ζ) ↦ 𝐞 ⟪θ + ζ, x⟫ ψ(θ + ζ) G(θ, ζ)`, since `‖G θ ζ‖ ≤ B ⟨ζ⟩ ^ m ‖𝓕 u ζ‖ ⟨θ⟩ ^ (-(n + 1))`. -/
private theorem HasCompactSpatialSupport.integrable_superposition
    (ha : a.HasCompactSpatialSupport) {ψ : CoordinateSpace n → ℂ} (hψ : Continuous ψ)
    (hψi : Integrable ψ) {D : ℝ} (hψD : ∀ ξ, ‖ψ ξ‖ ≤ D) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    Integrable (Function.uncurry fun η ζ : CoordinateSpace n ↦ 𝐞 ⟪η, x⟫ • ψ η •
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)) (volume.prod volume) ∧
    Integrable (Function.uncurry fun θ ζ : CoordinateSpace n ↦ 𝐞 ⟪θ + ζ, x⟫ • ψ (θ + ζ) •
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ)) (volume.prod volume) := by
  set G : CoordinateSpace n → CoordinateSpace n → W := fun θ ζ ↦
    𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ)
  obtain ⟨B, hB0, hB⟩ := ha.exists_norm_iteratedFDeriv_fourier_slice_smul_le 0 (n + 1)
  have hGle (θ ζ : CoordinateSpace n) : ‖G θ ζ‖ ≤
      (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * (B * (1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) := by
    have h := hB θ ζ
    rw [norm_iteratedFDeriv_zero, CharP.cast_eq_zero, sub_zero] at h
    calc ‖G θ ζ‖ ≤ ‖𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ‖ * ‖𝓕 u ζ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * (1 + ‖ζ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖𝓕 u ζ‖ := by
          gcongr
      _ = _ := by ring
  have hGc : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ G q.1 q.2 :=
    (ha.continuous_fourier_slice.comp (continuous_fst.prodMk
      (continuous_snd.const_smul (2 * π)))).clm_apply ((𝓕 u).continuous.comp continuous_snd)
  have hu : Integrable fun ζ : CoordinateSpace n ↦ B * (1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ := by
    simpa [mul_assoc] using ((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul B
  have hθ : Integrable fun θ : CoordinateSpace n ↦ (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by simp)
  refine ⟨((hψi.norm.mul_prod hu)).mono' ?_ (.of_forall fun q ↦ ?_),
    ((hθ.mul_prod hu).const_mul D).mono' ?_ (.of_forall fun q ↦ ?_)⟩
  · exact ((Real.continuous_fourierChar.comp (continuous_fst.inner continuous_const)).smul
      ((hψ.comp continuous_fst).smul (hGc.comp ((continuous_fst.sub continuous_snd).prodMk
        continuous_snd)))).aestronglyMeasurable
  · simp only [Function.uncurry, Circle.norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_left ((hGle _ _).trans ?_) (norm_nonneg _)
    refine mul_le_of_le_one_left (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_)
    · simp only [le_add_iff_nonneg_right]; positivity
    · linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · exact ((Real.continuous_fourierChar.comp ((continuous_fst.add continuous_snd).inner
      continuous_const)).smul ((hψ.comp (continuous_fst.add continuous_snd)).smul
        hGc)).aestronglyMeasurable
  · simp only [Function.uncurry, Circle.norm_smul, norm_smul]
    exact mul_le_mul (hψD _) (hGle _ _) (norm_nonneg _) ((norm_nonneg _).trans (hψD 0))

/-- **A frequency cutoff of a quantization as a superposition.** Let `a` be a symbol with compact
spatial support and `ψ` a bounded integrable continuous function. For a Schwartz function `u`,
the frequency cutoff `𝓕⁻ (ψ 𝓕 (Op(a) u))` of `Op(a) u` is the superposition over `θ` of the
modulated functions `𝐞 ⟪θ, ·⟫ 𝓕⁻ (ψ (· + θ) â(θ, 2π ·) 𝓕 u)`, where `â(θ, ξ)` is the Fourier
transform of the position slice `x ↦ a(x, ξ)` at `θ`. -/
theorem HasCompactSpatialSupport.fourierInv_smul_fourier_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) {ψ : CoordinateSpace n → ℂ} (hψ : Continuous ψ)
    (hψi : Integrable ψ) {D : ℝ} (hψD : ∀ ξ, ‖ψ ξ‖ ≤ D) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    𝓕⁻ (fun η ↦ ψ η • 𝓕 (quantizeSchwartzValue a.coefficient u) η) x =
      ∫ θ, 𝐞 ⟪θ, x⟫ • ∫ ζ, 𝐞 ⟪ζ, x⟫ • ψ (ζ + θ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ) := by
  set G : CoordinateSpace n → CoordinateSpace n → W := fun θ ζ ↦
    𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ) with hG
  obtain ⟨hF₁, hF₂⟩ := ha.integrable_superposition hψ hψi hψD u x
  -- Fubini, the substitution `η = θ + ζ`, and Fubini again.
  calc 𝓕⁻ (fun η ↦ ψ η • 𝓕 (quantizeSchwartzValue a.coefficient u) η) x
      = ∫ η, ∫ ζ, 𝐞 ⟪η, x⟫ • ψ η • G (η - ζ) ζ := by
        rw [Real.fourierInv_eq]
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        simp only [ha.fourier_quantizeSchwartzValue, hG, Circle.smul_def]
        rw [← integral_smul, ← integral_smul]
    _ = ∫ ζ, ∫ η, 𝐞 ⟪η, x⟫ • ψ η • G (η - ζ) ζ := integral_integral_swap hF₁
    _ = ∫ ζ, ∫ θ, 𝐞 ⟪θ + ζ, x⟫ • ψ (θ + ζ) • G θ ζ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only
        rw [← integral_add_right_eq_self (fun η ↦ 𝐞 ⟪η, x⟫ • ψ η • G (η - ζ) ζ) ζ]
        simp
    _ = ∫ θ, ∫ ζ, 𝐞 ⟪θ + ζ, x⟫ • ψ (θ + ζ) • G θ ζ := (integral_integral_swap hF₂).symm
    _ = _ := by
        refine integral_congr_ae (.of_forall fun θ ↦ ?_)
        dsimp only
        rw [Circle.smul_def, ← integral_smul]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [hG, inner_add_left, AddChar.map_add_eq_mul, Circle.smul_def,
          mul_smul, add_comm θ ζ]
        exact smul_comm _ _ _

end Superposition

/-! ### The estimate for one translate -/

section Estimates

variable [CompleteSpace V] [FiniteDimensional ℂ V] [CompleteSpace W] [FiniteDimensional ℂ W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Kernels of the dyadic pieces of the rescaled slices.** For a symbol of order `m` with
compact spatial support, the kernels of `Ψₖ(ζ) â(θ, 2πζ)`, for the enlarged Littlewood–Paley
cutoffs `Ψₖ`, have `L¹` norm `O((2^k) ^ m ⟨θ⟩ ^ (-ρ))`, uniformly in `k` and `θ`, for every
`ρ`. -/
private theorem HasCompactSpatialSupport.exists_integral_norm_fourierInv_cutoff_slice_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (L : ℕ)
    (ρ : ℝ) :
    ∃ C, ∀ (θ : CoordinateSpace n) (k : ℕ),
      ∫ x, ‖𝓕⁻ (fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ) x‖ ≤
        C * (2 ^ k) ^ m * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) := by
  choose B hB0 hB using fun i : ℕ ↦ ha.exists_norm_iteratedFDeriv_fourier_slice_smul_le i ρ
  choose Bχ _ hBχ using fun k : ℕ ↦ φ.exists_norm_iteratedFDeriv_enlargedLittlewoodPaley_le L k
  obtain ⟨α, β, hα, hαβ⟩ := φ.exists_one_add_norm_sq_le_of_mem_tsupport_enlargedLittlewoodPaley L
  obtain ⟨C, hC⟩ := exists_integral_norm_fourierInv_cutoff_smul_le_of_finiteDimensional
    (E := CoordinateSpace n) (G := V →L[ℂ] W) m (N := n + 1) (by simp; omega) (b := β) hα Bχ
  -- One constant `S` serves all derivatives up to order `n + 1`.
  set S := ∑ i ∈ Finset.range (n + 2), B i
  refine ⟨C * S, fun θ k ↦ ?_⟩
  have hgm (i : ℕ) (hi : i ≤ n + 1) (ζ : CoordinateSpace n) :
      ‖iteratedFDeriv ℝ i (fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ) ζ‖ ≤
        S * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) * (1 + ‖ζ‖ ^ 2) ^ ((m - i) / 2) := by
    calc _ ≤ B i * (1 + ‖ζ‖ ^ 2) ^ ((m - i) / 2) * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) := hB i θ ζ
      _ ≤ S * (1 + ‖ζ‖ ^ 2) ^ ((m - i) / 2) * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) := by
          gcongr
          exact Finset.single_le_sum (fun j _ ↦ hB0 j) (Finset.mem_range.2 (by omega))
      _ = _ := by ring
  refine (hC _ _ (ha.contDiff_fourier_slice_smul θ) hgm (2 ^ k) (φ.enlargedLittlewoodPaley L k)
    (by positivity) (φ.contDiff_enlargedLittlewoodPaley L k) (hαβ k)
    fun i _ ξ ↦ hBχ i k ξ).trans_eq ?_
  ring

omit [CompleteSpace V] [FiniteDimensional ℂ V] [CompleteSpace W] [FiniteDimensional ℂ W] in
/-- **Decomposition of a translate along the pieces.** If `2^j φ.rOut + ‖θ‖ ≤ 2^K φ.rIn`, the
modulated piece attached to `θ` is the sum over `k ≤ K` of the same integrals with `𝓕 u`
replaced by `ψₖ 𝓕 u = 𝓕 (Δₖ u)`: on the support of `ψⱼ (· + θ)` the pieces `ψₖ`, `k ≤ K`,
sum to `1`. -/
private theorem HasCompactSpatialSupport.integral_fourierChar_smul_eq_sum
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n))
    (u : 𝓢(CoordinateSpace n, V)) (j : ℕ) (x θ : CoordinateSpace n) {K : ℕ}
    (hK : 2 ^ j * φ.rOut + ‖θ‖ ≤ 2 ^ K * φ.rIn) :
    ∫ ζ, 𝐞 ⟪ζ, x⟫ • (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ) =
      ∑ k ∈ Finset.range (K + 1), ∫ ζ, 𝐞 ⟪ζ, x⟫ •
        (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
          𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 (SchwartzMap.fourierMultiplierCLM V
            (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) := by
  have hint (k : ℕ) : Integrable fun ζ ↦ 𝐞 ⟪ζ, x⟫ •
      (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 (SchwartzMap.fourierMultiplierCLM V
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) := by
    set v : 𝓢(CoordinateSpace n, V) := SchwartzMap.fourierMultiplierCLM V
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u
    exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      ((Complex.continuous_ofReal.comp
        (φ.contDiff_inhomogeneousLittlewoodPaley_comp_add_right j θ (n := 0)).continuous).smul
        ((ha.contDiff_fourier_slice_smul θ).continuous.clm_apply
          (𝓕 v).continuous))).integrable_of_hasCompactSupport
      (((φ.hasCompactSupport_inhomogeneousLittlewoodPaley_comp_add_right j θ).comp_left
        Complex.ofReal_zero).smul_right.smul_left)
  rw [← integral_finsetSum _ fun k _ ↦ hint k]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hF (k : ℕ) := SchwartzMap.fourier_fourierMultiplierCLM_apply (F := V)
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k) u ζ
  simp only [hF, map_smul, ← Finset.smul_sum, ← Finset.sum_smul]
  by_cases hj : φ.inhomogeneousLittlewoodPaley j (ζ + θ) = 0
  · simp [hj]
  -- On the support of the translate, `‖ζ‖ ≤ 2^K φ.rIn`, where the partial sum is `1`.
  have hζ : ‖ζ‖ ≤ 2 ^ K * φ.rIn := by
    have h := lt_of_not_ge fun h ↦ hj (φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm h)
    calc ‖ζ‖ = ‖(ζ + θ) - θ‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖ζ + θ‖ + ‖θ‖ := norm_sub_le _ _
      _ ≤ 2 ^ K * φ.rIn := by linarith
  have h1 : ∑ k ∈ Finset.range (K + 1), (φ.inhomogeneousLittlewoodPaley k ζ : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range, φ.one_of_mem_closedBall,
      Complex.ofReal_one]
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ (by positivity)]
    exact hζ
  rw [h1, one_smul]

omit [CompleteSpace V] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- **The terms of the decomposition.** The term of the decomposition of the modulated piece
attached to `θ` along `ψₖ` is bounded by `‖𝓕⁻ ψⱼ‖₁ ‖𝓕⁻ (Ψₖ â(θ, 2π ·))‖₁ ‖Δₖ u‖_∞`. -/
private theorem HasCompactSpatialSupport.norm_integral_fourierChar_smul_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : CoordinateSpace n,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (u : 𝓢(CoordinateSpace n, V)) (j k : ℕ) (x θ : CoordinateSpace n) {M : ℝ}
    (hM : ∀ y, ‖SchwartzMap.fourierMultiplierCLM V
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u y‖ ≤ M) :
    ‖∫ ζ, 𝐞 ⟪ζ, x⟫ • (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 (SchwartzMap.fourierMultiplierCLM V
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ)‖ ≤
      (∫ y, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) y‖) *
        ((∫ y, ‖𝓕⁻ (fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ •
          𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ) y‖) * M) := by
  set g : CoordinateSpace n → V →L[ℂ] W := fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ
  have hρc : HasCompactSupport fun ζ ↦ (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) :=
    (φ.hasCompactSupport_inhomogeneousLittlewoodPaley_comp_add_right j θ).comp_left
      Complex.ofReal_zero
  have hρd : ContDiff ℝ ∞ fun ζ ↦ (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (φ.contDiff_inhomogeneousLittlewoodPaley_comp_add_right j θ)
  set ρS : 𝓢(CoordinateSpace n, ℂ) := hρc.toSchwartzMap hρd
  set σS : 𝓢(CoordinateSpace n, V →L[ℂ] W) :=
    ((φ.hasCompactSupport_enlargedLittlewoodPaley L k).smul_right (f' := g)).toSchwartzMap
      ((φ.contDiff_enlargedLittlewoodPaley L k).smul (ha.contDiff_fourier_slice_smul θ))
  have hρ : ⇑ρS = fun ζ ↦ (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hσ : ⇑σS = fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ • g ζ :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have heq : ∫ ζ, 𝐞 ⟪ζ, x⟫ • (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
      g ζ (𝓕 (SchwartzMap.fourierMultiplierCLM V
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • ρS ζ • σS ζ (𝓕 (SchwartzMap.fourierMultiplierCLM V
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) := by
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
    have hpt : (φ.enlargedLittlewoodPaley L k ζ • g ζ) (𝓕 (SchwartzMap.fourierMultiplierCLM V
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) =
        g ζ (𝓕 (SchwartzMap.fourierMultiplierCLM V
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) := by
      -- On the support of `ψₖ` the enlarged cutoff `Ψₖ` is `1`.
      simp [SchwartzMap.fourier_fourierMultiplierCLM_apply
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k), smul_smul,
        φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL k ζ]
    rw [hρ, hσ]
    dsimp only
    rw [hpt]
  have hρn : ∫ y, ‖𝓕⁻ ρS y‖ = ∫ y, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) y‖ := by
    simpa only [sub_neg_eq_add, SchwartzMap.fourierInv_coe, hρ] using
      TauCeti.integral_norm_fourierInv_comp_sub_const
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (-θ)
  have hσn : ∫ y, ‖𝓕⁻ σS y‖ =
      ∫ y, ‖𝓕⁻ (fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ • g ζ) y‖ := by
    rw [SchwartzMap.fourierInv_coe, hσ]
  have h := SchwartzMap.norm_integral_fourierChar_smul_bilin_fourier_le ρS
    (ContinuousLinearMap.id ℂ (V →L[ℂ] W)) σS _ hM x
  simp only [ContinuousLinearMap.id_apply] at h
  rw [heq, ← hρn, ← hσn]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun _ ↦ norm_nonneg _))
  rw [mul_assoc]
  exact mul_le_of_le_one_left (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
    ((norm_nonneg _).trans (hM 0))) ContinuousLinearMap.norm_id_le

omit [CompleteSpace V] [FiniteDimensional ℂ V] [CompleteSpace W] [FiniteDimensional ℂ W] in
/-- **Distant pieces do not contribute.** The term of the decomposition of the modulated piece
attached to `θ` along `ψₖ` vanishes unless `2^j ≤ Q 2^k` and `2^k ≤ Q 2^j`, where
`Q = 2 (φ.rOut + 1) / φ.rIn (1 + ‖θ‖)`. -/
private theorem integral_fourierChar_smul_eq_zero (φ : ContDiffBump (0 : CoordinateSpace n))
    (g : CoordinateSpace n → V →L[ℂ] W) (u : 𝓢(CoordinateSpace n, V)) {j k : ℕ}
    (x θ : CoordinateSpace n)
    (h : ¬((2 : ℝ) ^ j ≤ 2 * (φ.rOut + 1) / φ.rIn * (1 + ‖θ‖) * 2 ^ k ∧
      (2 : ℝ) ^ k ≤ 2 * (φ.rOut + 1) / φ.rIn * (1 + ‖θ‖) * 2 ^ j)) :
    ∫ ζ, 𝐞 ⟪ζ, x⟫ • (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
        g ζ (𝓕 (SchwartzMap.fourierMultiplierCLM V
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ) = 0 := by
  refine integral_eq_zero_of_ae (.of_forall fun ζ ↦ ?_)
  dsimp only [Pi.zero_apply]
  rw [SchwartzMap.fourier_fourierMultiplierCLM_apply
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k)]
  rcases mul_eq_zero.1 (φ.inhomogeneousLittlewoodPaley_add_mul_eq_zero h ζ) with hj | hk
  · simp [hj]
  · simp [hk]

omit [CompleteSpace V] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- **The weighted bound for one term.** If `2^j ≤ Q 2^k` and `2^k ≤ Q 2^j`, the term of the
decomposition along `ψₖ`, weighted by `2^{(r - m) j}`, is at most `Cψ CK ⟨θ⟩ ^ (-ρ) M Q ^ |r - m|`,
given the kernel bounds `‖𝓕⁻ ψⱼ‖₁ ≤ Cψ` and `‖𝓕⁻ (Ψₖ â(θ, 2π ·))‖₁ ≤ CK (2^k) ^ m ⟨θ⟩ ^ (-ρ)` and
the block bounds `2^{rk} ‖Δₖ u‖_∞ ≤ M`. -/
private theorem HasCompactSpatialSupport.two_rpow_mul_norm_integral_fourierChar_smul_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : CoordinateSpace n,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (u : 𝓢(CoordinateSpace n, V)) {j k : ℕ} (x θ : CoordinateSpace n) {r M Cψ CK ρ Q : ℝ}
    (hM : ∀ (k : ℕ) x, 2 ^ (r * k) * ‖SchwartzMap.fourierMultiplierCLM V
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u x‖ ≤ M)
    (hk : (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j)
    (hCψ : ∫ y, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) y‖ ≤ Cψ)
    (hCK : ∫ y, ‖𝓕⁻ (fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ •
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ) y‖ ≤
        CK * (2 ^ k) ^ m * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2)) :
    2 ^ ((r - m) * j) * ‖∫ ζ, 𝐞 ⟪ζ, x⟫ • (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 (SchwartzMap.fourierMultiplierCLM V
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ)‖ ≤
      Cψ * max CK 0 * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) * M * Q ^ |r - m| := by
  have hMk (y : CoordinateSpace n) : ‖SchwartzMap.fourierMultiplierCLM V
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u y‖ ≤ 2 ^ (-(r * k)) * M := by
    rw [Real.rpow_neg zero_le_two, ← div_eq_inv_mul, le_div_iff₀ (by positivity), mul_comm]
    exact hM k y
  have hM0 : 0 ≤ M := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hM 0 0)
  have h := ha.norm_integral_fourierChar_smul_le φ hL u j k x θ hMk
  have hpow : (2 : ℝ) ^ ((r - m) * j) * ((2 : ℝ) ^ k) ^ m * 2 ^ (-(r * k)) =
      2 ^ ((r - m) * ((j : ℝ) - k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos,
      ← Real.rpow_add two_pos]
    ring_nf
  have hCψ0 : 0 ≤ Cψ := (integral_nonneg fun _ ↦ norm_nonneg _).trans hCψ
  have hCK' : ∫ y, ‖𝓕⁻ (fun ζ ↦ φ.enlargedLittlewoodPaley L k ζ •
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ) y‖ ≤
        max CK 0 * (2 ^ k) ^ m * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) :=
    hCK.trans (by gcongr; exact le_max_left _ _)
  calc 2 ^ ((r - m) * j) * ‖_‖
      ≤ 2 ^ ((r - m) * j) * (Cψ * ((max CK 0 * (2 ^ k) ^ m * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2)) *
          (2 ^ (-(r * k)) * M))) := by
        refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
        exact mul_le_mul hCψ (mul_le_mul_of_nonneg_right hCK' (by positivity))
          (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)) hCψ0
    _ = Cψ * max CK 0 * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) * M *
          (2 ^ ((r - m) * j) * ((2 : ℝ) ^ k) ^ m * 2 ^ (-(r * k))) := by ring
    _ ≤ Cψ * max CK 0 * (1 + ‖θ‖ ^ 2) ^ (-ρ / 2) * M * Q ^ |r - m| := by
        rw [hpow]
        gcongr
        exact two_rpow_mul_sub_le_rpow_abs hk.1 hk.2 _

omit [CompleteSpace V] [FiniteDimensional ℂ V] [CompleteSpace W] [FiniteDimensional ℂ W] in
/-- The arithmetic of the final bound for one translate: with `Q = c (1 + ‖θ‖)` and `s ≥ 0`,
`(2Q + 1) A ⟨θ⟩ ^ (-(n + 2 + s)) M Q ^ s ≤ 3 A (2c) ^ (1 + s) ⟨θ⟩ ^ (-(n + 1)) M`. -/
private theorem two_mul_add_one_mul_le {c M A s : ℝ} (hc : 1 ≤ c) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hs : 0 ≤ s) (θ : CoordinateSpace n) :
    (2 * (c * (1 + ‖θ‖)) + 1) *
        (A * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 2 + s) / 2) * M * (c * (1 + ‖θ‖)) ^ s) ≤
      3 * A * (2 * c) ^ (1 + s) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * M := by
  have h2 : (c * (1 + ‖θ‖)) ^ (1 + s) ≤ (2 * c) ^ (1 + s) * (1 + ‖θ‖ ^ 2) ^ ((1 + s) / 2) := by
    have h := Real.one_add_mul_abs_rpow_le ‖θ‖ zero_le_one (by linarith : (0 : ℝ) ≤ 1 + s)
    rw [one_mul, abs_norm, one_add_one_eq_two] at h
    rw [Real.mul_rpow (by linarith) (by positivity), Real.mul_rpow zero_le_two (by linarith),
      mul_comm ((2 : ℝ) ^ (1 + s)), mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  set Q := c * (1 + ‖θ‖)
  set w : ℝ := 1 + ‖θ‖ ^ 2
  have hw : 0 < w := by positivity
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hc (le_add_of_nonneg_right (norm_nonneg _))
  have h3 : w ^ ((1 + s) / 2) * w ^ (-((n : ℝ) + 2 + s) / 2) = w ^ (-((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add hw]
    ring_nf
  calc (2 * Q + 1) * (A * w ^ (-((n : ℝ) + 2 + s) / 2) * M * Q ^ s)
      ≤ 3 * Q * (A * w ^ (-((n : ℝ) + 2 + s) / 2) * M * Q ^ s) := by gcongr; linarith
    _ = 3 * A * M * w ^ (-((n : ℝ) + 2 + s) / 2) * Q ^ (1 + s) := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]
        ring
    _ ≤ 3 * A * M * w ^ (-((n : ℝ) + 2 + s) / 2) *
          ((2 * c) ^ (1 + s) * w ^ ((1 + s) / 2)) := by gcongr
    _ = _ := by rw [← h3]; ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- **The estimate for one translate.** Let `a` be a symbol of order `m` with compact spatial
support and `r` real. There is `C` such that, for a Schwartz function `u` whose Littlewood–Paley
blocks satisfy `2^{rk} ‖Δₖ u‖_∞ ≤ M`, the modulated piece of `Δⱼ Op(a) u` attached to the
translation `θ` is bounded by `2^{-(r - m) j} C ⟨θ⟩ ^ (-(n + 1)) M`. The translate `ψⱼ (· + θ)`
meets only the pieces `ψₖ` with `2^|j - k| ≲ ⟨θ⟩`, of which there are `O(⟨θ⟩)`, and each of them
contributes `O(2^{(m - r) k} ⟨θ⟩ ^ (-ρ) M)`, for any `ρ`. -/
private theorem HasCompactSpatialSupport.exists_norm_integral_fourierChar_smul_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (r : ℝ) :
    ∃ C, ∀ (u : 𝓢(CoordinateSpace n, V)) (M : ℝ),
      (∀ (k : ℕ) x, 2 ^ (r * k) * ‖SchwartzMap.fourierMultiplierCLM V
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u x‖ ≤ M) →
      ∀ (j : ℕ) (x θ : CoordinateSpace n), 2 ^ ((r - m) * j) *
        ‖∫ ζ, 𝐞 ⟪ζ, x⟫ • (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
          𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ)‖ ≤
        C * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * M := by
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  obtain ⟨CK, hCK⟩ := ha.exists_integral_norm_fourierInv_cutoff_slice_le φ L (n + 2 + |r - m|)
  obtain ⟨Cψ, hCψ⟩ :=
    φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 0
  simp only [pow_zero, one_mul, inv_one] at hCψ
  set c : ℝ := 2 * (φ.rOut + 1) / φ.rIn
  have hc : 1 ≤ c := by
    rw [le_div_iff₀ φ.rIn_pos]
    linarith [φ.rIn_lt_rOut, φ.rIn_pos]
  refine ⟨3 * (Cψ * max CK 0) * (2 * c) ^ (1 + |r - m|), fun u M hM j x θ ↦ ?_⟩
  set Q : ℝ := c * (1 + ‖θ‖)
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hc (le_add_of_nonneg_right (norm_nonneg _))
  have hM0 : 0 ≤ M := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hM 0 0)
  set X : ℝ := Cψ * max CK 0 * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 2 + |r - m|) / 2) * M * Q ^ |r - m|
  -- Each term of the decomposition is at most `X`, and only those of comparable size survive.
  have hterm (k : ℕ) : 2 ^ ((r - m) * j) * ‖∫ ζ, 𝐞 ⟪ζ, x⟫ •
      (φ.inhomogeneousLittlewoodPaley j (ζ + θ) : ℂ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 (SchwartzMap.fourierMultiplierCLM V
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u) ζ)‖ ≤
      if (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j then X else 0 := by
    split_ifs with hk
    · exact ha.two_rpow_mul_norm_integral_fourierChar_smul_le φ hL u x θ hM hk (hCψ j)
        (hCK θ k)
    · rw [integral_fourierChar_smul_eq_zero φ _ u x θ hk, norm_zero, mul_zero]
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((2 ^ j * φ.rOut + ‖θ‖) / φ.rIn)
    (one_lt_two (α := ℝ))
  rw [div_lt_iff₀ φ.rIn_pos] at hK
  rw [ha.integral_fourierChar_smul_eq_sum φ u j x θ hK.le]
  calc 2 ^ ((r - m) * j) * ‖∑ k ∈ Finset.range (K + 1), _‖
      ≤ ∑ k ∈ Finset.range (K + 1),
          if (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j then X else 0 := by
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ ↦ hterm k
    _ = ((Finset.range (K + 1)).filter fun k ↦
          (2 : ℝ) ^ j ≤ Q * 2 ^ k ∧ (2 : ℝ) ^ k ≤ Q * 2 ^ j).card * X := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Q + 1) * X :=
        mul_le_mul_of_nonneg_right (card_filter_two_pow_le_mul_two_pow_le _ j hQ) (by positivity)
    _ ≤ 3 * (Cψ * max CK 0) * (2 * c) ^ (1 + |r - m|) *
          (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * M :=
        two_mul_add_one_mul_le hc hM0 (mul_nonneg Cψ.property (le_max_right CK 0)) (abs_nonneg _) θ

/-! ### The Zygmund estimate -/

omit [CompleteSpace V] [CompleteSpace W] in
/-- **Dyadic blocks of a quantization.** Let `a` be a symbol of order `m` with compact spatial
support between finite-dimensional spaces, `φ` the bump function of a Littlewood–Paley
partition and `r` real. There is `C ≥ 0` such that for every Schwartz function `u` and every `M`
with `2^{rk} ‖Δₖ u‖_∞ ≤ M` for all `k`, the blocks of `Op(a) u` satisfy
`2^{(r - m) j} ‖Δⱼ Op(a) u‖_∞ ≤ C M` for all `j`: `Op(a)` lowers the Zygmund smoothness, measured by
the blocks, by `m`. -/
theorem HasCompactSpatialSupport.exists_rpow_mul_norm_fourierMultiplierCLM_quantizeUniformCLM_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (u : 𝓢(CoordinateSpace n, V)) (M : ℝ),
      (∀ (k : ℕ) x, 2 ^ (r * k) * ‖SchwartzMap.fourierMultiplierCLM V
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u x‖ ≤ M) →
      ∀ (j : ℕ) x, 2 ^ ((r - m) * j) * ‖SchwartzMap.fourierMultiplierCLM W
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (quantizeUniformCLM a ha.isUniform u)
          x‖ ≤ C * M := by
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  obtain ⟨C, hC⟩ := ha.exists_norm_integral_fourierChar_smul_le φ r
  set I : ℝ := ∫ θ : CoordinateSpace n, (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : Integrable fun θ : CoordinateSpace n ↦ (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by simp)
  refine ⟨max C 0 * I, mul_nonneg (le_max_right _ _) (integral_nonneg fun _ ↦ by positivity),
    fun u M hM j x ↦ ?_⟩
  set ψ : CoordinateSpace n → ℂ := fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)
  have hrep : SchwartzMap.fourierMultiplierCLM W ψ (quantizeUniformCLM a ha.isUniform u) x =
      𝓕⁻ (fun η ↦ ψ η • 𝓕 (quantizeSchwartzValue a.coefficient u) η) x := by
    have hfun : ⇑(SchwartzMap.smulLeftCLM W ψ (𝓕 (quantizeUniformCLM a ha.isUniform u))) =
        fun η ↦ ψ η • 𝓕 (quantizeSchwartzValue a.coefficient u) η := by
      funext η
      rw [SchwartzMap.smulLeftCLM_apply_apply
        (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j), SchwartzMap.fourier_coe,
        coe_quantizeUniformCLM]
    rw [SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe, hfun]
  have hψi : Integrable ψ := by
    have h := (φ.inhomogeneousLittlewoodPaleySchwartz j).integrable (μ := volume)
    rwa [φ.coe_inhomogeneousLittlewoodPaleySchwartz] at h
  have hψc : Continuous ψ :=
    Complex.continuous_ofReal.comp (φ.contDiff_inhomogeneousLittlewoodPaley j (n := 0)).continuous
  have hψ1 (ξ : CoordinateSpace n) : ‖ψ ξ‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact φ.abs_inhomogeneousLittlewoodPaley_le_one j ξ
  rw [hrep, ha.fourierInv_smul_fourier_quantizeSchwartzValue hψc hψi hψ1 u x]
  -- Each modulated piece is `O(2^{-(r - m) j} ⟨θ⟩ ^ (-(n + 1)) M)`, which is integrable in `θ`.
  have hb (θ : CoordinateSpace n) : ‖𝐞 ⟪θ, x⟫ • ∫ ζ, 𝐞 ⟪ζ, x⟫ • ψ (ζ + θ) •
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ)‖ ≤
      (2 ^ ((r - m) * j))⁻¹ * (max C 0 * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * M) := by
    have hM0 : 0 ≤ M := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hM 0 0)
    rw [Circle.norm_smul, le_inv_mul_iff₀ (by positivity)]
    exact (hC u M hM j x θ).trans (by gcongr; exact le_max_left _ _)
  calc 2 ^ ((r - m) * j) * ‖∫ θ, 𝐞 ⟪θ, x⟫ • ∫ ζ, 𝐞 ⟪ζ, x⟫ • ψ (ζ + θ) •
        𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) θ (𝓕 u ζ)‖
      ≤ 2 ^ ((r - m) * j) * ∫ θ : CoordinateSpace n,
          (2 ^ ((r - m) * j))⁻¹ * (max C 0 * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * M) := by
        gcongr
        exact norm_integral_le_of_norm_le (((hI.const_mul _).mul_const _).const_mul _)
          (.of_forall hb)
    _ = max C 0 * I * M := by
        rw [integral_const_mul, integral_mul_const, integral_const_mul,
          mul_inv_cancel_left₀ (by positivity)]

/-- **Zygmund estimate for pseudodifferential operators with compact spatial support.** Let `a`
be a symbol of order `m` with compact spatial support between finite-dimensional complex normed
spaces, and `r` real. There is `C ≥ 0` such that for every Schwartz function `u`, the norm of
`Op(a) u` in the Hölder–Zygmund space `𝒞^{r - m} = B^{r - m}_{∞,∞}` is at most `C` times the norm
of `u` in `𝒞^r = B^r_{∞,∞}`: `‖Op(a) u‖_{𝒞^{r - m}} ≤ C ‖u‖_{𝒞^r}`. -/
theorem
    HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesovSpaceCLM W φ (r - m) ∞ ∞ (quantizeUniformCLM a ha.isUniform u)‖ ≤
        C * ‖SchwartzMap.toBesovSpaceCLM V φ r ∞ ∞ u‖ := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_rpow_mul_norm_fourierMultiplierCLM_quantizeUniformCLM_le φ r
  refine ⟨C, hC0, fun u ↦ ?_⟩
  set v := SchwartzMap.toBesovSpaceCLM V φ r ∞ ∞ u
  have hM (k : ℕ) (x : CoordinateSpace n) : 2 ^ (r * k) * ‖SchwartzMap.fourierMultiplierCLM V
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) u x‖ ≤ ‖v‖ := by
    refine le_trans ?_ (v.rpow_mul_norm_block_le k)
    rw [BesovSpace.block_toBesovSpaceCLM]
    gcongr
    exact Lp.norm_le_norm_top_of_ae_eq_of_continuousAt (SchwartzMap.coeFn_toLp _ ⊤ volume)
      (SchwartzMap.continuous _).continuousAt
  rw [BesovSpace.norm_eq_ciSup]
  refine ciSup_le fun j ↦ ?_
  rw [BesovSpace.block_toBesovSpaceCLM, ← le_div_iff₀' (by positivity)]
  refine (SchwartzMap.norm_toLp_top_le).trans (SchwartzMap.seminorm_le_bound ℝ 0 0 _
    (by positivity) fun x ↦ ?_)
  rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, le_div_iff₀' (by positivity)]
  exact hC u ‖v‖ hM j x

end Estimates

end Symbol

end TauCeti
