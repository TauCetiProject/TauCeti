/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
public import TauCeti.Analysis.Fourier.L2Multiplier
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Calculus.BumpFunction.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.SpecificLimits.ZPow
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

/-!
# The homogeneous Littlewood–Paley decomposition of a tempered distribution

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`, `j ∈ ℤ`, be the dyadic cutoffs built from it
(`ContDiffBump.littlewoodPaley`), supported in the annuli `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut` and
summing to `1` on `E \ {0}`. The **homogeneous Littlewood–Paley blocks** of a tempered
distribution `u` are the Fourier multipliers

`Pⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)`, `j ∈ ℤ`.

For `j ≥ 1` they are the inhomogeneous blocks `Δⱼ` (`TemperedDistribution.littlewoodPaleyBlock`);
the blocks with `j ≤ 0` split the low-frequency block `Δ₀` into dyadic pieces down to frequency
zero. Homogeneous Besov and Sobolev norms, and the frequency-localized estimates of dispersive
equations, are built on these blocks. Their partial sums telescope: for `a ≤ b`,

`∑_{a < j ≤ b} Pⱼ u = Sᵦ u - Sₐ u`, where `Sₐ u = 𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)`.

As `b → ∞` the truncations `Sᵦ u` converge to `u` for every tempered distribution. As `a → -∞`
they need not converge to `0`: the Fourier transform of `Sₐ u` concentrates at the origin. Hence
the reconstruction `u = ∑_{j ∈ ℤ} Pⱼ u` is not automatic. The partial sums over `a < j ≤ b`
converge to `u` as `a → -∞` and `b → ∞` exactly when `Sₐ u → 0`
(`TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_iff`). Whenever they converge,
to some `v`, the difference `u - v` has Fourier transform supported at the origin
(`TemperedDistribution.isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock`):
the homogeneous decomposition reconstructs a distribution modulo distributions with spectrum
`{0}`, the polynomials. Those are invisible to every block: if `𝓕 u` vanishes on `E \ {0}`, then
`Pⱼ u = 0` for every `j`
(`TemperedDistribution.homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero`), so
the reconstruction fails for every nonzero such `u`, for instance a nonzero constant.

The main class of distributions that the decomposition does reconstruct is `Lᵖ`, `p < ∞`, on a
nontrivial space. The truncation `Sₐ f` of `f ∈ Lᵖ` has spectrum in the ball of radius
`2^a φ.rOut` and `Lᵖ` norm at most `‖𝓕⁻ φ‖₁ ‖f‖_p`, so Bernstein's inequality bounds it in `L^∞`
by a constant times `2^{a n / p} ‖f‖_p`, where `n ≥ 1` is the dimension
(`TemperedDistribution.exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le_mul_rpow`). This tends
to `0` as `a → -∞`, so `Sₐ f → 0` and `f = ∑_{j ∈ ℤ} Pⱼ f`
(`TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_of_ne_top`). At `p = ∞` this
fails: a nonzero constant function lies in `L^∞` but has no homogeneous blocks
(`TemperedDistribution.homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero`).

Like the inhomogeneous blocks, the homogeneous blocks are bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`,
uniformly in `j ∈ ℤ`: the kernel `𝓕⁻ ψⱼ` is the `L¹`-normalised dilate of `𝓕⁻ ψ₀`. They are
almost orthogonal, `Pⱼ Pₖ = 0` once `|j - k|` exceeds a constant depending only on `φ`, and the
Fourier transform of `Pⱼ u` vanishes off the annulus carrying `ψⱼ`, the form in which Bernstein's
inequalities on annuli apply.

## Main declarations

* `TemperedDistribution.homogeneousLittlewoodPaleyBlock`: the homogeneous block `Pⱼ`, `j ∈ ℤ`,
  with `TemperedDistribution.homogeneousLittlewoodPaleyBlock_natCast` identifying it with the
  inhomogeneous block `Δⱼ` for `j ≥ 1`.
* `TemperedDistribution.sum_homogeneousLittlewoodPaleyBlock_Ioc`: the partial sums telescope to
  differences of low-pass truncations.
* `TemperedDistribution.isVanishingOn_fourier_homogeneousLittlewoodPaleyBlock`: the spectrum of a
  block lies in its dyadic annulus.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_eq_of_isVanishingOn_fourier_sub`: the
  blocks see a distribution only modulo distributions with spectrum at the origin.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_comm`: the blocks of two bump functions
  commute.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_compL_eq_zero`: almost
  orthogonality, also between the blocks of two bump functions, and
  `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico`: the blocks of a second
  bump function are window sums `P'ⱼ u = ∑_{j - L ≤ k < j + L} P'ⱼ Pₖ u`.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le`: the blocks are
  bounded on `Lᵖ`, uniformly in `j ∈ ℤ`,
  `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le`: Bernstein's
  inequality `‖Pⱼ u‖_r ≤ C 2^{jn(1/p - 1/r)} ‖Pⱼ u‖_p` for `p ≤ r`, and
  `TemperedDistribution.exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le_mul_rpow`: the
  truncation at scale `R` of an `Lᵖ` function is `O(R ^ (n / p))` in `L^∞`.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range`: a block
  `Pⱼ` with `2^j φ.rOut ≤ 2^N φ.rIn` only sees the inhomogeneous blocks `Δₖ`, `k ≤ N`, and
  `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_nonpos`: if the
  inhomogeneous blocks of `u` are `Lᵖ` functions, its blocks `Pⱼ u`, `j ≤ 0`, are bounded in `Lᵖ`.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_toTemperedDistribution`: on `L²` the block
  `Pⱼ` is the `L²` Fourier multiplier with symbol `ψⱼ`.
* `TemperedDistribution.exists_fourierMultiplierCLM_eq_zero_of_eq_homogeneousLittlewoodPaleyBlock`:
  almost orthogonality on `L²`, an `L²` function `Pⱼ v` has no block `Pₖ` with `|k - j| ≥ L`.
* `exists_eLpNorm_eLpNorm_fourierMultiplierCLM_of_eq_homogeneousLittlewoodPaleyBlock`: the same in
  mixed norms, with the bound `‖Pₖ x‖_{L^p_α L^r} ≤ K ‖x‖_{L^p_α L^r}` on every block.
* `TemperedDistribution.tendsto_fourierMultiplierCLM_two_zpow_atTop`: `Sᵦ u → u` as `b → ∞`.
* `TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_iff`: the homogeneous
  reconstruction holds exactly when `Sₐ u → 0` as `a → -∞`, and
  `TemperedDistribution.isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock`:
  in general it holds modulo distributions with spectrum at the origin.
* `TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_of_ne_top`: every `Lᵖ`
  function, `p < ∞`, is the sum of its homogeneous blocks.
* `TemperedDistribution.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock_of_summable`: if the
  blocks of nonpositive index are bounded functions with summable `L^∞` norms, the decomposition
  converges, to `u` modulo a distribution with spectrum at the origin.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.4
  (homogeneous Littlewood–Paley decomposition) and Section 1.5 (the space `𝓢'_h`).
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 2.4.
-/

public section

open Filter Topology MeasureTheory
open FourierTransform Distribution
open scoped SchwartzMap LineDeriv ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

variable (F) in
/-- The **homogeneous Littlewood–Paley block** `Pⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)`, `j ∈ ℤ`, of a tempered
distribution: the Fourier multiplier by the dyadic cutoff `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`,
which carries the frequencies `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`. -/
noncomputable def homogeneousLittlewoodPaleyBlock (φ : ContDiffBump (0 : E)) (j : ℤ) :
    𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)

variable (φ : ContDiffBump (0 : E))

/-- Unfolding `TemperedDistribution.homogeneousLittlewoodPaleyBlock`. -/
theorem homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM (j : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j =
      fourierMultiplierCLM F (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :=
  (rfl)

/-- Unfolding `TemperedDistribution.homogeneousLittlewoodPaleyBlock` on a tempered distribution. -/
theorem homogeneousLittlewoodPaleyBlock_apply (j : ℤ) (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j u =
      fourierMultiplierCLM F (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) u :=
  (rfl)

/-- For `j ≥ 1` the homogeneous block `Pⱼ` is the inhomogeneous block `Δⱼ`. -/
theorem homogeneousLittlewoodPaleyBlock_natCast {j : ℕ} (hj : j ≠ 0) :
    homogeneousLittlewoodPaleyBlock F φ j = littlewoodPaleyBlock F φ j := by
  rw [homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    littlewoodPaleyBlock_eq_fourierMultiplierCLM, φ.inhomogeneousLittlewoodPaley_of_ne_zero hj]

/-- **The partial sums telescope.** For `a ≤ b`,
`∑_{a < j ≤ b} Pⱼ = 𝓕⁻ (φ (2^{-b} ·) • 𝓕 ·) - 𝓕⁻ (φ (2^{-a} ·) • 𝓕 ·)`. -/
theorem sum_homogeneousLittlewoodPaleyBlock_Ioc {a b : ℤ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ioc a b, homogeneousLittlewoodPaleyBlock F φ j =
      fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ b)⁻¹ • ξ) : ℂ)) -
        fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ)) := by
  have hsum : (fun ξ ↦ ∑ j ∈ Finset.Ioc a b, (φ.littlewoodPaley j ξ : ℂ)) +
      (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ)) = fun ξ ↦ (φ (((2 : ℝ) ^ b)⁻¹ • ξ) : ℂ) := by
    funext ξ
    simp only [Pi.add_apply, ← Complex.ofReal_sum, φ.sum_littlewoodPaley_Ioc hab]
    push_cast
    ring
  have hadd := fourierMultiplierCLM_add (F := F)
    (Function.HasTemperateGrowth.sum (s := Finset.Ioc a b) fun j _ ↦
      φ.hasTemperateGrowth_ofReal_littlewoodPaley j)
    (φ.lowPassSchwartz (zpow_ne_zero a two_ne_zero)).hasTemperateGrowth
  rw [φ.coe_lowPassSchwartz, hsum,
    fourierMultiplierCLM_sum F fun j _ ↦ φ.hasTemperateGrowth_ofReal_littlewoodPaley j]
    at hadd
  simp_rw [homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM]
  exact eq_sub_of_add_eq hadd.symm

/-- **The spectrum of a homogeneous block.** The Fourier transform of `Pⱼ u` vanishes on the open
ball of radius `2^{j-1} φ.rIn` and outside the closed ball of radius `2^j φ.rOut`. -/
theorem isVanishingOn_fourier_homogeneousLittlewoodPaleyBlock (j : ℤ) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (homogeneousLittlewoodPaleyBlock F φ j u) : 𝓢'(E, F))
      (Metric.ball 0 (2 ^ (j - 1) * φ.rIn) ∪ (Metric.closedBall 0 (2 ^ j * φ.rOut))ᶜ) := by
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ ?_) u
  simp only [Set.mem_union, Metric.mem_ball, dist_zero_right, Set.mem_compl_iff,
    Metric.mem_closedBall, not_le] at hξ
  rcases hξ with hξ | hξ
  · rw [φ.littlewoodPaley_eq_zero_of_norm_le hξ.le, Complex.ofReal_zero]
  · rw [φ.littlewoodPaley_eq_zero_of_le_norm hξ.le, Complex.ofReal_zero]

/-- The homogeneous blocks commute with directional derivatives. -/
theorem homogeneousLittlewoodPaleyBlock_lineDerivOp (j : ℤ) (m : E) (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j (∂_{m} u) =
      ∂_{m} (homogeneousLittlewoodPaleyBlock F φ j u) := by
  rw [homogeneousLittlewoodPaleyBlock_apply, homogeneousLittlewoodPaleyBlock_apply,
    lineDerivOp_fourierMultiplierCLM (φ.hasTemperateGrowth_ofReal_littlewoodPaley j)]

open Distribution in
/-- **Blocks off the spectrum vanish.** If the Fourier transform of `u` vanishes on a set
containing the support of the cutoff `ψⱼ`, then `Pⱼ u = 0`. -/
theorem homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {j : ℤ} (hj : tsupport (φ.littlewoodPaley j) ⊆ s) :
    homogeneousLittlewoodPaleyBlock F φ j u = 0 :=
  fourierMultiplierCLM_eq_zero_of_isVanishingOn hu <|
    (tsupport_comp_subset Complex.ofReal_zero _).trans hj

open Distribution in
/-- **Distributions with spectrum at the origin have no homogeneous blocks.** If the Fourier
transform of `u` vanishes on `E \ {0}`, as for a polynomial, then `Pⱼ u = 0` for every `j`. -/
theorem homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero {u : 𝓢'(E, F)}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) {0}ᶜ) (j : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j u = 0 :=
  homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn φ hu fun _ hξ h0 ↦
    φ.zero_notMem_tsupport_littlewoodPaley j (h0 ▸ hξ)

open Distribution in
/-- **The blocks see a distribution only modulo spectrum at the origin.** If the Fourier transform
of `u - v` vanishes on `E \ {0}`, as when `u - v` is a polynomial, then `Pⱼ u = Pⱼ v` for every
`j`. -/
theorem homogeneousLittlewoodPaleyBlock_eq_of_isVanishingOn_fourier_sub {u v : 𝓢'(E, F)}
    (h : IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ) (j : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j u = homogeneousLittlewoodPaleyBlock F φ j v := by
  rw [← sub_eq_zero, ← map_sub]
  exact homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero φ h j

/-- The composition of the homogeneous blocks of two bump functions is the Fourier multiplier by
the product of the two cutoffs. -/
theorem homogeneousLittlewoodPaleyBlock_compL_homogeneousLittlewoodPaleyBlock
    (φ' : ContDiffBump (0 : E)) (j k : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j ∘L homogeneousLittlewoodPaleyBlock F φ' k =
      fourierMultiplierCLM F
        fun ξ ↦ ((φ.littlewoodPaley j ξ * φ'.littlewoodPaley k ξ : ℝ) : ℂ) := by
  rw [homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_compL_fourierMultiplierCLM
      (φ'.hasTemperateGrowth_ofReal_littlewoodPaley k)
      (φ.hasTemperateGrowth_ofReal_littlewoodPaley j)]
  congr 1
  funext ξ
  simp [mul_comm]

/-- **The homogeneous blocks commute.** For two bump functions `φ` and `φ'`, `Pⱼ P'ₖ u = P'ₖ Pⱼ u`,
where `P` and `P'` are the homogeneous blocks built from `φ` and `φ'`. -/
theorem homogeneousLittlewoodPaleyBlock_comm (φ' : ContDiffBump (0 : E)) (j k : ℤ)
    (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j (homogeneousLittlewoodPaleyBlock F φ' k u) =
      homogeneousLittlewoodPaleyBlock F φ' k (homogeneousLittlewoodPaleyBlock F φ j u) := by
  have h : homogeneousLittlewoodPaleyBlock F φ j ∘L homogeneousLittlewoodPaleyBlock F φ' k =
      homogeneousLittlewoodPaleyBlock F φ' k ∘L homogeneousLittlewoodPaleyBlock F φ j := by
    simp_rw [homogeneousLittlewoodPaleyBlock_compL_homogeneousLittlewoodPaleyBlock, mul_comm]
  exact congr($h u)

/-- **Almost orthogonality of the homogeneous blocks.** For two bump functions `φ` and `φ'`,
there is `L` such that `Pⱼ P'ₖ = P'ₖ Pⱼ = 0` whenever `j + L ≤ k`, where `P` and `P'` are the
homogeneous blocks built from `φ` and `φ'`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_compL_eq_zero (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ j k : ℤ, j + L ≤ k →
      homogeneousLittlewoodPaleyBlock F φ j ∘L homogeneousLittlewoodPaleyBlock F φ' k = 0 ∧
        homogeneousLittlewoodPaleyBlock F φ' k ∘L homogeneousLittlewoodPaleyBlock F φ j = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ'
  refine ⟨L, fun j k hjk ↦ ⟨?_, ?_⟩⟩
  · simp_rw [homogeneousLittlewoodPaleyBlock_compL_homogeneousLittlewoodPaleyBlock, hL j k hjk,
      Complex.ofReal_zero, fourierMultiplierCLM_const, zero_smul]
  · simp_rw [homogeneousLittlewoodPaleyBlock_compL_homogeneousLittlewoodPaleyBlock,
      mul_comm _ (φ.littlewoodPaley j _), hL j k hjk, Complex.ofReal_zero,
      fourierMultiplierCLM_const, zero_smul]

/-- **The low-frequency blocks see only the low frequencies.** If the cutoff `ψⱼ` is carried by
the ball where `φ (2^{-N} ·) = 1`, which is guaranteed by `2^j φ.rOut ≤ 2^N φ.rIn`, then `Pⱼ` does
not see the inhomogeneous blocks `Δₖ`, `k > N`: `Pⱼ (∑_{k ≤ N} Δₖ u) = Pⱼ u`. -/
theorem homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range {j : ℤ} {N : ℕ}
    (hjN : 2 ^ j * φ.rOut ≤ 2 ^ N * φ.rIn) (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j
        (∑ k ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ k u) =
      homogeneousLittlewoodPaleyBlock F φ j u := by
  have hN : (0 : ℝ) < 2 ^ N := by positivity
  rw [← _root_.sum_apply, ← littlewoodPaleyLowPass_def,
    littlewoodPaleyLowPass_succ_eq_fourierMultiplierCLM, homogeneousLittlewoodPaleyBlock_apply,
    homogeneousLittlewoodPaleyBlock_apply,
    ← φ.coe_lowPassSchwartz hN.ne', fourierMultiplierCLM_fourierMultiplierCLM_apply
      (φ.lowPassSchwartz hN.ne').hasTemperateGrowth (φ.hasTemperateGrowth_ofReal_littlewoodPaley j),
    mul_comm, φ.mul_lowPassSchwartz_of_support_subset hN]
  -- On the support of `ψⱼ`, `‖ξ‖ ≤ 2^j φ.rOut ≤ 2^N φ.rIn`.
  refine (subset_tsupport _).trans <| (tsupport_comp_subset Complex.ofReal_zero _).trans
    fun ξ hξ ↦ mem_closedBall_zero_iff.2 ?_
  exact (φ.tsupport_littlewoodPaley_subset j hξ).2.trans hjN

/-! ### Reconstruction -/

/-- **High-frequency reconstruction.** For every tempered distribution `u`, the low-pass
truncations `𝓕⁻ (φ (2^{-b} ·) • 𝓕 u)` converge to `u` as `b → ∞`. -/
theorem tendsto_fourierMultiplierCLM_two_zpow_atTop (u : 𝓢'(E, F)) :
    Tendsto (fun b : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ b)⁻¹ • ξ) : ℂ)) u)
      atTop (𝓝 u) :=
  tendsto_fourierMultiplierCLM_contDiffBump φ
    (TauCeti.tendsto_zpow_atTop_atTop_of_one_lt one_lt_two) u

/-- Eventually along `a → -∞`, `b → ∞`, the two-sided partial sum `∑_{a < j ≤ b} Pⱼ u` is the
difference `Sᵦ u - Sₐ u` of the low-pass truncations. -/
private theorem sum_homogeneousLittlewoodPaleyBlock_Ioc_eventuallyEq (u : 𝓢'(E, F)) :
    (fun ab : ℤ × ℤ ↦ ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
      =ᶠ[atBot ×ˢ atTop] fun ab ↦
        fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ ab.2)⁻¹ • ξ) : ℂ)) u -
          fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ ab.1)⁻¹ • ξ) : ℂ)) u := by
  filter_upwards [tendsto_fst.eventually (eventually_le_atBot (0 : ℤ)),
    tendsto_snd.eventually (eventually_ge_atTop (0 : ℤ))] with ab ha hb
  rw [← _root_.sum_apply, sum_homogeneousLittlewoodPaleyBlock_Ioc φ (ha.trans hb),
    _root_.sub_apply]

/-- If the two-sided partial sums of the homogeneous blocks of `u` converge to `v`, then the
low-pass truncations `𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)` converge to `u - v` as `a → -∞`. -/
private theorem tendsto_fourierMultiplierCLM_two_zpow_atBot_of_tendsto_sum {u v : 𝓢'(E, F)}
    (h : Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
        (atBot ×ˢ atTop) (𝓝 v)) :
    Tendsto (fun a : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ)) u)
      atBot (𝓝 (u - v)) := by
  rw [← map_fst_prod atBot (atTop : Filter ℤ), tendsto_map'_iff]
  have hb := (tendsto_fourierMultiplierCLM_two_zpow_atTop φ u).comp
    (tendsto_snd (f := (atBot : Filter ℤ)))
  refine (hb.sub h).congr' ?_
  filter_upwards [sum_homogeneousLittlewoodPaleyBlock_Ioc_eventuallyEq φ u] with ab hab
  rw [Function.comp_apply, Function.comp_apply, hab, sub_sub_cancel]

/-- **Homogeneous Littlewood–Paley reconstruction.** The two-sided partial sums
`∑_{a < j ≤ b} Pⱼ u` converge to `u` as `a → -∞` and `b → ∞` exactly when the low-pass
truncations `𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)` converge to `0` as `a → -∞`. -/
theorem tendsto_sum_homogeneousLittlewoodPaleyBlock_iff (u : 𝓢'(E, F)) :
    Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
        (atBot ×ˢ atTop) (𝓝 u) ↔
      Tendsto (fun a : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ)) u)
        atBot (𝓝 0) := by
  refine ⟨fun h ↦ by simpa using tendsto_fourierMultiplierCLM_two_zpow_atBot_of_tendsto_sum φ h,
    fun h ↦ ?_⟩
  refine (sub_zero u ▸ ((tendsto_fourierMultiplierCLM_two_zpow_atTop φ u).comp
    tendsto_snd).sub (h.comp tendsto_fst)).congr' ?_
  exact (sum_homogeneousLittlewoodPaleyBlock_Ioc_eventuallyEq φ u).symm

open Distribution in
/-- **Reconstruction modulo polynomials.** If the two-sided partial sums `∑_{a < j ≤ b} Pⱼ u`
converge to `v` as `a → -∞` and `b → ∞`, then the Fourier transform of `u - v` vanishes on
`E \ {0}`. -/
theorem isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock
    {u v : 𝓢'(E, F)}
    (h : Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
        (atBot ×ˢ atTop) (𝓝 v)) :
    IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ := by
  intro ψ hψ
  -- The support of `ψ` stays away from the origin, at distance at least `r`.
  obtain ⟨r, hr, hrψ⟩ := Metric.isOpen_iff.1 (isClosed_tsupport ψ).isOpen_compl 0
    fun h0 ↦ hψ h0 rfl
  have hlim := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.1
    (((fourierCLM ℂ 𝓢'(E, F)).continuous.tendsto _).comp
      (tendsto_fourierMultiplierCLM_two_zpow_atBot_of_tendsto_sum φ h)) ψ
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  -- Once `2^a φ.rOut < r`, the spectrum of the truncation misses the support of `ψ`.
  have hsmall : ∀ᶠ a : ℤ in atBot, (2 : ℝ) ^ a * φ.rOut < r :=
    ((TauCeti.tendsto_zpow_atBot_nhds_zero_of_one_lt one_lt_two).mul_const φ.rOut).eventually
      (gt_mem_nhds (by rwa [zero_mul] : 0 * φ.rOut < r))
  filter_upwards [hsmall] with a ha
  simp only [Function.comp_apply, fourierCLM_apply]
  refine (isVanishingOn_fourier_fourierMultiplierCLM
    (φ.ofReal_apply_inv_smul_eq_zero (zpow_pos two_pos a)) u ψ
    fun ξ hξ hball ↦ hrψ ?_ hξ).symm
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  rw [Metric.mem_ball, dist_zero_right]
  exact hball.trans_lt ha

/-- **Change of bump function.** The homogeneous blocks `Pₖ` and `P'ⱼ` built from two bump functions
`φ` and `φ'` interact only at nearby indices: there is `L`, depending only on `φ` and `φ'`, such
that `P'ⱼ u = ∑_{j - L ≤ k < j + L} P'ⱼ Pₖ u` for every `j ∈ ℤ` and every tempered distribution
`u`. The block `P'ⱼ u` has spectrum in an annulus away from the origin, so it is the sum of its
own blocks `Pₖ P'ⱼ u`, and only those with `k` near `j` are nonzero. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ (j : ℤ) (u : 𝓢'(E, F)), homogeneousLittlewoodPaleyBlock F φ' j u =
      ∑ k ∈ Finset.Ico (j - L) (j + L),
        homogeneousLittlewoodPaleyBlock F φ' j (homogeneousLittlewoodPaleyBlock F φ k u) := by
  obtain ⟨L₁, hL₁⟩ := exists_homogeneousLittlewoodPaleyBlock_compL_eq_zero (F := F) φ φ'
  obtain ⟨L₂, hL₂⟩ := exists_homogeneousLittlewoodPaleyBlock_compL_eq_zero (F := F) φ' φ
  refine ⟨max L₁ L₂, fun j u ↦ ?_⟩
  have hL₁L : L₁ ≤ max L₁ L₂ := le_max_left _ _
  have hL₂L : L₂ ≤ max L₁ L₂ := le_max_right _ _
  set w := homogeneousLittlewoodPaleyBlock F φ' j u
  -- The blocks commute: `P'ⱼ Pₖ u = Pₖ P'ⱼ u`.
  have hcomm (k : ℤ) : homogeneousLittlewoodPaleyBlock F φ' j
      (homogeneousLittlewoodPaleyBlock F φ k u) = homogeneousLittlewoodPaleyBlock F φ k w :=
    homogeneousLittlewoodPaleyBlock_comm φ' φ j k u
  -- The low-pass truncations of `w` vanish once their spectrum misses the annulus carrying `w`.
  have hlow : Tendsto (fun a : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ))
      w) atBot (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    have hsmall : ∀ᶠ a : ℤ in atBot, (2 : ℝ) ^ a * φ.rOut < 2 ^ (j - 1) * φ'.rIn :=
      ((TauCeti.tendsto_zpow_atBot_nhds_zero_of_one_lt one_lt_two).mul_const φ.rOut).eventually
        (gt_mem_nhds (by rw [zero_mul]; exact mul_pos (zpow_pos two_pos _) φ'.rIn_pos))
    filter_upwards [hsmall] with a ha
    refine (fourierMultiplierCLM_eq_zero_of_isVanishingOn
      ((isVanishingOn_fourier_homogeneousLittlewoodPaleyBlock φ' j u).mono
        Set.subset_union_left) ?_).symm
    refine (closure_minimal (fun ξ hξ ↦ ?_) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball ha)
    by_contra h
    exact hξ (φ.ofReal_apply_inv_smul_eq_zero (zpow_pos two_pos a) ξ h)
  -- So `w` is the sum of its blocks `Pₖ w`, and those far from `j` vanish.
  refine tendsto_nhds_unique ((tendsto_sum_homogeneousLittlewoodPaleyBlock_iff φ w).2 hlow)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [tendsto_fst.eventually (eventually_lt_atBot (j - max L₁ L₂)),
    tendsto_snd.eventually (eventually_ge_atTop (j + max L₁ L₂))] with ab ha hb
  simp_rw [hcomm]
  refine Finset.sum_subset (fun k hk ↦ ?_) fun k _ hk ↦ ?_
  · rw [Finset.mem_Ico] at hk
    rw [Finset.mem_Ioc]
    omega
  · rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
    rcases hk with hk | hk
    · simpa using DFunLike.congr_fun (hL₁ k j (by omega)).1 u
    · simpa using DFunLike.congr_fun (hL₂ j k (by omega)).2 u

/-! ### Bounds on `Lᵖ` and the reconstruction of `Lᵖ` functions -/

section Lp

variable [CompleteSpace F]

/-- **The homogeneous blocks are bounded on `Lᵖ` uniformly in `j ∈ ℤ`.** There is `C`, depending
only on `φ`, such that for every `1 ≤ p ≤ ∞`, every `j ∈ ℤ` and every `f ∈ Lᵖ`, the block `Pⱼ f`
is a function in `Lᵖ` with `‖Pⱼ f‖_p ≤ C ‖f‖_p`. The kernel of `Pⱼ` is the `L¹`-normalised dilate
of the kernel of `P₀`, so one can take `C = ‖𝓕⁻ ψ₀‖₁`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℤ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        homogeneousLittlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  refine ⟨∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ)) x‖, fun {p} _ j f ↦ ?_⟩
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le (φ.littlewoodPaleySchwartz j) f
  rw [φ.coe_littlewoodPaleySchwartz] at hg hgf
  refine ⟨g, hg, ?_⟩
  -- The kernel of `Pⱼ` is the `L¹`-normalised dilate of the kernel of `P₀`.
  simp_rw [φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply j] at hgf
  rwa [TauCeti.integral_norm_fourierInv_comp_smul (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))
    (inv_ne_zero (zpow_ne_zero j two_ne_zero))] at hgf

/-- **Bernstein's inequality for the homogeneous blocks.** For `1 ≤ p ≤ r ≤ ∞` there is `C`,
depending only on `E`, `F`, `p`, `r` and `φ`, with the following property. If the block `Pⱼ u`,
`j ∈ ℤ`, of a tempered distribution is an `Lᵖ` function `f`, then it is also an `Lʳ` function `g`,
with

`‖g‖_r ≤ C 2^{j n (1/p - 1/r)} ‖f‖_p`,

where `n` is the dimension of `E` and `1/∞ = 0`. The Fourier transform of the block is carried by
the ball of radius `2^j φ.rOut`, so this is Bernstein's inequality at that radius. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ r)] (hpr : p ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E)),
      homogeneousLittlewoodPaleyBlock F φ j u = f → ∃ g : Lp F r (volume : Measure E),
        homogeneousLittlewoodPaleyBlock F φ j u = g ∧
          ‖g‖ ≤ C * 2 ^ (Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹) * j) * ‖f‖ := by
  obtain ⟨C, hC, hB⟩ :=
    TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F) hpr
  set a : ℝ := Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)
  refine ⟨C * φ.rOut ^ a, mul_nonneg hC (Real.rpow_nonneg φ.rOut_pos.le a), fun j u f hf ↦ ?_⟩
  -- Bernstein's inequality without derivatives, at the radius `2^j φ.rOut` carrying `Pⱼ u`.
  obtain ⟨g, hg, hgf⟩ := hB (mul_pos (zpow_pos two_pos j) φ.rOut_pos) f
    (hf ▸ (isVanishingOn_fourier_homogeneousLittlewoodPaleyBlock φ j u).mono
      Set.subset_union_right)
  refine ⟨g, hf.trans hg, hgf.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) φ.rOut_pos.le, ← Real.rpow_intCast,
    ← Real.rpow_mul zero_le_two, mul_comm (j : ℝ) a]
  ring

variable {φ} in
/-- **The low-frequency homogeneous blocks are bounded in `Lᵖ`.** If the inhomogeneous blocks
`Δₖ u` are `Lᵖ` functions `fₖ`, then there are `B` and `Lᵖ` functions `G j` with `Pⱼ u = G j`
and `‖G j‖_p ≤ B` for every `j ≤ 0`. They are blocks of the `Lᵖ` function `∑_{k ≤ N} Δₖ u`, for `N`
with `φ.rOut ≤ 2^N φ.rIn`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_nonpos
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)} {f : ℕ → Lp F p (volume : Measure E)}
    (hf : ∀ k, littlewoodPaleyBlock F φ k u = f k) :
    ∃ B : ℝ, ∃ G : ℤ → Lp F p (volume : Measure E), ∀ j ≤ 0,
      homogeneousLittlewoodPaleyBlock F φ j u = G j ∧ ‖G j‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  set S : Lp F p (volume : Measure E) := ∑ k ∈ Finset.range (N + 1), f k
  choose G hG hGC using fun j : ℤ ↦ hC (p := p) j S
  refine ⟨C * ‖S‖, G, fun j hj ↦ ⟨?_, hGC j⟩⟩
  have hjN : (2 : ℝ) ^ j * φ.rOut ≤ 2 ^ N * φ.rIn :=
    calc (2 : ℝ) ^ j * φ.rOut ≤ 1 * φ.rOut :=
          mul_le_mul_of_nonneg_right (zpow_le_one_of_nonpos₀ (one_le_two (α := ℝ)) hj)
            φ.rOut_pos.le
      _ ≤ 2 ^ N * φ.rIn := by rw [one_mul]; exact hN.le
  rw [← homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range φ hjN, ← hG j,
    Lp.toTemperedDistribution_sum, Finset.sum_congr rfl fun k _ ↦ hf k]

/-- **Low-pass truncations of `Lᵖ` functions are small in `L^∞`.** There is `C`, depending only on
`φ` and `p`, such that for every `R > 0` and every `f ∈ Lᵖ`, the truncation
`𝓕⁻ (φ (R⁻¹ ·) • 𝓕 f)` is a bounded function with
`‖𝓕⁻ (φ (R⁻¹ ·) • 𝓕 f)‖_∞ ≤ C R ^ (n / p) ‖f‖_p`, where `n` is the dimension of `E` and
`1/∞ = 0`. -/
theorem exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le_mul_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      ∃ g : Lp F ∞ (volume : Measure E),
        fourierMultiplierCLM F (fun ξ ↦ (φ (R⁻¹ • ξ) : ℂ)) (f : 𝓢'(E, F)) = g ∧
          ‖g‖ ≤ C * R ^ ((Module.finrank ℝ E : ℝ) * p.toReal⁻¹) * ‖f‖ := by
  obtain ⟨B, hB, hBern⟩ := TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier
    (E := E) (F := F) (p := p) (q := ∞) le_top
  set K := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  set e := (Module.finrank ℝ E : ℝ) * p.toReal⁻¹
  have hK : 0 ≤ K := integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨B * φ.rOut ^ e * K,
    mul_nonneg (mul_nonneg hB (Real.rpow_nonneg φ.rOut_pos.le _)) hK, fun {R} hR f ↦ ?_⟩
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le φ hR.ne' f
  -- The truncation is band-limited to the ball of radius `R φ.rOut`.
  have hspec : IsVanishingOn (𝓕 (g : 𝓢'(E, F)) : 𝓢'(E, F))
      (Metric.closedBall 0 (R * φ.rOut))ᶜ := by
    rw [← hg]
    exact isVanishingOn_fourier_fourierMultiplierCLM (φ.ofReal_apply_inv_smul_eq_zero hR) _
  obtain ⟨g', hg', hg'g⟩ := hBern (mul_pos hR φ.rOut_pos) g hspec
  refine ⟨g', hg.trans hg', ?_⟩
  simp only [ENNReal.toReal_top, inv_zero, sub_zero] at hg'g
  rw [Real.mul_rpow hR.le φ.rOut_pos.le] at hg'g
  calc ‖g'‖ ≤ B * (R ^ e * φ.rOut ^ e) * ‖g‖ := hg'g
    _ ≤ B * (R ^ e * φ.rOut ^ e) * (K * ‖f‖) :=
        mul_le_mul_of_nonneg_left hgf (mul_nonneg hB (mul_nonneg (Real.rpow_nonneg hR.le _)
          (Real.rpow_nonneg φ.rOut_pos.le _)))
    _ = B * φ.rOut ^ e * K * R ^ e * ‖f‖ := by ring

/-- **Low-frequency vanishing of `Lᵖ` functions.** On a nontrivial space, for `1 ≤ p < ∞` and
`f ∈ Lᵖ`, the low-pass truncations `𝓕⁻ (φ (2^{-a} ·) • 𝓕 f)` converge to `0` as `a → -∞`. -/
theorem tendsto_fourierMultiplierCLM_two_zpow_atBot [Nontrivial E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (f : Lp F p (volume : Measure E)) :
    Tendsto (fun a : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ))
      (f : 𝓢'(E, F))) atBot (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le_mul_rpow φ (F := F)
    (p := p)
  choose g hg hgn using fun a : ℤ ↦ hC (zpow_pos two_pos a) f
  have he : 0 < (Module.finrank ℝ E : ℝ) * p.toReal⁻¹ := by
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
    have : 0 < Module.finrank ℝ E := Module.finrank_pos
    positivity
  -- The `L^∞` norms of the truncations tend to `0`.
  have hbound : Tendsto (fun a : ℤ ↦ C * ((2 : ℝ) ^ a) ^ ((Module.finrank ℝ E : ℝ) * p.toReal⁻¹)
      * ‖f‖) atBot (𝓝 0) := by
    have := (((TauCeti.tendsto_zpow_atBot_nhds_zero_of_one_lt one_lt_two).rpow_const
      (Or.inr he.le)).const_mul C).mul_const ‖f‖
    rwa [Real.zero_rpow he.ne', mul_zero, zero_mul] at this
  have hg0 : Tendsto g atBot (𝓝 0) :=
    squeeze_zero_norm (fun a ↦ hgn a) hbound
  have := ((Lp.toTemperedDistributionCLM F volume ∞).continuous.tendsto 0).comp hg0
  rw [map_zero] at this
  exact this.congr fun a ↦ (hg a).symm

/-- **Every `Lᵖ` function, `p < ∞`, is the sum of its homogeneous blocks.** On a nontrivial space,
for `1 ≤ p < ∞` and `f ∈ Lᵖ`, the two-sided partial sums `∑_{a < j ≤ b} Pⱼ f` converge to `f` in
the tempered distributions as `a → -∞` and `b → ∞`. -/
theorem tendsto_sum_homogeneousLittlewoodPaleyBlock_of_ne_top [Nontrivial E] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (f : Lp F p (volume : Measure E)) :
    Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j (f : 𝓢'(E, F)))
        (atBot ×ˢ atTop) (𝓝 (f : 𝓢'(E, F))) :=
  (tendsto_sum_homogeneousLittlewoodPaleyBlock_iff φ _).2
    (tendsto_fourierMultiplierCLM_two_zpow_atBot φ hp f)

/-- **Reconstruction modulo spectrum at the origin from summable low frequencies.** If the blocks
`P₋ₖ u`, `k ∈ ℕ`, of nonpositive index are bounded functions `gₖ` with `∑ₖ ‖gₖ‖_∞ < ∞`, then the
two-sided partial sums `∑_{a < j ≤ b} Pⱼ u` converge in the tempered distributions, as `a → -∞`
and `b → ∞`, to a distribution `v` such that the Fourier transform of `u - v` vanishes on
`E \ {0}`. The high-frequency partial sums converge for every tempered distribution; the
hypothesis makes the low-frequency ones converge in `L^∞`. -/
theorem exists_tendsto_sum_homogeneousLittlewoodPaleyBlock_of_summable {u : 𝓢'(E, F)}
    {g : ℕ → Lp F ∞ (volume : Measure E)}
    (hg : ∀ k : ℕ, homogeneousLittlewoodPaleyBlock F φ (-k) u = g k)
    (hsum : Summable fun k ↦ ‖g k‖) :
    ∃ v : 𝓢'(E, F), Tendsto (fun ab : ℤ × ℤ ↦
        ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
          (atBot ×ˢ atTop) (𝓝 v) ∧ IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ := by
  obtain ⟨w, hw⟩ := hsum.of_norm
  -- The low-frequency partial sums `∑_{a < j ≤ 0} Pⱼ u` converge to `w` as `a → -∞`.
  have hlow : Tendsto (fun a : ℤ ↦ ∑ j ∈ Finset.Ioc a 0, homogeneousLittlewoodPaleyBlock F φ j u)
      atBot (𝓝 (w : 𝓢'(E, F))) := by
    have hw' := ((Lp.toTemperedDistributionCLM F volume ∞).continuous.tendsto w).comp
      hw.tendsto_sum_nat
    have htoNat : Tendsto (fun a : ℤ ↦ (-a).toNat) atBot atTop :=
      tendsto_atTop.2 fun N ↦ (eventually_le_atBot (-(N : ℤ))).mono fun a ha ↦ by omega
    refine (hw'.comp htoNat).congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℤ)] with a ha
    have ha' : a = -(((-a).toNat : ℕ) : ℤ) := by omega
    rw [ha', Finset.sum_Ioc_neg_zero_eq_sum_range, ← ha']
    simp only [Function.comp_apply, map_sum, Lp.toTemperedDistributionCLM_apply, hg]
  -- The high-frequency partial sums `∑_{0 < j ≤ b} Pⱼ u` telescope to `S_b u - S_0 u → u - S_0 u`.
  have hhigh : Tendsto (fun b : ℤ ↦ ∑ j ∈ Finset.Ioc 0 b, homogeneousLittlewoodPaleyBlock F φ j u)
      atTop (𝓝 (u - fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ) : ℂ)) u)) := by
    refine ((tendsto_fourierMultiplierCLM_two_zpow_atTop φ u).sub_const _).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with b hb
    rw [← _root_.sum_apply, sum_homogeneousLittlewoodPaleyBlock_Ioc φ hb, _root_.sub_apply]
  have hsplit : (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u) =ᶠ[atBot ×ˢ atTop]
      fun ab ↦ (∑ j ∈ Finset.Ioc ab.1 0, homogeneousLittlewoodPaleyBlock F φ j u) +
        ∑ j ∈ Finset.Ioc 0 ab.2, homogeneousLittlewoodPaleyBlock F φ j u := by
    filter_upwards [tendsto_fst.eventually (eventually_le_atBot (0 : ℤ)),
      tendsto_snd.eventually (eventually_ge_atTop (0 : ℤ))] with ab ha hb
    rw [← Finset.Ioc_union_Ioc_eq_Ioc ha hb,
      Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  have hlim := ((hlow.comp tendsto_fst).add (hhigh.comp tendsto_snd)).congr' hsplit.symm
  exact ⟨_, hlim, isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock φ hlim⟩

end Lp

/-! ### The blocks of `L²` functions -/

section L2

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The homogeneous blocks of `L²` functions.** On `f ∈ L²`, the homogeneous block `Pⱼ` is the
`L²` Fourier multiplier with symbol `ψⱼ`, given by any element of `L^∞` almost everywhere equal to
`ψⱼ`. -/
theorem homogeneousLittlewoodPaleyBlock_toTemperedDistribution {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (f : Lp G 2 (volume : Measure E)) :
    homogeneousLittlewoodPaleyBlock G φ j (f : 𝓢'(E, G)) =
      (Lp.fourierMultiplierCLM G m f : 𝓢'(E, G)) := by
  have hmem : MemLp (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) ∞ (volume : Measure E) :=
    (Lp.memLp m).ae_eq hm
  rw [show m = hmem.toLp _ from Lp.ext (hm.trans hmem.coeFn_toLp.symm),
    homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM]
  exact Lp.fourierMultiplierCLM_toTemperedDistribution_eq f
    (φ.hasTemperateGrowth_ofReal_littlewoodPaley j) hmem

/-- **Almost orthogonality of the blocks on `L²`.** There is `L` such that an `L²` function `f`
that is the `j`-th block `Pⱼ v` of a tempered distribution `v` has no block `Pₖ` with
`|k - j| ≥ L`: the `L²` Fourier multiplier with symbol `ψₖ` vanishes on `f`. -/
theorem exists_fourierMultiplierCLM_eq_zero_of_eq_homogeneousLittlewoodPaleyBlock :
    ∃ L : ℕ, ∀ j k : ℤ, k ∉ Finset.Ioo (j - L) (j + L) → ∀ {m : Lp ℂ ∞ (volume : Measure E)},
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley k ξ : ℂ)) →
      ∀ (f : Lp G 2 (volume : Measure E)) (v : 𝓢'(E, G)),
        (f : 𝓢'(E, G)) = homogeneousLittlewoodPaleyBlock G φ j v →
          Lp.fourierMultiplierCLM G m f = 0 := by
  obtain ⟨L, hL⟩ := exists_homogeneousLittlewoodPaleyBlock_compL_eq_zero (F := G) φ φ
  refine ⟨L, fun j k hk m hm f v hf ↦ Lp.toTemperedDistribution_injective ?_⟩
  dsimp only
  rw [← homogeneousLittlewoodPaleyBlock_toTemperedDistribution φ hm, hf,
    Lp.toTemperedDistribution_zero]
  rw [Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hk
  rcases hk with hk | hk
  · exact congr($((hL k j (by omega)).1) v)
  · exact congr($((hL j k (by omega)).2) v)

/-- **Almost orthogonality of the blocks in mixed norms.** There are `L` and `K`, depending only on
`φ`, such that for every family `x : α → L²` whose values are almost everywhere `j`-th blocks
`Pⱼ v` of tempered distributions, every block `Pₖ`, acting on `L²` as the Fourier multiplier with
any symbol almost everywhere equal to `ψₖ`, satisfies, for `1 ≤ r`,

`‖Pₖ x‖_{L^p_α L^r} = 0` for `|k - j| ≥ L`, and `‖Pₖ x‖_{L^p_α L^r} ≤ K ‖x‖_{L^p_α L^r}`.

Over a one-point measure space this bounds the blocks of a single `L²` function. -/
theorem exists_eLpNorm_eLpNorm_fourierMultiplierCLM_of_eq_homogeneousLittlewoodPaleyBlock :
    ∃ (L : ℕ) (K : ℝ≥0), ∀ {α : Type*} {mα : MeasurableSpace α} {ρ : Measure α} {p r : ℝ≥0∞},
      1 ≤ r → ∀ {j : ℤ} {x : α → Lp G 2 (volume : Measure E)}, AEStronglyMeasurable x ρ →
      (∀ᵐ a ∂ρ, ∃ v : 𝓢'(E, G), (x a : 𝓢'(E, G)) = homogeneousLittlewoodPaleyBlock G φ j v) →
      ∀ {k : ℤ} {m : Lp ℂ ∞ (volume : Measure E)},
        m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley k ξ : ℂ)) →
        (k ∉ Finset.Ioo (j - L) (j + L) →
          eLpNorm (fun a ↦ eLpNorm (Lp.fourierMultiplierCLM G m (x a)) r volume) p ρ = 0) ∧
        eLpNorm (fun a ↦ eLpNorm (Lp.fourierMultiplierCLM G m (x a)) r volume) p ρ ≤
          K * eLpNorm (fun a ↦ eLpNorm (x a) r volume) p ρ := by
  obtain ⟨L, hL⟩ := exists_fourierMultiplierCLM_eq_zero_of_eq_homogeneousLittlewoodPaleyBlock
    (G := G) φ
  refine ⟨L, (eLpNorm (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))) 1 volume).toNNReal,
    fun {_ _ _ _ r} hr {j x} hx hblock {k m} hm ↦ ⟨fun hk ↦ ?_, ?_⟩⟩
  · have h0 : (fun a ↦ eLpNorm (Lp.fourierMultiplierCLM G m (x a)) r volume) =ᵐ[_] 0 :=
      hblock.mono fun a ⟨v, hv⟩ ↦ by
        dsimp only [Pi.zero_apply]
        rw [hL j k hk hm (x a) v hv, eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    rw [eLpNorm_congr_ae h0, eLpNorm_zero]
  · rw [ENNReal.coe_toNNReal (φ.memLp_fourierInv_littlewoodPaley 0 1).eLpNorm_ne_top]
    exact eLpNorm_eLpNorm_apply_le (Lp.fourierMultiplierCLM G m).continuous
      (fun f ↦ φ.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le hm f hr) hx

end L2

end TemperedDistribution
