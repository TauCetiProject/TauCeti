/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Calculus.BumpFunction.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.SpecificLimits.ZPow

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
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_compL_eq_zero`: almost
  orthogonality, also between the blocks of two bump functions.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le`: the blocks are
  bounded on `Lᵖ`, uniformly in `j ∈ ℤ`, and
  `TemperedDistribution.exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le_mul_rpow`: the
  truncation at scale `R` of an `Lᵖ` function is `O(R ^ (n / p))` in `L^∞`.
* `TemperedDistribution.tendsto_fourierMultiplierCLM_two_zpow_atTop`: `Sᵦ u → u` as `b → ∞`.
* `TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_iff`: the homogeneous
  reconstruction holds exactly when `Sₐ u → 0` as `a → -∞`, and
  `TemperedDistribution.isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock`:
  in general it holds modulo distributions with spectrum at the origin.
* `TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_of_ne_top`: every `Lᵖ`
  function, `p < ∞`, is the sum of its homogeneous blocks.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.4
  (homogeneous Littlewood–Paley decomposition) and Section 1.5 (the space `𝓢'_h`).
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 2.4.
-/

public section

open Filter Topology MeasureTheory
open FourierTransform Distribution
open scoped SchwartzMap LineDeriv ENNReal

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

end Lp

end TemperedDistribution
