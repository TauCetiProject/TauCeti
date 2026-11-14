/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The homogeneous Littlewood–Paley blocks of a tempered distribution

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and
let `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`, `j ∈ ℤ`, be the dyadic cutoffs built from it
(`ContDiffBump.littlewoodPaley`), supported in the annuli `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`. The
**homogeneous Littlewood–Paley blocks** of a tempered distribution `u` are the Fourier multipliers

`\dot Δⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)`, `j ∈ ℤ`.

Unlike the inhomogeneous blocks `Δⱼ` (`TemperedDistribution.littlewoodPaleyBlock`), which keep
the low-frequency piece `Δ₀` with symbol `φ`, the homogeneous blocks resolve the frequencies near
the origin into infinitely many dyadic annuli; for `j ≥ 1` the two kinds of blocks agree. Since
every `ψⱼ` vanishes near the origin, the blocks cannot see the frequency `0`: all the blocks of
`u` vanish exactly when the Fourier transform of `u` is supported at the origin
(`TemperedDistribution.forall_homogeneousLittlewoodPaleyBlock_eq_zero_iff`). These are the
polynomials, and in particular the constants, whose Fourier transform is a Dirac mass at the
origin. This is why the homogeneous function spaces built from these blocks, such as the
homogeneous Besov spaces `\dot B^s_{p,q}`, consist of tempered distributions modulo polynomials.

As for the inhomogeneous blocks, the blocks built from two bump functions interact only at nearby
indices, and the blocks are bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j ∈ ℤ`: the kernel
`𝓕⁻ ψⱼ` of `\dot Δⱼ` is the `L¹`-normalised dilate of `𝓕⁻ ψ₀`, since `ψⱼ = ψ₀ (2^{-j} ·)`.

## Main declarations

* `TemperedDistribution.homogeneousLittlewoodPaleyBlock`: the homogeneous block `\dot Δⱼ`, `j ∈ ℤ`.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_natCast`: `\dot Δⱼ = Δⱼ` for `j ≥ 1`.
* `TemperedDistribution.isVanishingOn_fourier_homogeneousLittlewoodPaleyBlock`: the Fourier
  transform of `\dot Δⱼ u` vanishes outside the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico`: each block of one bump
  function is a sum of boundedly many blocks of another, composed with it.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range`: a block
  `\dot Δⱼ` with `2^j φ.rOut ≤ 2^N φ.rIn` only sees the inhomogeneous blocks `Δₖ`, `k ≤ N`.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le`: the blocks are
  bounded on `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j ∈ ℤ`.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_le`: weighted `Lᵖ` norms of
  the blocks of one bump function are bounded by nearby weighted `Lᵖ` norms of the blocks of
  another.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_nonpos`: if the
  inhomogeneous blocks of `u` are `Lᵖ` functions, its blocks `\dot Δⱼ u`, `j ≤ 0`, are bounded in
  `Lᵖ`.
* `TemperedDistribution.forall_homogeneousLittlewoodPaleyBlock_eq_zero_iff`: all the blocks of `u`
  vanish exactly when `𝓕 u` vanishes away from the origin.
* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_volume_toTemperedDistribution`: the
  blocks of the constant function `1` vanish.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.2 and Section 2.4.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.3.
-/

public section

open Filter Topology MeasureTheory
open FourierTransform
open scoped SchwartzMap ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

variable (F) in
/-- The **homogeneous Littlewood–Paley block** `\dot Δⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)`, `j ∈ ℤ`, of a tempered
distribution, the Fourier multiplier by the dyadic cutoff `ψⱼ` built from `φ`. -/
noncomputable def homogeneousLittlewoodPaleyBlock (φ : ContDiffBump (0 : E)) (j : ℤ) :
    𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)

variable (φ : ContDiffBump (0 : E))

/-- Unfolding `TemperedDistribution.homogeneousLittlewoodPaleyBlock`. -/
theorem homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM (j : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j =
      fourierMultiplierCLM F (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :=
  (rfl)

/-- Unfolding `TemperedDistribution.homogeneousLittlewoodPaleyBlock` on a tempered
distribution. -/
theorem homogeneousLittlewoodPaleyBlock_apply (j : ℤ) (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j u =
      fourierMultiplierCLM F (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) u :=
  (rfl)

/-- For `j ≥ 1` the homogeneous block `\dot Δⱼ` is the inhomogeneous block `Δⱼ`. -/
theorem homogeneousLittlewoodPaleyBlock_natCast {j : ℕ} (hj : j ≠ 0) :
    homogeneousLittlewoodPaleyBlock F φ j = littlewoodPaleyBlock F φ j := by
  rw [homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    littlewoodPaleyBlock_eq_fourierMultiplierCLM, φ.inhomogeneousLittlewoodPaley_of_ne_zero hj]

/-- The Fourier transform of `\dot Δⱼ u` is the cutoff `ψⱼ` times the Fourier transform of `u`. -/
theorem fourier_homogeneousLittlewoodPaleyBlock (j : ℤ) (u : 𝓢'(E, F)) :
    𝓕 (homogeneousLittlewoodPaleyBlock F φ j u) =
      smulLeftCLM F (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (𝓕 u) := by
  rw [homogeneousLittlewoodPaleyBlock_apply, fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]

open Distribution in
/-- **The spectrum of a homogeneous block.** The Fourier transform of `\dot Δⱼ u` vanishes outside
the closed annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, which carries the cutoff `ψⱼ`. -/
theorem isVanishingOn_fourier_homogeneousLittlewoodPaleyBlock (j : ℤ) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (homogeneousLittlewoodPaleyBlock F φ j u) : 𝓢'(E, F))
      {ξ | 2 ^ (j - 1) * φ.rIn ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 ^ j * φ.rOut}ᶜ := by
  rw [homogeneousLittlewoodPaleyBlock_apply]
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ ?_) u
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hξ (φ.tsupport_littlewoodPaley_subset j h),
    Complex.ofReal_zero]

/-- The composition of the homogeneous blocks of two bump functions is the Fourier multiplier by
the product of the two cutoffs. -/
theorem homogeneousLittlewoodPaleyBlock_compL_homogeneousLittlewoodPaleyBlock
    (φ' : ContDiffBump (0 : E)) (j k : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j ∘L homogeneousLittlewoodPaleyBlock F φ' k =
      fourierMultiplierCLM F fun ξ ↦
        ((φ.littlewoodPaley j ξ * φ'.littlewoodPaley k ξ : ℝ) : ℂ) := by
  rw [homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_compL_fourierMultiplierCLM (φ'.hasTemperateGrowth_ofReal_littlewoodPaley k)
      (φ.hasTemperateGrowth_ofReal_littlewoodPaley j)]
  congr 1
  funext ξ
  simp [mul_comm]

/-- **Change of bump function.** The homogeneous blocks `\dot Δⱼ` and `\dot Δ'ₖ` built from two bump
functions `φ` and `φ'` interact only at nearby indices: there is `L`, depending only on `φ` and
`φ'`, such that `\dot Δ'ⱼ u = ∑_{j - L ≤ k < j + L} \dot Δ'ⱼ \dot Δₖ u` for every `j ∈ ℤ` and every
tempered distribution `u`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ (j : ℤ) (u : 𝓢'(E, F)), homogeneousLittlewoodPaleyBlock F φ' j u =
      ∑ k ∈ Finset.Ico (j - L) (j + L),
        homogeneousLittlewoodPaleyBlock F φ' j (homogeneousLittlewoodPaleyBlock F φ k u) := by
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_sum_Ico_eq φ'
  refine ⟨L, fun j u ↦ ?_⟩
  rw [homogeneousLittlewoodPaleyBlock_apply φ' j u]
  simp_rw [← ContinuousLinearMap.comp_apply,
    homogeneousLittlewoodPaleyBlock_compL_homogeneousLittlewoodPaleyBlock φ',
    ← _root_.sum_apply]
  rw [← fourierMultiplierCLM_sum F fun k _ ↦ by fun_prop]
  simp_rw [← Complex.ofReal_sum, ← Finset.mul_sum, hL j]

/-- **The low-frequency blocks see only the low frequencies.** If the cutoff `ψⱼ` is carried by
the ball where `φ (2^{-N} ·) = 1`, that is `2^j φ.rOut ≤ 2^N φ.rIn`, then `\dot Δⱼ` does not see the
inhomogeneous blocks `Δₖ`, `k > N`: `\dot Δⱼ (∑_{k ≤ N} Δₖ u) = \dot Δⱼ u`. -/
theorem homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range {j : ℤ} {N : ℕ}
    (hjN : 2 ^ j * φ.rOut ≤ 2 ^ N * φ.rIn) (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j
        (∑ k ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ k u) =
      homogeneousLittlewoodPaleyBlock F φ j u := by
  have hc : (fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [← _root_.sum_apply, sum_littlewoodPaleyBlock_range,
    homogeneousLittlewoodPaleyBlock_apply, homogeneousLittlewoodPaleyBlock_apply,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hc
      (φ.hasTemperateGrowth_ofReal_littlewoodPaley j)]
  refine congrArg (fun g ↦ fourierMultiplierCLM F g u) (funext fun ξ ↦ ?_)
  -- On the support of `ψⱼ`, `‖ξ‖ ≤ 2^j φ.rOut ≤ 2^N φ.rIn`, where `φ (2^{-N} ξ) = 1`.
  by_cases hξ : φ.littlewoodPaley j ξ = 0
  · simp only [Pi.mul_apply, hξ, Complex.ofReal_zero, mul_zero]
  have hle : ‖ξ‖ ≤ 2 ^ N * φ.rIn :=
    le_trans (not_le.1 (mt φ.littlewoodPaley_eq_zero_of_le_norm hξ)).le hjN
  rw [Pi.mul_apply, φ.one_of_mem_closedBall, Complex.ofReal_one, one_mul]
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_pow, Real.norm_two,
    inv_mul_le_iff₀ (by positivity)]
  exact hle

/-- **The homogeneous blocks are bounded on `Lᵖ` uniformly in `j`.** There is `C`, depending only on
`φ`, such that for every `1 ≤ p ≤ ∞`, every `j ∈ ℤ` and every `f ∈ Lᵖ`, the block `\dot Δⱼ f` is a
function in `Lᵖ` with `‖\dot Δⱼ f‖_p ≤ C ‖f‖_p`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le [CompleteSpace F] :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℤ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        homogeneousLittlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  refine ⟨∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ)) x‖, fun {p} _ j f ↦ ?_⟩
  -- The kernel `𝓕⁻ ψⱼ` is an `L¹`-normalised dilate of `𝓕⁻ ψ₀`, since `ψⱼ = ψ₀ (2^{-j} ·)`.
  have hK : ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) x‖ =
      ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ)) x‖ := by
    simp_rw [φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply j]
    exact TauCeti.integral_norm_fourierInv_comp_smul (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))
      (inv_ne_zero (zpow_ne_zero _ two_ne_zero))
  -- The symbol `ψⱼ` is smooth and compactly supported, hence a Schwartz function.
  have hσ := (φ.hasCompactSupport_littlewoodPaley j).comp_left Complex.ofReal_zero
  set σ : 𝓢(E, ℂ) :=
    hσ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (φ.contDiff_littlewoodPaley j))
  have hσ_coe : (σ : E → ℂ) = fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ f
  rw [hσ_coe, hK] at hgf
  rw [hσ_coe] at hg
  exact ⟨g, hg, hgf⟩

/-- **The blocks of another bump function.** If the homogeneous blocks `\dot Δₖ u` built from `φ`
are `Lᵖ` functions `fₖ`, then the homogeneous blocks `\dot Δ'ⱼ u` built from `φ'` are `Lᵖ` functions
`f'ⱼ`, with `2^{js} ‖f'ⱼ‖_p ≤ K ∑_{j - L ≤ k < j + L} 2^{ks} ‖fₖ‖_p`. The constants `K` and `L`
depend only on `φ`, `φ'` and `s`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_le [CompleteSpace F]
    (φ' : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ K : ℝ, ∃ L : ℕ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (f : ℤ → Lp F p (volume : Measure E)),
      (∀ k, homogeneousLittlewoodPaleyBlock F φ k u = f k) →
      ∃ f' : ℤ → Lp F p (volume : Measure E),
        (∀ j, homogeneousLittlewoodPaleyBlock F φ' j u = f' j) ∧
        ∀ j : ℤ, 2 ^ (s * j) * ‖f' j‖ ≤
          K * ∑ k ∈ Finset.Ico (j - L) (j + L), 2 ^ (s * k) * ‖f k‖ := by
  obtain ⟨L, hL⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ'
  obtain ⟨C, hC⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le (F := F) φ'
  refine ⟨max C 0 * 2 ^ (|s| * L), L, by positivity, fun {p} _ {u} f hf ↦ ?_⟩
  choose g hg hgC using fun j k ↦ hC (p := p) j (f k)
  refine ⟨fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), g j k, fun j ↦ ?_, fun j ↦ ?_⟩
  · rw [hL j u]
    simp_rw [hf, hg]
    exact (map_sum (Lp.toTemperedDistributionCLM F volume p) _ _).symm
  · refine TauCeti.two_rpow_mul_norm_sum_le s (hgC j) fun k hk ↦ ?_
    rw [Finset.mem_Ico] at hk
    refine abs_sub_le_iff.2 ⟨?_, ?_⟩
    all_goals rw [sub_le_iff_le_add']; exact_mod_cast (by omega)

variable {φ} in
/-- **The low-frequency homogeneous blocks are bounded in `Lᵖ`.** If the inhomogeneous blocks
`Δₖ u` are `Lᵖ` functions `fₖ`, then there are `B` and `Lᵖ` functions `G j` with `\dot Δⱼ u = G j`
and `‖G j‖_p ≤ B` for every `j ≤ 0`. They are blocks of the `Lᵖ` function `∑_{k ≤ N} Δₖ u`, for `N`
with `φ.rOut ≤ 2^N φ.rIn`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_nonpos [CompleteSpace F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)} {f : ℕ → Lp F p (volume : Measure E)}
    (hf : ∀ k, littlewoodPaleyBlock F φ k u = f k) :
    ∃ B : ℝ, ∃ G : ℤ → Lp F p (volume : Measure E), ∀ j ≤ 0,
      homogeneousLittlewoodPaleyBlock F φ j u = G j ∧ ‖G j‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) (one_lt_two (α := ℝ))
  set S : Lp F p (volume : Measure E) := ∑ k ∈ Finset.range (N + 1), f k
  choose G hG hGC using fun j : ℤ ↦ hC (p := p) j S
  refine ⟨C * ‖S‖, G, fun j hj ↦ ⟨?_, hGC j⟩⟩
  have hjN : (2 : ℝ) ^ j * φ.rOut ≤ 2 ^ N * φ.rIn :=
    calc (2 : ℝ) ^ j * φ.rOut ≤ 1 * φ.rOut :=
          mul_le_mul_of_nonneg_right (zpow_le_one_of_nonpos₀ (one_le_two (α := ℝ)) hj)
            φ.rOut_pos.le
      _ ≤ 2 ^ N * φ.rIn := by rw [one_mul]; exact ((div_lt_iff₀ φ.rIn_pos).1 hN).le
  rw [← homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range φ hjN, ← hG j]
  congr 1
  rw [Finset.sum_congr rfl fun k _ ↦ hf k]
  exact (map_sum (Lp.toTemperedDistributionCLM F volume p) _ _).symm

open Distribution

/-- If the Fourier transform of `u` vanishes away from the origin, then every homogeneous block of
`u` vanishes. -/
theorem homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn {u : 𝓢'(E, F)}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) {0}ᶜ) (j : ℤ) :
    homogeneousLittlewoodPaleyBlock F φ j u = 0 := by
  -- The multiplier by `1 - ψⱼ` fixes `u`, since `ψⱼ` is supported away from the origin.
  have hψ := φ.hasTemperateGrowth_ofReal_littlewoodPaley j
  have h1 : fourierMultiplierCLM F (fun ξ ↦ 1 - (φ.littlewoodPaley j ξ : ℂ)) u = u := by
    refine fourierMultiplierCLM_eq_self_of_isVanishingOn hu (by fun_prop) ?_
    have : ((fun ξ ↦ 1 - (φ.littlewoodPaley j ξ : ℂ)) - 1) =
        -fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) := by
      funext ξ
      simp
    rw [this, tsupport_neg, Set.subset_compl_singleton_iff]
    exact fun h ↦ φ.zero_notMem_tsupport_littlewoodPaley j
      (tsupport_comp_subset Complex.ofReal_zero _ h)
  -- Split `1 - ψⱼ` as `1 + (-1) • ψⱼ`; the second multiplier is `-\dot Δⱼ`.
  have h2 : (fun ξ ↦ 1 - (φ.littlewoodPaley j ξ : ℂ)) =
      (fun _ ↦ (1 : ℂ)) + (-1 : ℂ) • fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) := by
    funext ξ
    simp [sub_eq_add_neg]
  rw [h2, fourierMultiplierCLM_add (by fun_prop) (by rw [neg_one_smul]; exact hψ.neg),
    fourierMultiplierCLM_smul hψ,
    ← homogeneousLittlewoodPaleyBlock_eq_fourierMultiplierCLM] at h1
  simpa using h1

/-- **The common kernel of the homogeneous blocks.** All the homogeneous blocks of a tempered
distribution `u` vanish exactly when its Fourier transform vanishes away from the origin, that
is, when `𝓕 u` is supported in `{0}`. -/
theorem forall_homogeneousLittlewoodPaleyBlock_eq_zero_iff {u : 𝓢'(E, F)} :
    (∀ j, homogeneousLittlewoodPaleyBlock F φ j u = 0) ↔
      IsVanishingOn (𝓕 u : 𝓢'(E, F)) {0}ᶜ := by
  refine ⟨fun h ψ hψ ↦ ?_, fun hu ↦ homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn φ hu⟩
  -- `ψ` vanishes on a ball `B(0, r)`.
  obtain ⟨r, hr, hψr⟩ := Metric.eventually_nhds_iff.1
    ((notMem_tsupport_iff_eventuallyEq).1 fun h0 ↦ hψ h0 rfl)
  -- Choose `a` with `2^a φ.rOut ≤ r`, so that `φ (2^{-a} ·)` vanishes outside `B(0, r)`.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (φ.rOut / r) (one_lt_two (α := ℝ))
  set a : ℤ := -n
  have ha : ∀ ξ : E, φ (((2 : ℝ) ^ a)⁻¹ • ξ) * ψ ξ = 0 := fun ξ ↦ by
    rcases lt_or_ge ‖ξ‖ r with hξ | hξ
    · rw [show ψ ξ = 0 from hψr (by rwa [dist_zero_right]), mul_zero]
    · refine mul_eq_zero_of_left ?_ _
      rw [φ.zero_of_le_dist, Complex.ofReal_zero]
      rw [dist_zero_right, norm_smul, zpow_neg, zpow_natCast, inv_inv,
        Real.norm_of_nonneg (by positivity)]
      calc φ.rOut ≤ 2 ^ n * r := ((div_lt_iff₀ hr).1 hn).le
        _ ≤ 2 ^ n * ‖ξ‖ := by gcongr
  -- Each block contributes nothing: `𝓕 u (ψⱼ ψ) = 𝓕 (\dot Δⱼ u) ψ = 0`.
  have hblock : ∀ j, 𝓕 u (SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) ψ) = 0 :=
    fun j ↦ by
      rw [← smulLeftCLM_apply_apply, ← fourier_homogeneousLittlewoodPaleyBlock, h j,
        FourierTransform.fourier_zero, zero_apply]
  -- For `N ≥ a`, the truncation `φ (2^{-N} ·) ψ` is the sum of the pieces `ψⱼ ψ`, `a < j ≤ N`.
  have hsum : ∀ N : ℕ, SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ)) ψ =
      ∑ j ∈ Finset.Ioc a N,
        SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) ψ := fun N ↦ by
    have hc : (fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ)).HasTemperateGrowth := by fun_prop
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hc, _root_.sum_apply]
    simp_rw [SchwartzMap.smulLeftCLM_apply_apply (φ.hasTemperateGrowth_ofReal_littlewoodPaley _)]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum,
      φ.sum_littlewoodPaley_Ioc (by simp [a]), zpow_natCast]
    have := ha ξ
    simp only [smul_eq_mul] at this ⊢
    push_cast
    linear_combination this
  have hlim := ((map_continuous (𝓕 u)).tendsto ψ).comp
    (SchwartzMap.tendsto_smulLeftCLM_contDiffBump_two_pow φ ψ)
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun N ↦ ?_)
  rw [Function.comp_apply, hsum, map_sum, Finset.sum_eq_zero fun j _ ↦ hblock j]

/-- **The blocks of a constant vanish.** Every homogeneous block of the constant function `1`,
the tempered distribution `ψ ↦ ∫ ψ`, is zero: its Fourier transform is the Dirac mass at the
origin. -/
@[simp]
theorem homogeneousLittlewoodPaleyBlock_volume_toTemperedDistribution (j : ℤ) :
    homogeneousLittlewoodPaleyBlock ℂ φ j (volume.toTemperedDistribution : 𝓢'(E, ℂ)) = 0 := by
  refine homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn φ (fun ψ hψ ↦ ?_) j
  -- `𝓕 1 ψ = ∫ 𝓕 ψ = 𝓕⁻ (𝓕 ψ) 0 = ψ 0`, by Fourier inversion.
  have h0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hψ h rfl
  have hinv : (𝓕⁻ (𝓕 ψ) : 𝓢(E, ℂ)) 0 = ψ 0 := by rw [FourierTransform.fourierInv_fourier_eq]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at hinv
  simpa [h0] using hinv

end TemperedDistribution
