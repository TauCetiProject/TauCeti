/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
public import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Plane waves and their Littlewood–Paley blocks

For a frequency `ξ` in a finite-dimensional real inner product space `E`, the **plane wave**
`e_ξ(x) = 𝐞 ⟪x, ξ⟫ = exp(2πi ⟪x, ξ⟫)` is a smooth function of temperate growth, and as a tempered
distribution it is the inverse Fourier transform of the Dirac mass at `ξ`
(`TemperedDistribution.fourierInv_delta`). Its spectrum is the single point `ξ`, so it is the
basic example on which the dyadic decomposition can be computed exactly.

* Every Fourier multiplier acts on `e_ξ` by its value at `ξ`; in particular the Littlewood–Paley
  blocks are `Δⱼ e_ξ = ψⱼ(ξ) e_ξ` (`TemperedDistribution.littlewoodPaleyBlock_fourierInv_delta`).
  If `2^j φ.rOut ≤ ‖ξ‖ ≤ 2^{j+1} φ.rIn`, the plane wave is its own block of index `j + 1` and all
  its other blocks vanish
  (`TemperedDistribution.littlewoodPaleyBlock_fourierInv_delta_of_le_norm_of_norm_le`); for the bump
  with `φ.rIn = 1` and `φ.rOut = 2` this is the frequency `‖ξ‖ = 2^{j+1}`. The index is that of
  the piece `ψ_{j+1} = φ (2^{-(j+1)} ·) - φ (2^{-j} ·)` of the convention here, which is
  supported in the annulus `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`. If `‖ξ‖ ≤ φ.rIn`, the plane wave
  is its own low-frequency block `Δ₀` and has no other block
  (`TemperedDistribution.littlewoodPaleyBlock_fourierInv_delta_of_norm_le`). For `ξ = 0` this is
  the constant function `1`, which is the distribution `volume.toTemperedDistribution`
  (`TemperedDistribution.fourierInv_delta_zero`): `Δ₀ 1 = 1` and `Δⱼ 1 = 0` for `j ≥ 1`
  (`TemperedDistribution.littlewoodPaleyBlock_toTemperedDistribution_volume`).
* Differentiation multiplies `e_ξ` by its frequency, `∂_m e_ξ = 2πi ⟪ξ, m⟫ e_ξ`
  (`TemperedDistribution.lineDerivOp_fourierInv_delta`). Since `|e_ξ| = 1`, the plane wave of
  frequency `‖ξ‖ = R` in the direction `m = ξ / R` has `‖∂_m e_ξ‖_∞ = 2π R ‖e_ξ‖_∞`, while its
  spectrum lies in the closed ball of radius `R`. Hence the constant in Bernstein's inequality
  `‖∂_m f‖_∞ ≤ C R ‖m‖ ‖f‖_∞` for functions with spectrum in the ball of radius `R`
  (`TauCeti.exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`) is at least `2π`
  (`TauCeti.two_mul_pi_le_of_forall_lineDerivOp_eq_and_norm_le`).

## Main declarations

* `TemperedDistribution.fourierInv_delta`, `TemperedDistribution.fourierInv_delta_zero`: the
  inverse Fourier transform of `δ_ξ` is the plane wave `e_ξ`, and that of `δ₀` is the constant `1`.
* `TemperedDistribution.littlewoodPaleyBlock_fourierInv_delta`,
  `TemperedDistribution.littlewoodPaleyBlock_fourierInv_delta_of_le_norm_of_norm_le`,
  `TemperedDistribution.littlewoodPaleyBlock_fourierInv_delta_of_norm_le`: the blocks of plane
  waves.
* `TemperedDistribution.lineDerivOp_fourierInv_delta`: the derivatives of a plane wave.
* `TauCeti.two_mul_pi_le_of_forall_lineDerivOp_eq_and_norm_le`: the constant of Bernstein's
  inequality for one derivative in `L^∞` is at least `2π`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.1 (Bernstein's lemma) and Section 2.2 (the Littlewood–Paley
  decomposition).
-/

public section

open MeasureTheory Metric
open FourierTransform Real
open scoped SchwartzMap LineDeriv RealInnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

/-- **The inverse Fourier transform of a Dirac mass is a plane wave.** As tempered distributions,
`𝓕⁻ δ_ξ` is the function `x ↦ 𝐞 ⟪x, ξ⟫`. -/
theorem fourierInv_delta (ξ : E) :
    𝓕⁻ (delta ξ) = (hasTemperateGrowth_fourierChar_inner ξ).toTemperedDistribution := by
  ext f
  simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Circle.smul_def, mul_comm]

/-- **The inverse Fourier transform of `δ₀` is the constant function `1`**, which as a tempered
distribution is integration against the volume. -/
theorem fourierInv_delta_zero : 𝓕⁻ (delta (0 : E)) = volume.toTemperedDistribution := by
  ext f
  simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]

variable (φ : ContDiffBump (0 : E))

/-- **The Littlewood–Paley blocks of a plane wave.** The block `Δⱼ` multiplies the plane wave
`𝓕⁻ δ_ξ` by the value `ψⱼ(ξ)` of the `j`-th piece of the partition. -/
@[simp]
theorem littlewoodPaleyBlock_fourierInv_delta (j : ℕ) (ξ : E) :
    littlewoodPaleyBlock ℂ φ j (𝓕⁻ (delta ξ)) =
      (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) • 𝓕⁻ (delta ξ) := by
  rw [littlewoodPaleyBlock_apply, fourierMultiplierCLM_fourierInv_delta
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)]

/-- **A plane wave of dyadic frequency is a single block.** If `2^j φ.rOut ≤ ‖ξ‖ ≤ 2^{j+1} φ.rIn`,
then the plane wave `𝓕⁻ δ_ξ` is its own block of index `j + 1`, and all its other blocks vanish. -/
theorem littlewoodPaleyBlock_fourierInv_delta_of_le_norm_of_norm_le {j : ℕ} {ξ : E}
    (h₁ : 2 ^ j * φ.rOut ≤ ‖ξ‖) (h₂ : ‖ξ‖ ≤ 2 ^ (j + 1) * φ.rIn) (k : ℕ) :
    littlewoodPaleyBlock ℂ φ k (𝓕⁻ (delta ξ)) = if k = j + 1 then 𝓕⁻ (delta ξ) else 0 := by
  rw [littlewoodPaleyBlock_fourierInv_delta]
  split_ifs with hk
  · subst hk
    rw [φ.inhomogeneousLittlewoodPaley_succ_eq_one_of_le_norm_of_norm_le h₁ h₂]
    simp
  · rcases le_or_gt k j with hkj | hkj
    · rw [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm]
      · simp
      have hr : 0 < φ.rOut := φ.rOut_pos
      exact le_trans (by gcongr; norm_num) h₁
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le]
      · simp
      have hr : 0 < φ.rIn := φ.rIn_pos
      exact h₂.trans (by gcongr <;> first | omega | norm_num)

/-- **A plane wave of low frequency is its own low-frequency block.** If `‖ξ‖ ≤ φ.rIn`, then the
plane wave `𝓕⁻ δ_ξ` is its block `Δ₀`, and all its other blocks vanish. -/
theorem littlewoodPaleyBlock_fourierInv_delta_of_norm_le {ξ : E} (h : ‖ξ‖ ≤ φ.rIn) (k : ℕ) :
    littlewoodPaleyBlock ℂ φ k (𝓕⁻ (delta ξ)) = if k = 0 then 𝓕⁻ (delta ξ) else 0 := by
  rw [littlewoodPaleyBlock_fourierInv_delta]
  rcases k with _ | k
  · rw [φ.inhomogeneousLittlewoodPaley_zero, φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 h)]
    simp
  · rw [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le
      (h.trans (le_mul_of_one_le_left φ.rIn_pos.le (one_le_pow₀ one_le_two)))]
    simp

/-- **The derivatives of a plane wave.** Differentiating the plane wave `𝓕⁻ δ_ξ` in the direction
`m` multiplies it by `2πi ⟪ξ, m⟫`. -/
@[simp]
theorem lineDerivOp_fourierInv_delta (m ξ : E) :
    ∂_{m} (𝓕⁻ (delta ξ)) = (2 * π * Complex.I * ⟪ξ, m⟫) • 𝓕⁻ (delta ξ) := by
  have hg : (fun x : E ↦ ((⟪x, m⟫ : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [lineDerivOp_fourierInv_eq, smulLeftCLM_delta hg, smul_smul,
    FourierTransform.fourierInv_smul]

end TemperedDistribution

namespace TauCeti

open TemperedDistribution

/-- The plane wave `x ↦ 𝐞 ⟪x, ξ⟫`, as an element of `L^∞`, is the tempered distribution
`𝓕⁻ δ_ξ`. -/
theorem toTemperedDistribution_toLp_fourierChar_inner (ξ : E) :
    (((memLp_top_fourierChar_inner ξ).toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E, ℂ)) =
      𝓕⁻ (delta ξ) := by
  rw [MemLp.toTemperedDistribution_toLp _ (hasTemperateGrowth_fourierChar_inner ξ),
    fourierInv_delta]

/-- **The constant of Bernstein's inequality is at least `2π`.** Suppose that `C` is a constant in
Bernstein's inequality for one derivative in `L^∞` at a radius `R > 0`: every `f ∈ L^∞` whose
Fourier transform vanishes outside the closed ball of radius `R` has `∂_m f ∈ L^∞` with
`‖∂_m f‖_∞ ≤ C R ‖m‖ ‖f‖_∞`, as `TauCeti.exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`
provides. Then `2π ≤ C`: a plane wave `e_ξ` with `‖ξ‖ = R` has `∂_ξ e_ξ = 2πi R² e_ξ`. -/
theorem two_mul_pi_le_of_forall_lineDerivOp_eq_and_norm_le [Nontrivial E] {C R : ℝ} (hR : 0 < R)
    (hC : ∀ f : Lp ℂ ∞ (volume : Measure E),
      Distribution.IsVanishingOn (𝓕 (f : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ)) (closedBall 0 R)ᶜ → ∀ m : E,
      ∃ g : Lp ℂ ∞ (volume : Measure E), ∂_{m} (f : 𝓢'(E, ℂ)) = g ∧
        ‖g‖ ≤ C * R * ‖m‖ * ‖f‖) :
    2 * π ≤ C := by
  obtain ⟨ξ, hξ⟩ := exists_norm_eq E hR.le
  set f : Lp ℂ ∞ (volume : Measure E) := (memLp_top_fourierChar_inner ξ).toLp _
  have hf : (f : 𝓢'(E, ℂ)) = 𝓕⁻ (delta ξ) := toTemperedDistribution_toLp_fourierChar_inner ξ
  have hvan : Distribution.IsVanishingOn (𝓕 (f : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ)) (closedBall 0 R)ᶜ := by
    rw [hf, FourierTransform.fourier_fourierInv_eq]
    exact (isVanishingOn_delta ξ).mono <| Set.compl_subset_compl.2 <|
      Set.singleton_subset_iff.2 (by rw [mem_closedBall_zero_iff, hξ])
  obtain ⟨g, hg, hgC⟩ := hC f hvan ξ
  have hge : g = (2 * π * Complex.I * (R ^ 2 : ℝ)) • f := Lp.toTemperedDistribution_injective <| by
    dsimp only
    rw [← hg, Lp.toTemperedDistribution_smul, hf, lineDerivOp_fourierInv_delta,
      real_inner_self_eq_norm_sq, hξ]
  have hn : ‖2 * π * Complex.I * ((R ^ 2 : ℝ) : ℂ)‖ = 2 * π * R ^ 2 := by
    simp [abs_of_pos Real.pi_pos]
  rw [hge, norm_smul, norm_toLp_fourierChar_inner, hξ, hn] at hgC
  nlinarith [mul_pos hR hR]

end TauCeti
