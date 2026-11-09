/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
public import TauCeti.Analysis.Distribution.TemperedDistribution.ELpNorm
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# The inhomogeneous Littlewood–Paley decomposition of a tempered distribution

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and
let `ψ₀ = φ`, `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` (`j ≥ 1`) be the inhomogeneous Littlewood–Paley
partition built from it (`ContDiffBump.inhomogeneousLittlewoodPaley`). The **Littlewood–Paley
blocks** of a tempered distribution `u` are the Fourier multipliers

`Δⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)`,

so that `Δ₀ u` carries the frequencies of `u` in the ball of radius `φ.rOut` and `Δⱼ u` those in
the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`. Their partial sums are the low-pass truncations
`∑_{j ≤ N} Δⱼ u = 𝓕⁻ (φ (2^{-N} ·) • 𝓕 u)`, and these converge to `u`: every tempered
distribution is reconstructed from its Littlewood–Paley blocks, `u = ∑ⱼ Δⱼ u` in `𝓢'(E, F)`. This
is deduced, by duality, from the convergence of the truncations `φ (2^{-N} ·) • f → f` of Schwartz
functions (`SchwartzMap.tendsto_smulLeftCLM_contDiffBump_two_pow`).

The blocks are almost orthogonal: there is `L`, depending only on `φ`, with `Δⱼ Δₖ = 0` whenever
`|j - k| ≥ L`. The same holds between the blocks `Δⱼ` and `Δ'ₖ` built from two bump functions `φ`
and `φ'`, so that, applying `Δ'ⱼ` to `u = ∑ₖ Δₖ u`, every block `Δ'ⱼ u` is the sum of the
`Δ'ⱼ Δₖ u` over the `k` with `|j - k| < L`. Being Fourier multipliers, the blocks commute with
every Fourier multiplier of temperate growth, in particular with the Bessel potentials `J^s` of
Mathlib's Bessel-potential spaces.

The blocks are bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`: there is `C`, depending only
on `φ`, with `‖Δⱼ f‖_p ≤ C ‖f‖_p` for every `f ∈ Lᵖ`; in terms of the extended `Lᵖ` norm of
tempered distributions, `‖Δⱼ u‖_p ≤ C ‖u‖_p` for every `u`. The kernel `𝓕⁻ ψⱼ` of `Δⱼ` is a Schwartz
function, and for `j ≥ 1` it is the `L¹`-normalised dilate `2^{(j-1)n} 𝓕⁻ ψ₁ (2^{j-1} ·)` of the
first dyadic kernel, since `ψ_{j+1} = ψ₁ (2^{-j} ·)`; so all the kernels have `L¹` norm at most
`max ‖𝓕⁻ ψ₀‖₁ ‖𝓕⁻ ψ₁‖₁`, and Young's inequality bounds the blocks.

This decomposition underlies the dyadic description of Besov spaces and of the Bessel-potential
spaces `H^{s,p}`: the Besov norm of `u` is a weighted sequence norm of the `Lᵖ` norms of the
blocks `Δⱼ u`.

## Main declarations

* `TemperedDistribution.littlewoodPaleyBlock`: the Littlewood–Paley block `Δⱼ`.
* `TemperedDistribution.sum_littlewoodPaleyBlock_range`: the partial sums are the low-pass
  truncations by `φ (2^{-N} ·)`.
* `TemperedDistribution.tendsto_sum_littlewoodPaleyBlock`: `u = ∑ⱼ Δⱼ u` in `𝓢'(E, F)`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_compL_eq_zero`: almost orthogonality, also
  between the blocks of the decompositions built from two different bump functions.
* `TemperedDistribution.littlewoodPaleyBlock_besselPotential_comm`: the blocks commute with the
  Bessel potentials.
* `ContDiffBump.integral_norm_fourierInv_inhomogeneousLittlewoodPaley_succ`: the dyadic kernels
  `𝓕⁻ ψⱼ`, `j ≥ 1`, all have the same `L¹` norm.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`: the blocks are bounded on
  `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`.
* `TemperedDistribution.exists_eLpNorm_littlewoodPaleyBlock_le`: the same bound for the extended
  `Lᵖ` norm of an arbitrary tempered distribution.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico`: each block of a second
  decomposition is a sum of boundedly many blocks of the first one.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.2.
-/

public section

open Filter Topology
open FourierTransform
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace ContDiffBump

variable (φ : ContDiffBump (0 : E))

/-- **The dyadic kernels are `L¹`-dilates of one another.** Since `ψ_{j+1} = ψ₁ (2^{-j} ·)`, the
kernel `𝓕⁻ ψ_{j+1}` is `2^{jn} 𝓕⁻ ψ₁ (2^j ·)` in dimension `n`, so it has the same `L¹` norm as
`𝓕⁻ ψ₁`. -/
theorem integral_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (j : ℕ) :
    ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) x‖ =
      ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) x‖ := by
  simp_rw [φ.inhomogeneousLittlewoodPaley_succ_apply_eq_one_apply j]
  exact TauCeti.integral_norm_fourierInv_comp_smul
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) (inv_ne_zero (pow_ne_zero _ two_ne_zero))

end ContDiffBump

namespace TemperedDistribution

variable (F) in
/-- The **Littlewood–Paley block** `Δⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)` of a tempered distribution, the Fourier
multiplier by the `j`-th piece `ψⱼ` of the inhomogeneous Littlewood–Paley partition built from
`φ`. -/
noncomputable def littlewoodPaleyBlock (φ : ContDiffBump (0 : E)) (j : ℕ) :
    𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)

variable (φ : ContDiffBump (0 : E))

/-- Unfolding `TemperedDistribution.littlewoodPaleyBlock`. -/
theorem littlewoodPaleyBlock_eq_fourierMultiplierCLM (j : ℕ) :
    littlewoodPaleyBlock F φ j =
      fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) :=
  (rfl)

/-- Unfolding `TemperedDistribution.littlewoodPaleyBlock` on a tempered distribution. -/
theorem littlewoodPaleyBlock_apply (j : ℕ) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j u =
      fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) u :=
  (rfl)

/-- The partial sums of the Littlewood–Paley blocks are the low-pass truncations:
`∑_{j ≤ N} Δⱼ = 𝓕⁻ (φ (2^{-N} ·) • 𝓕 ·)`. -/
theorem sum_littlewoodPaleyBlock_range (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ j =
      fourierMultiplierCLM F fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ) := by
  simp_rw [littlewoodPaleyBlock_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_sum F
    fun j _ ↦ φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j]
  simp_rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range]

/-- **Littlewood–Paley reconstruction.** Every tempered distribution is the limit in `𝓢'(E, F)`
of the partial sums of its Littlewood–Paley blocks: `u = ∑ⱼ Δⱼ u`. -/
theorem tendsto_sum_littlewoodPaleyBlock (u : 𝓢'(E, F)) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u) atTop (𝓝 u) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [← _root_.sum_apply, sum_littlewoodPaleyBlock_range]
  refine PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 fun f ↦ ?_
  simp only [fourierMultiplierCLM_apply_apply]
  have h := ((map_continuous u).tendsto _).comp <|
    ((fourierCLM ℂ 𝓢(E, ℂ)).continuous.tendsto _).comp
      (SchwartzMap.tendsto_smulLeftCLM_contDiffBump_two_pow φ (𝓕⁻ f))
  rwa [fourierCLM_apply, FourierTransform.fourier_fourierInv_eq] at h

/-- The composition of two Littlewood–Paley blocks, built from the bump functions `φ` and `φ'`,
is the Fourier multiplier by the product of the two pieces. -/
theorem littlewoodPaleyBlock_compL_littlewoodPaleyBlock (φ' : ContDiffBump (0 : E)) (j k : ℕ) :
    littlewoodPaleyBlock F φ j ∘L littlewoodPaleyBlock F φ' k =
      fourierMultiplierCLM F fun ξ ↦
        ((φ.inhomogeneousLittlewoodPaley j ξ * φ'.inhomogeneousLittlewoodPaley k ξ : ℝ) : ℂ) := by
  rw [littlewoodPaleyBlock_eq_fourierMultiplierCLM, littlewoodPaleyBlock_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_compL_fourierMultiplierCLM
      (φ'.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k)
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)]
  congr 1
  funext ξ
  simp [mul_comm]

/-- **Almost orthogonality of the Littlewood–Paley blocks.** For bump functions `φ` and `φ'`, there
is `L`, depending only on `φ` and `φ'`, such that `Δⱼ Δ'ₖ = Δ'ₖ Δⱼ = 0` whenever `j + L ≤ k`, where
`Δ` and `Δ'` are the blocks built from `φ` and `φ'`. Taking `φ' = φ` gives the almost
orthogonality of a single decomposition. -/
theorem exists_littlewoodPaleyBlock_compL_eq_zero (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ j k : ℕ, j + L ≤ k →
      littlewoodPaleyBlock F φ j ∘L littlewoodPaleyBlock F φ' k = 0 ∧
        littlewoodPaleyBlock F φ' k ∘L littlewoodPaleyBlock F φ j = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ'
  refine ⟨L, fun j k hjk ↦ ⟨?_, ?_⟩⟩
  · simp_rw [littlewoodPaleyBlock_compL_littlewoodPaleyBlock, hL j k hjk, Complex.ofReal_zero,
      fourierMultiplierCLM_const, zero_smul]
  · simp_rw [littlewoodPaleyBlock_compL_littlewoodPaleyBlock, mul_comm, hL j k hjk,
      Complex.ofReal_zero, fourierMultiplierCLM_const, zero_smul]

/-- **Comparison of two Littlewood–Paley decompositions.** For bump functions `φ` and `φ'`, there
is `L` such that every block `Δ'ⱼ u` built from `φ'` is the finite sum, over the blocks `Δₖ u`
built from `φ` with `|j - k| < L`, of `Δ'ⱼ Δₖ u`. -/
theorem exists_littlewoodPaleyBlock_eq_sum_Ico (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ (j : ℕ) (u : 𝓢'(E, F)), littlewoodPaleyBlock F φ' j u =
      ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
        littlewoodPaleyBlock F φ' j (littlewoodPaleyBlock F φ k u) := by
  obtain ⟨L₁, hL₁⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ' φ
  obtain ⟨L₂, hL₂⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ φ'
  refine ⟨max L₁ L₂, fun j u ↦ ?_⟩
  -- Apply `Δ'ⱼ` to the reconstruction `u = ∑ₖ Δₖ u`: only the terms with `|j - k| < L` survive.
  have h := ((littlewoodPaleyBlock F φ' j).continuous.tendsto u).comp
    (tendsto_sum_littlewoodPaleyBlock φ u)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop (j + max L₁ L₂)] with N hN
  rw [Function.comp_apply, map_sum]
  refine Finset.sum_subset (fun k hk ↦ ?_) (fun k _ hk ↦ ?_)
  · simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
    omega
  · simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
    rw [← ContinuousLinearMap.comp_apply]
    rcases hk with hk | hk
    · rw [(hL₂ k j (by omega)).2, zero_apply]
    · rw [(hL₁ j k (by omega)).1, zero_apply]

/-- The Littlewood–Paley blocks commute with every Fourier multiplier of temperate growth. -/
theorem littlewoodPaleyBlock_fourierMultiplierCLM_comm {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (j : ℕ) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (fourierMultiplierCLM F g u) =
      fourierMultiplierCLM F g (littlewoodPaleyBlock F φ j u) := by
  rw [littlewoodPaleyBlock_apply, littlewoodPaleyBlock_apply,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hg
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j),
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) hg, mul_comm]

/-- The Littlewood–Paley blocks commute with each other. -/
theorem littlewoodPaleyBlock_comm (j k : ℕ) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (littlewoodPaleyBlock F φ k u) =
      littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) := by
  simp only [littlewoodPaleyBlock_apply φ k]
  exact littlewoodPaleyBlock_fourierMultiplierCLM_comm φ
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k) j u

/-- The Littlewood–Paley blocks commute with the Bessel potentials `J^s`. -/
theorem littlewoodPaleyBlock_besselPotential_comm (s : ℝ) (j : ℕ) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (besselPotential E F s u) =
      besselPotential E F s (littlewoodPaleyBlock F φ j u) := by
  simp only [besselPotential]
  exact littlewoodPaleyBlock_fourierMultiplierCLM_comm φ (by fun_prop) j u

/-- On a Schwartz function, the Littlewood–Paley block is the Schwartz Fourier multiplier
by `ψⱼ`. -/
theorem littlewoodPaleyBlock_toTemperedDistributionCLM_eq [CompleteSpace F] (j : ℕ)
    (f : 𝓢(E, F)) :
    littlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) =
      (SchwartzMap.fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f :
        𝓢'(E, F)) := by
  rw [littlewoodPaleyBlock_apply]
  exact fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) f

section Lp

open MeasureTheory
open scoped ENNReal NNReal

/-- **The Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in `j`.** There is `C`, depending
only on `φ`, such that for every `1 ≤ p ≤ ∞`, every `j` and every `f ∈ Lᵖ`, the block `Δⱼ f` is a
function in `Lᵖ` with `‖Δⱼ f‖_p ≤ C ‖f‖_p`. -/
theorem exists_littlewoodPaleyBlock_eq_and_norm_le [CompleteSpace F] :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  set K : ℕ → ℝ := fun j ↦ ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖
  refine ⟨max (K 0) (K 1), fun {p} _ j f ↦ ?_⟩
  -- The kernel of `Δ₀` is `𝓕⁻ φ`; every later kernel has the `L¹` norm of `𝓕⁻ ψ₁`.
  have hK : K j ≤ max (K 0) (K 1) := by
    rcases j with _ | j
    · exact le_max_left _ _
    · exact (φ.integral_norm_fourierInv_inhomogeneousLittlewoodPaley_succ j).le.trans
        (le_max_right _ _)
  -- The symbol `ψⱼ` is smooth and compactly supported, hence a Schwartz function.
  have hσ := (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).comp_left Complex.ofReal_zero
  set σ : 𝓢(E, ℂ) :=
    hσ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (φ.contDiff_inhomogeneousLittlewoodPaley j))
  have hσ_coe : (σ : E → ℂ) = fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ f
  rw [hσ_coe] at hg hgf
  exact ⟨g, hg, hgf.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg f))⟩

/-- **The Littlewood–Paley blocks are bounded in the extended `Lᵖ` norm, uniformly in `j`.** There
is `C`, depending only on `φ`, such that `‖Δⱼ u‖_p ≤ C ‖u‖_p` for every `1 ≤ p ≤ ∞`, every `j` and
every tempered distribution `u`, where `‖·‖_p` is the extended `Lᵖ` norm
`TemperedDistribution.eLpNorm`. -/
theorem exists_eLpNorm_littlewoodPaleyBlock_le [CompleteSpace F] :
    ∃ C : ℝ≥0, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (u : 𝓢'(E, F)),
      (littlewoodPaleyBlock F φ j u).eLpNorm p ≤ C * u.eLpNorm p := by
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set C' : ℝ≥0 := ⟨max C 1, le_max_of_le_right zero_le_one⟩
  have hC' : (C' : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (NNReal.coe_pos.1 (lt_max_of_lt_right one_pos)).ne'
  refine ⟨C', fun {p} _ j u ↦ ?_⟩
  by_cases hu : u.eLpNorm p = ∞
  · rw [hu, ENNReal.mul_top hC']
    exact le_top
  obtain ⟨f, rfl⟩ := eLpNorm_lt_top_iff.1 (lt_top_iff_ne_top.2 hu)
  obtain ⟨g, hg, hgf⟩ := hC j f
  rw [hg, eLpNorm_coe, eLpNorm_coe, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C'.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (hgf.trans (by gcongr; exact le_max_left C 1))

end Lp

end TemperedDistribution
