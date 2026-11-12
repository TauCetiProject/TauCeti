/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
import TauCeti.Analysis.Convolution.Commutator
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
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
`|j - k| ≥ L`. The same holds between the blocks `Δⱼ` and `Δ'ₖ` built from two bump functions
`φ` and `φ'`, and so, applying `Δ'ⱼ` to the reconstruction of `u`, each block of `φ'` is a sum of
boundedly many blocks of `φ` composed with it: `Δ'ⱼ u = ∑_{j - L ≤ k < j + L} Δ'ⱼ Δₖ u`. This
is how a dyadic description of a function space is shown not to depend on the bump function.
Being Fourier multipliers, the blocks commute with every Fourier multiplier of temperate growth,
in particular with the Bessel potentials `J^s` of Mathlib's Bessel-potential spaces.

The blocks are bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`: there is `C`, depending only
on `φ`, with `‖Δⱼ f‖_p ≤ C ‖f‖_p` for every `f ∈ Lᵖ`. The kernel `𝓕⁻ ψⱼ` of `Δⱼ` is a Schwartz
function, and for `j ≥ 1` it is the `L¹`-normalised dilate `2^{(j-1)n} 𝓕⁻ ψ₁ (2^{j-1} ·)` of the
first dyadic kernel, since `ψ_{j+1} = ψ₁ (2^{-j} ·)`; so all the kernels have `L¹` norm at most
`max ‖𝓕⁻ ψ₀‖₁ ‖𝓕⁻ ψ₁‖₁`, and Young's inequality bounds the blocks.

The same dilation makes the first moment `∫ ‖x‖ ‖𝓕⁻ ψⱼ x‖` of the kernel `O(2^{-j})`: the kernel
lives at the spatial scale `2^{-j}`. Hence the commutator of `Δⱼ` with multiplication by a
`K`-Lipschitz function `f` gains one derivative,
`‖Δⱼ (f • g) - f • Δⱼ g‖_p ≤ C 2^{-j} K ‖g‖_p` for `1 ≤ p ≤ ∞`, with `C` depending only on `φ`:
the commutator gains the factor `2^{-j}` over the uniform bound `‖Δⱼ g‖_p ≤ C ‖g‖_p`, and the
estimate involves only the Lipschitz constant of `f`, not its size. This is the commutator
estimate used for paraproducts and transport equations (Bahouri–Chemin–Danchin, Lemma 2.97).

This decomposition underlies the dyadic description of Besov spaces and of the Bessel-potential
spaces `H^{s,p}`: the Besov norm of `u` is a weighted sequence norm of the `Lᵖ` norms of the
blocks `Δⱼ u`.

## Main declarations

* `TemperedDistribution.littlewoodPaleyBlock`: the Littlewood–Paley block `Δⱼ`.
* `TemperedDistribution.sum_littlewoodPaleyBlock_range`: the partial sums are the low-pass
  truncations by `φ (2^{-N} ·)`.
* `TemperedDistribution.tendsto_sum_littlewoodPaleyBlock`: `u = ∑ⱼ Δⱼ u` in `𝓢'(E, F)`; in
  particular `u` is determined by its blocks (`eq_of_forall_littlewoodPaleyBlock_eq`).
* `TemperedDistribution.isVanishingOn_fourier_littlewoodPaleyBlock`: the Fourier transform of
  `Δⱼ u` vanishes outside the ball of radius `2^j φ.rOut`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_compL_eq_zero`: almost orthogonality, also
  between the blocks of two bump functions.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico`: each block of one bump function
  is a sum of boundedly many blocks of another, composed with it.
* `TemperedDistribution.littlewoodPaleyBlock_besselPotential_comm`: the blocks commute with the
  Bessel potentials.
* `TemperedDistribution.littlewoodPaleyBlock_toTemperedDistributionCLM_eq_ite`: a Schwartz function
  whose Fourier transform is carried by the region where `ψⱼ = 1` is its own `j`-th block and has
  no other block.
* `ContDiffBump.integral_norm_fourierInv_inhomogeneousLittlewoodPaley_succ`: the dyadic kernels
  `𝓕⁻ ψⱼ`, `j ≥ 1`, all have the same `L¹` norm.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`: the blocks are bounded on
  `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`.
* `TemperedDistribution.ae_eq_convolution_of_littlewoodPaleyBlock_eq`: on `Lᵖ`, the block `Δⱼ` is
  convolution with `𝓕⁻ ψⱼ`.
* `ContDiffBump.integral_norm_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ` and
  `ContDiffBump.exists_integral_norm_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le`: the
  first moments of the kernels `𝓕⁻ ψⱼ` are `O(2^{-j})`.
* `TemperedDistribution.exists_eLpNorm_littlewoodPaleyBlock_smul_sub_smul_le`: the commutator of
  `Δⱼ` with a Lipschitz function is `O(2^{-j})` on `Lᵖ`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le_of_le`: Bernstein's inequality
  `‖Δⱼ u‖_r ≤ C 2^{j n (1/p - 1/r)} ‖Δⱼ u‖_p` for `p ≤ r`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.2 and Lemma 2.97 (the commutator estimate).
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

/-- **The first moments of the dyadic kernels decay like `2^{-j}`.** Since `𝓕⁻ ψ_{j+1}` is the
`L¹`-normalised dilate `2^{jn} 𝓕⁻ ψ₁ (2^j ·)`, its first moment `∫ ‖x‖ ‖𝓕⁻ ψ_{j+1} x‖` is `2^{-j}`
times that of `𝓕⁻ ψ₁`. -/
theorem integral_norm_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (j : ℕ) :
    ∫ x, ‖x‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) x‖ =
      (2 ^ j)⁻¹ * ∫ x, ‖x‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) x‖ := by
  simp_rw [φ.inhomogeneousLittlewoodPaley_succ_apply_eq_one_apply j]
  rw [TauCeti.integral_norm_mul_norm_fourierInv_comp_smul
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) (inv_ne_zero (pow_ne_zero _ two_ne_zero)),
    abs_of_pos (by positivity)]

open scoped NNReal in
/-- **The first moments of the kernels `𝓕⁻ ψⱼ` are `O(2^{-j})`.** There is `C`, depending only on
`φ`, with `∫ ‖x‖ ‖𝓕⁻ ψⱼ x‖ ≤ 2^{-j} C` for every `j`. -/
theorem exists_integral_norm_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le :
    ∃ C : ℝ≥0, ∀ j : ℕ,
      ∫ x, ‖x‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖ ≤ (2 ^ j)⁻¹ * C := by
  set M : ℕ → ℝ := fun j ↦ ∫ x, ‖x‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖
  have hM0 : 0 ≤ M 0 := MeasureTheory.integral_nonneg fun x ↦ by positivity
  refine ⟨⟨max (M 0) (2 * M 1), hM0.trans (le_max_left _ _)⟩, fun j ↦ ?_⟩
  rcases j with _ | j
  · rw [pow_zero, inv_one, one_mul]
    exact le_max_left _ _
  · calc M (j + 1) = (2 ^ (j + 1))⁻¹ * (2 * M 1) := by
          simp only [M, φ.integral_norm_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ j,
            pow_succ, mul_inv]
          ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

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

/-- A tempered distribution is determined by its Littlewood–Paley blocks. -/
theorem eq_of_forall_littlewoodPaleyBlock_eq {u v : 𝓢'(E, F)}
    (h : ∀ j, littlewoodPaleyBlock F φ j u = littlewoodPaleyBlock F φ j v) : u = v :=
  tendsto_nhds_unique (tendsto_sum_littlewoodPaleyBlock φ u) <| by
    simpa only [h] using tendsto_sum_littlewoodPaleyBlock φ v

open Distribution in
/-- **The spectrum of a block.** The Fourier transform of `Δⱼ u` vanishes outside the closed ball
of radius `2^j φ.rOut`, which carries the piece `ψⱼ`. -/
theorem isVanishingOn_fourier_littlewoodPaleyBlock (j : ℕ) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (littlewoodPaleyBlock F φ j u) : 𝓢'(E, F))
      (Metric.closedBall 0 (2 ^ j * φ.rOut))ᶜ := by
  rw [littlewoodPaleyBlock_apply]
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ ?_) u
  rw [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm
    (not_le.1 (mt mem_closedBall_zero_iff.2 hξ)).le, Complex.ofReal_zero]

/-- The composition of the Littlewood–Paley blocks of two bump functions is the Fourier
multiplier by the product of the two pieces. -/
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

/-- **Almost orthogonality of the Littlewood–Paley blocks.** For two bump functions `φ` and `φ'`,
there is `L` such that `Δⱼ Δ'ₖ = Δ'ₖ Δⱼ = 0` whenever `j + L ≤ k`, where `Δ` and `Δ'` are the
blocks built from `φ` and `φ'`. For `φ' = φ` this is the almost orthogonality of the blocks of a
single partition. -/
theorem exists_littlewoodPaleyBlock_compL_eq_zero (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ j k : ℕ, j + L ≤ k →
      littlewoodPaleyBlock F φ j ∘L littlewoodPaleyBlock F φ' k = 0 ∧
        littlewoodPaleyBlock F φ' k ∘L littlewoodPaleyBlock F φ j = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ'
  refine ⟨L, fun j k hjk ↦ ⟨?_, ?_⟩⟩
  · simp_rw [littlewoodPaleyBlock_compL_littlewoodPaleyBlock, hL j k hjk, Complex.ofReal_zero,
      fourierMultiplierCLM_const, zero_smul]
  · simp_rw [littlewoodPaleyBlock_compL_littlewoodPaleyBlock,
      mul_comm _ (φ.inhomogeneousLittlewoodPaley j _), hL j k hjk, Complex.ofReal_zero,
      fourierMultiplierCLM_const, zero_smul]

/-- **Change of bump function.** The blocks `Δⱼ` and `Δ'ₖ` built from two bump functions `φ` and
`φ'` interact only at nearby indices: there is `L`, depending only on `φ` and `φ'`, such that
`Δ'ⱼ u = ∑_{j - L ≤ k < j + L} Δ'ⱼ Δₖ u` for every `j` and every tempered distribution `u`. -/
theorem exists_littlewoodPaleyBlock_eq_sum_Ico (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ (j : ℕ) (u : 𝓢'(E, F)), littlewoodPaleyBlock F φ' j u =
      ∑ k ∈ Finset.Ico (j - L) (j + L),
        littlewoodPaleyBlock F φ' j (littlewoodPaleyBlock F φ k u) := by
  obtain ⟨L₁, hL₁⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ φ'
  obtain ⟨L₂, hL₂⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ' φ
  refine ⟨max L₁ L₂, fun j u ↦ ?_⟩
  -- Apply `Δ'ⱼ` to the reconstruction `u = ∑ₖ Δₖ u`: the partial sums are eventually constant.
  have h := ((map_continuous (littlewoodPaleyBlock F φ' j)).tendsto u).comp
    (tendsto_sum_littlewoodPaleyBlock φ u)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop (j + max L₁ L₂)] with N hN
  simp only [Function.comp_apply, map_sum]
  refine Finset.sum_subset (fun k hk ↦ Finset.mem_range.2 ((Finset.mem_Ico.1 hk).2.trans_le hN))
    fun k _ hk ↦ ?_
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
  rcases hk with hk | hk
  · exact congr($((hL₁ k j (by omega)).2) u)
  · exact congr($((hL₂ j k (by omega)).1) u)

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

/-- **A Schwartz function carried by one block.** If on the support of the Fourier transform of
a Schwartz function `f` the piece `ψⱼ` equals `1` and every other piece `ψₖ` vanishes, then
`Δⱼ f = f` and `Δₖ f = 0` for `k ≠ j`. -/
theorem littlewoodPaleyBlock_toTemperedDistributionCLM_eq_ite [CompleteSpace F] {j : ℕ}
    {f : 𝓢(E, F)}
    (hf : ∀ k ξ, 𝓕 f ξ ≠ 0 → φ.inhomogeneousLittlewoodPaley k ξ = if k = j then 1 else 0)
    (k : ℕ) :
    littlewoodPaleyBlock F φ k (f : 𝓢'(E, F)) = if k = j then (f : 𝓢'(E, F)) else 0 := by
  have h : SchwartzMap.smulLeftCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) (𝓕 f) =
      if k = j then 𝓕 f else 0 := by
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k)]
    by_cases hξ : 𝓕 f ξ = 0
    · split_ifs <;> simp [hξ]
    · rw [hf k ξ hξ]
      split_ifs <;> simp
  rw [littlewoodPaleyBlock_toTemperedDistributionCLM_eq, SchwartzMap.fourierMultiplierCLM_apply, h]
  split_ifs
  · rw [FourierTransform.fourierInv_fourier_eq]
  · simp

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

open ContinuousLinearMap in
open scoped Convolution in
/-- **The blocks of an `Lᵖ` function are convolutions.** For `1 ≤ p ≤ ∞` and `h ∈ Lᵖ`, the block
`Δⱼ h` is an `Lᵖ` function `v` (`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`),
and `v` is almost everywhere the convolution `𝓕⁻ ψⱼ ⋆ h` of `h` with the kernel of `Δⱼ`. -/
theorem ae_eq_convolution_of_littlewoodPaleyBlock_eq [CompleteSpace F] (j : ℕ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {h v : Lp F p (volume : Measure E)}
    (hv : littlewoodPaleyBlock F φ j (h : 𝓢'(E, F)) = v) :
    (v : E → F) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ⋆[lsmul ℂ ℂ] (h : E → F) := by
  have hσ := (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).comp_left Complex.ofReal_zero
  set σ : 𝓢(E, ℂ) :=
    hσ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (φ.contDiff_inhomogeneousLittlewoodPaley j))
  have hσ_coe : (σ : E → ℂ) = fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  obtain ⟨v', hv', hv'h, -⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq σ h
    (q := p) (r := 1) le_rfl (by rw [inv_one, add_comm])
  rw [littlewoodPaleyBlock_apply, ← hσ_coe, hv'] at hv
  have hvv : v' = v := LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E)) (p := p)) hv
  rw [← hvv, ← hσ_coe]
  exact hv'h

open ContinuousLinearMap in
open scoped Convolution in
/-- **The commutator of a Littlewood–Paley block with a Lipschitz function gains one
derivative.** There is `C`, depending only on `φ`, with the following property. Let `1 ≤ p ≤ ∞`,
let `f : E → ℂ` be `K`-Lipschitz, and let `g ∈ Lᵖ` be such that `f • g` is in `Lᵖ` too, represented
by `fg`. If `u` and `w` are the `Lᵖ` functions `Δⱼ g` and `Δⱼ (f • g)`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`), then the commutator satisfies

`‖Δⱼ (f • g) - f • Δⱼ g‖_p ≤ C 2^{-j} K ‖g‖_p`.

Compared with the uniform bound `‖Δⱼ g‖_p ≤ C ‖g‖_p`, the commutator gains the factor `2^{-j}`,
one derivative at the frequency scale `2^j` of the block. The bound does not involve the size of
`f`, which may be unbounded, only its Lipschitz constant. -/
theorem exists_eLpNorm_littlewoodPaleyBlock_smul_sub_smul_le [CompleteSpace F] :
    ∃ C : ℝ≥0, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) {f : E → ℂ} {K : ℝ≥0}, LipschitzWith K f →
      ∀ g fg u w : Lp F p (volume : Measure E), fg =ᵐ[volume] (fun x ↦ f x • g x) →
        littlewoodPaleyBlock F φ j (g : 𝓢'(E, F)) = u →
        littlewoodPaleyBlock F φ j (fg : 𝓢'(E, F)) = w →
        eLpNorm (fun x ↦ w x - f x • u x) p volume ≤
          C * (2 ^ j)⁻¹ * K * eLpNorm g p volume := by
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le
  refine ⟨C, fun {p} _ j f K hf g fg u w hfg hu hw ↦ ?_⟩
  -- The kernel `κ = 𝓕⁻ ψⱼ` of `Δⱼ` is a Schwartz function.
  have hσ := (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).comp_left Complex.ofReal_zero
  set κ : 𝓢(E, ℂ) := 𝓕⁻ (hσ.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff_inhomogeneousLittlewoodPaley j)))
  have hκ : (κ : E → ℂ) = 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
    rw [SchwartzMap.fourierInv_coe]
    exact congrArg _ (funext (HasCompactSupport.toSchwartzMap_toFun _ _))
  -- Both convolutions with `κ` exist everywhere, by Hölder's inequality, so the commutator is
  -- the integral of `MeasureTheory.eLpNorm_integral_sub_smul_smul_le`.
  have : ((1 - p⁻¹)⁻¹).HolderConjugate p :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' (Fact.out : 1 ≤ p)).symm
  have hex {h : E → F} (hh : MemLp h p volume) (x : E) :
      ConvolutionExistsAt (κ : E → ℂ) h x (lsmul ℂ ℂ) volume :=
    ConvolutionExists.of_memLp_memLp _ (κ.memLp (1 - p⁻¹)⁻¹) hh x
  have hae : (fun x ↦ w x - f x • u x) =ᵐ[volume]
      fun x ↦ ∫ t, (f (x - t) - f x) • κ t • g (x - t) := by
    filter_upwards [ae_eq_convolution_of_littlewoodPaleyBlock_eq φ j hu,
      ae_eq_convolution_of_littlewoodPaleyBlock_eq φ j hw] with x hux hwx
    rw [hux, hwx, ← hκ, convolution_congr (lsmul ℂ ℂ) (Filter.EventuallyEq.refl _ _) hfg,
      convolution_smul_sub_smul_convolution (hex ((Lp.memLp fg).ae_eq hfg) x)
        (hex (Lp.memLp g) x)]
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_integral_sub_smul_smul_le hf κ.continuous.aestronglyMeasurable
    (Lp.aestronglyMeasurable g) (Fact.out : 1 ≤ p)).trans ?_
  -- The first moment of `κ` is at most `2^{-j} C`.
  have hmoment : ∫⁻ t, ‖t‖ₑ * ‖κ t‖ₑ ≤ (2 ^ j)⁻¹ * C := by
    have hint : Integrable (fun x ↦ ‖x‖ * ‖κ x‖) volume := by
      simpa only [pow_one] using κ.integrable_pow_mul volume 1
    calc ∫⁻ t, ‖t‖ₑ * ‖κ t‖ₑ = ENNReal.ofReal (∫ x, ‖x‖ * ‖κ x‖) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x ↦ by positivity)]
          simp only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      _ ≤ ENNReal.ofReal ((2 ^ j)⁻¹ * C) := ENNReal.ofReal_le_ofReal (hκ ▸ hC j)
      _ = (2 ^ j)⁻¹ * C := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
            ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  calc (K : ℝ≥0∞) * (∫⁻ t, ‖t‖ₑ * ‖κ t‖ₑ) * eLpNorm g p volume
      ≤ K * ((2 ^ j)⁻¹ * C) * eLpNorm g p volume := by gcongr
    _ = C * (2 ^ j)⁻¹ * K * eLpNorm g p volume := by ring

/-- **Bernstein's inequality for the Littlewood–Paley blocks.** For `1 ≤ p ≤ r ≤ ∞` there is `C`,
depending only on `E`, `F`, `p`, `r` and `φ`, with the following property. If the block `Δⱼ u` of
a tempered distribution is an `Lᵖ` function `f`, then it is also an `Lʳ` function `g`, with

`‖g‖_r ≤ C 2^{j n (1/p - 1/r)} ‖f‖_p`,

where `n` is the dimension of `E` and `1/∞ = 0`. The Fourier transform of the block is carried by
the ball of radius `2^j φ.rOut`, so this is Bernstein's inequality at that radius. -/
theorem exists_littlewoodPaleyBlock_eq_and_norm_le_of_le [CompleteSpace F] {p r : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hpr : p ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E)),
      littlewoodPaleyBlock F φ j u = f → ∃ g : Lp F r (volume : Measure E),
        littlewoodPaleyBlock F φ j u = g ∧
          ‖g‖ ≤ C * 2 ^ (Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹) * j) * ‖f‖ := by
  obtain ⟨C, hC, hB⟩ :=
    TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F) hpr
  set a : ℝ := Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)
  refine ⟨C * φ.rOut ^ a, mul_nonneg hC (Real.rpow_nonneg φ.rOut_pos.le a), fun j u f hf ↦ ?_⟩
  -- Bernstein's inequality without derivatives, at the radius `2^j φ.rOut` carrying `Δⱼ u`.
  obtain ⟨g, hg, hgf⟩ := hB (mul_pos (pow_pos two_pos j) φ.rOut_pos) f
    (hf ▸ isVanishingOn_fourier_littlewoodPaleyBlock φ j u)
  refine ⟨g, hf.trans hg, hgf.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) φ.rOut_pos.le, ← Real.rpow_natCast,
    ← Real.rpow_mul zero_le_two, mul_comm (j : ℝ) a]
  ring

end Lp

end TemperedDistribution
