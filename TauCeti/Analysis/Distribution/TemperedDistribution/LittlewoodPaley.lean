/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
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
Blocks far from the spectrum of `u` vanish: if `𝓕 u` vanishes outside the closed ball of radius
`2^j R`, then `Δₖ u = 0` for `k ≥ j + L`, and if it vanishes on the open ball of radius
`2^j a`, `a > 0`, then `Δₖ u = 0` for `k + L ≤ j`, with `L` depending only on `φ` and `R`,
respectively `a`. So a distribution whose spectrum lies in the dyadic annulus
`2^j a ≤ ‖ξ‖ ≤ 2^j R` is the sum of its boundedly many blocks of index near `j`. Being Fourier
multipliers, the blocks commute with every Fourier multiplier of temperate growth, in particular
with the Bessel potentials `J^s` of Mathlib's Bessel-potential spaces.

The blocks are bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`: there is `C`, depending only
on `φ`, with `‖Δⱼ f‖_p ≤ C ‖f‖_p` for every `f ∈ Lᵖ`. The kernel `𝓕⁻ ψⱼ` of `Δⱼ` is a Schwartz
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
* `TemperedDistribution.tendsto_sum_littlewoodPaleyBlock`: `u = ∑ⱼ Δⱼ u` in `𝓢'(E, F)`; in
  particular `u` is determined by its blocks (`eq_of_forall_littlewoodPaleyBlock_eq`).
* `TemperedDistribution.isVanishingOn_fourier_littlewoodPaleyBlock`: the Fourier transform of
  `Δⱼ u` vanishes outside the ball of radius `2^j φ.rOut`, and for `j ≥ 1` also inside the ball of
  radius `2^{j-1} φ.rIn` (`isVanishingOn_fourier_littlewoodPaleyBlock_succ`); the Fourier transform
  of a sum of blocks of index at most `n` vanishes outside the ball of radius `2^n φ.rOut`
  (`isVanishingOn_fourier_sum_littlewoodPaleyBlock`).
* `TemperedDistribution.littlewoodPaleyBlock_lineDerivOp`,
  `TemperedDistribution.littlewoodPaleyBlock_iteratedLineDerivOp`: the blocks commute with
  derivatives.
* `TemperedDistribution.littlewoodPaleyBlock_eq_zero_of_isVanishingOn`,
  `TemperedDistribution.exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_closedBall`,
  `TemperedDistribution.exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_ball`,
  `TemperedDistribution.exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_annulus`: the blocks
  away from the spectrum vanish, and `TemperedDistribution.sum_littlewoodPaleyBlock_eq_self`: a
  distribution with finitely many nonzero blocks is their sum.
* `TemperedDistribution.littlewoodPaleyBlock_eq_sum_Ico_of_hasSum`: the block `Δₖ` of a series
  whose terms have `Δₖ uⱼ = 0` unless `k - L ≤ j < k + L` is the finite sum over that window.
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
  `𝓕⁻ ψⱼ`, `j ≥ 1`, all have the same `L¹` norm, and
  `ContDiffBump.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_succ`: their `Lʳ` norms grow like
  `2^{j n (1 - 1/r)}`; `ContDiffBump.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_ne_zero`:
  each kernel `𝓕⁻ ψⱼ` is nonzero in every `Lʳ`.
* `TemperedDistribution.littlewoodPaleyBlock_delta_zero`: the blocks of the Dirac mass `δ₀` are
  the kernels `𝓕⁻ ψⱼ`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`: the blocks are bounded on
  `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le_of_le`: Bernstein's inequality
  `‖Δⱼ u‖_r ≤ C 2^{j n (1/p - 1/r)} ‖Δⱼ u‖_p` for `p ≤ r`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.2.
-/

public section

open Filter Topology
open FourierTransform
open scoped SchwartzMap LineDeriv

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

open MeasureTheory in
/-- **The `Lʳ` norms of the dyadic kernels.** Since `𝓕⁻ ψ_{j+1} = 2^{jn} 𝓕⁻ ψ₁ (2^j ·)` in
dimension `n`, the `Lʳ` norm of `𝓕⁻ ψ_{j+1}` is `(2^j)^{n - n/r}` times that of `𝓕⁻ ψ₁`, where
`1/∞ = 0`. -/
theorem eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_succ (j : ℕ) (r : ENNReal) :
    eLpNorm (𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) r volume =
      ENNReal.ofReal
          ((2 ^ j : ℝ) ^ ((Module.finrank ℝ E : ℝ) - Module.finrank ℝ E / r.toReal)) *
        eLpNorm (𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) r volume := by
  simp_rw [φ.inhomogeneousLittlewoodPaley_succ_apply_eq_one_apply j]
  exact TauCeti.eLpNorm_fourierInv_comp_inv_smul
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) (pow_pos two_pos j) r

open MeasureTheory in
/-- **The kernels are nonzero.** On a nontrivial space, each `𝓕⁻ ψⱼ` has nonzero `Lʳ` norm for
every `r ≠ 0`: it is continuous, so vanishing almost everywhere would force `ψⱼ = 0`. -/
theorem eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_ne_zero [Nontrivial E] (j : ℕ)
    {r : ENNReal} (hr : r ≠ 0) :
    eLpNorm (𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) r volume ≠ 0 := by
  set σ := φ.inhomogeneousLittlewoodPaleySchwartz j
  have hσ : (σ : E → ℂ) = _ := φ.coe_inhomogeneousLittlewoodPaleySchwartz j
  rw [← hσ, ← SchwartzMap.fourierInv_coe]
  intro h
  -- `𝓕⁻ σ` is continuous and vanishes almost everywhere, hence it is `0`, and so is `σ`.
  have hσ0 : σ = 0 := by
    have h0 : 𝓕⁻ σ = 0 := SchwartzMap.ext fun x ↦ congrFun
      ((Continuous.ae_eq_iff_eq volume (𝓕⁻ σ).continuous continuous_zero).1
        ((eLpNorm_eq_zero_iff hr).1 h)) x
    simpa using congrArg (fun g : 𝓢(E, ℂ) ↦ (𝓕 g : 𝓢(E, ℂ))) h0
  obtain ⟨ξ, hξ⟩ := φ.exists_inhomogeneousLittlewoodPaley_pos j
  have := congrFun hσ ξ
  rw [hσ0, zero_apply] at this
  exact hξ.ne' (Complex.ofReal_eq_zero.1 this.symm)

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

open Distribution in
/-- **The spectrum of a dyadic block.** The Fourier transform of `Δ_{j+1} u` vanishes outside the
annulus `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`, which carries the piece `ψ_{j+1}`. -/
theorem isVanishingOn_fourier_littlewoodPaleyBlock_succ (j : ℕ) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (littlewoodPaleyBlock F φ (j + 1) u) : 𝓢'(E, F))
      (Metric.closedBall 0 (2 ^ (j + 1) * φ.rOut) \ Metric.ball 0 (2 ^ j * φ.rIn))ᶜ := by
  rw [littlewoodPaleyBlock_apply]
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ ?_) u
  simp only [Set.mem_compl_iff, Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff,
    not_and_or, not_le, not_not] at hξ
  rcases hξ with hξ | hξ
  · rw [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hξ.le, Complex.ofReal_zero]
  · rw [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le hξ.le, Complex.ofReal_zero]

open Distribution in
/-- **The spectrum of a sum of blocks.** If every index in `s` is at most `n`, the Fourier
transform of `∑_{k ∈ s} Δₖ u` vanishes outside the closed ball of radius `2^n φ.rOut`. -/
theorem isVanishingOn_fourier_sum_littlewoodPaleyBlock {s : Finset ℕ} {n : ℕ}
    (hs : ∀ k ∈ s, k ≤ n) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (∑ k ∈ s, littlewoodPaleyBlock F φ k u) : 𝓢'(E, F))
      (Metric.closedBall 0 (2 ^ n * φ.rOut))ᶜ := by
  simp_rw [littlewoodPaleyBlock_apply, ← _root_.sum_apply,
    ← fourierMultiplierCLM_sum F fun k _ ↦
      φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k]
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ Finset.sum_eq_zero fun k hk ↦ ?_) u
  rw [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le] at hξ
  have hkn : (2 : ℝ) ^ k * φ.rOut ≤ 2 ^ n * φ.rOut :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (hs k hk)) φ.rOut_pos.le
  simp [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm (hkn.trans hξ.le)]

/-- The Littlewood–Paley blocks commute with directional derivatives. -/
theorem littlewoodPaleyBlock_lineDerivOp (j : ℕ) (m : E) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (∂_{m} u) = ∂_{m} (littlewoodPaleyBlock F φ j u) := by
  rw [littlewoodPaleyBlock_apply, littlewoodPaleyBlock_apply, lineDerivOp_fourierMultiplierCLM
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)]

/-- The Littlewood–Paley blocks commute with iterated directional derivatives. -/
theorem littlewoodPaleyBlock_iteratedLineDerivOp (j : ℕ) {k : ℕ} (m : Fin k → E)
    (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (∂^{m} u) = ∂^{m} (littlewoodPaleyBlock F φ j u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left,
      littlewoodPaleyBlock_lineDerivOp, ih]

/-- A tempered distribution whose blocks vanish outside a finite set of indices is the sum of
its blocks over that set. -/
theorem sum_littlewoodPaleyBlock_eq_self {u : 𝓢'(E, F)} (s : Finset ℕ)
    (hs : ∀ k ∉ s, littlewoodPaleyBlock F φ k u = 0) :
    ∑ k ∈ s, littlewoodPaleyBlock F φ k u = u := by
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) (tendsto_sum_littlewoodPaleyBlock φ u)
  filter_upwards [eventually_ge_atTop (s.sup id + 1)] with N hN
  refine Finset.sum_subset (fun k hk ↦ Finset.mem_range.2 ?_) fun k _ hk ↦ hs k hk
  exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)).trans_le hN

/-- The block `Δₖ` of a series of tempered distributions `uⱼ` with `Δₖ uⱼ = 0` unless
`k - L ≤ j < k + L` is the finite sum of the `Δₖ uⱼ` over that window. -/
theorem littlewoodPaleyBlock_eq_sum_Ico_of_hasSum {u : ℕ → 𝓢'(E, F)} {U : 𝓢'(E, F)}
    (hU : HasSum u U) {L : ℕ}
    (hL : ∀ j k, k + L ≤ j ∨ j + L ≤ k → littlewoodPaleyBlock F φ k (u j) = 0) (k : ℕ) :
    littlewoodPaleyBlock F φ k U =
      ∑ j ∈ Finset.Ico (k - L) (k + L), littlewoodPaleyBlock F φ k (u j) := by
  refine (hU.map (littlewoodPaleyBlock F φ k) (map_continuous _)).unique
    (hasSum_sum_of_ne_finset_zero fun j hj ↦ hL j k ?_)
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hj
  omega

open Distribution in
/-- **Blocks off the spectrum vanish.** If the Fourier transform of `u` vanishes on a set
containing the support of the piece `ψₖ`, then `Δₖ u = 0`. -/
theorem littlewoodPaleyBlock_eq_zero_of_isVanishingOn {u : 𝓢'(E, F)} {s : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) s) {k : ℕ}
    (hk : tsupport (φ.inhomogeneousLittlewoodPaley k) ⊆ s) : littlewoodPaleyBlock F φ k u = 0 :=
  fourierMultiplierCLM_eq_zero_of_isVanishingOn hu <|
    (tsupport_comp_subset Complex.ofReal_zero _).trans hk

open Distribution in
/-- **Blocks far above the spectrum vanish.** For every `R` there is `L`, depending only on `φ`
and `R`, such that if the Fourier transform of `u` vanishes outside the closed ball of radius
`2^j R`, then `Δₖ u = 0` for every `k ≥ j + L`. -/
theorem exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_closedBall (R : ℝ) :
    ∃ L : ℕ, ∀ (j k : ℕ) (u : 𝓢'(E, F)),
      IsVanishingOn (𝓕 u : 𝓢'(E, F)) (Metric.closedBall 0 (2 ^ j * R))ᶜ →
        j + L ≤ k → littlewoodPaleyBlock F φ k u = 0 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / φ.rIn) one_lt_two
  rw [div_lt_iff₀ φ.rIn_pos] at hN
  refine ⟨N + 1, fun j k u hu hjk ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- The piece `ψ_{k+1}` lives where `2^k φ.rIn ≤ ‖ξ‖`, beyond the radius `2^j R`.
  refine littlewoodPaleyBlock_eq_zero_of_isVanishingOn φ hu <|
    (φ.tsupport_inhomogeneousLittlewoodPaley_succ_subset k).trans fun ξ hξ ↦ ?_
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
  calc 2 ^ j * R < 2 ^ j * (2 ^ N * φ.rIn) := by gcongr
    _ = 2 ^ (j + N) * φ.rIn := by ring
    _ ≤ 2 ^ k * φ.rIn :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) φ.rIn_pos.le
    _ ≤ ‖ξ‖ := hξ.1

open Distribution in
/-- **Blocks far below the spectrum vanish.** For every `a > 0` there is `L`, depending only on
`φ` and `a`, such that if the Fourier transform of `u` vanishes on the open ball of radius
`2^j a`, then `Δₖ u = 0` for every `k` with `k + L ≤ j`. -/
theorem exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_ball {a : ℝ} (ha : 0 < a) :
    ∃ L : ℕ, ∀ (j k : ℕ) (u : 𝓢'(E, F)),
      IsVanishingOn (𝓕 u : 𝓢'(E, F)) (Metric.ball 0 (2 ^ j * a)) →
        k + L ≤ j → littlewoodPaleyBlock F φ k u = 0 := by
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (φ.rOut / a) one_lt_two
  rw [div_lt_iff₀ ha] at hL
  refine ⟨L, fun j k u hu hkj ↦ ?_⟩
  -- The piece `ψₖ` lives in the closed ball of radius `2^k φ.rOut`, inside the radius `2^j a`.
  refine littlewoodPaleyBlock_eq_zero_of_isVanishingOn φ hu <|
    (φ.tsupport_inhomogeneousLittlewoodPaley_subset_closedBall k).trans
      (Metric.closedBall_subset_ball ?_)
  calc 2 ^ k * φ.rOut < 2 ^ k * (2 ^ L * a) := by gcongr
    _ = 2 ^ (k + L) * a := by ring
    _ ≤ 2 ^ j * a := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hkj) ha.le

open Distribution in
/-- **Blocks away from a dyadic annulus vanish.** For `a > 0` and every `b` there is `L`, depending
only on `φ`, `a` and `b`, with the following property. If the Fourier transform of `u` vanishes
outside the closed ball of radius `2^j b` and, when `j > 0`, on the open ball of radius `2^j a`,
then `Δₖ u = 0` whenever `k + L ≤ j` or `j + L ≤ k`. -/
theorem exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_annulus {a : ℝ} (ha : 0 < a)
    (b : ℝ) :
    ∃ L : ℕ, ∀ (j k : ℕ) (u : 𝓢'(E, F)),
      IsVanishingOn (𝓕 u : 𝓢'(E, F)) (Metric.closedBall 0 (2 ^ j * b))ᶜ →
        (0 < j → IsVanishingOn (𝓕 u : 𝓢'(E, F)) (Metric.ball 0 (2 ^ j * a))) →
          k + L ≤ j ∨ j + L ≤ k → littlewoodPaleyBlock F φ k u = 0 := by
  obtain ⟨L₁, hL₁⟩ := exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_ball (F := F) φ ha
  obtain ⟨L₂, hL₂⟩ :=
    exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_closedBall (F := F) φ b
  refine ⟨max L₁ L₂ + 1, fun j k u hb ha hjk ↦ ?_⟩
  rcases hjk with hjk | hjk
  · exact hL₁ j k u (ha (by omega)) (by omega)
  · exact hL₂ j k u hb (by omega)

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

/-- **The blocks of the Dirac mass are the Littlewood–Paley kernels.** The block `Δⱼ δ₀` is the
Schwartz function `𝓕⁻ ψⱼ`, since the Fourier transform of `δ₀` is `1`. -/
@[simp]
theorem littlewoodPaleyBlock_delta_zero (j : ℕ) :
    littlewoodPaleyBlock ℂ φ j (delta 0) =
      (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) : 𝓢(E, ℂ)) := by
  rw [← fourierInv_toTemperedDistributionCLM_eq, littlewoodPaleyBlock_apply,
    fourierMultiplierCLM_apply, fourier_delta_zero]
  congr 1
  ext u
  simp [φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j, mul_comm]

section Lp

open MeasureTheory
open scoped ENNReal

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
  obtain ⟨g, hg, hgf⟩ :=
    exists_fourierMultiplierCLM_eq_and_norm_le (φ.inhomogeneousLittlewoodPaleySchwartz j) f
  rw [φ.coe_inhomogeneousLittlewoodPaleySchwartz j] at hg hgf
  exact ⟨g, hg, hgf.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg f))⟩

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
