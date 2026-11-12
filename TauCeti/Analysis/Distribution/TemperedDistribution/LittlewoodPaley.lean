/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
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
  `Δⱼ u` vanishes outside the ball of radius `2^j φ.rOut`, and for `j ≥ 1` outside the annulus
  `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut` (`isVanishingOn_fourier_littlewoodPaleyBlock_succ`).
* `TemperedDistribution.littlewoodPaleyLowPass`: the low-frequency truncation `Sⱼ = ∑_{k < j} Δₖ`,
  the Fourier multiplier by `φ (2^{1-j} ·)` for `j ≥ 1`, with its spectrum
  (`isVanishingOn_fourier_littlewoodPaleyLowPass_succ`), its uniform `Lᵖ` bound
  (`exists_littlewoodPaleyLowPass_eq_and_norm_le`) and its expression as an average against the
  dilates of the kernel `𝓕⁻ φ` (`ae_eq_integral_of_littlewoodPaleyLowPass_succ_eq`), whose
  integral is `1` (`ContDiffBump.integral_fourierInv`).
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
  `𝓕⁻ ψⱼ`, `j ≥ 1`, all have the same `L¹` norm.
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

/-- The bump function `φ`, as a complex Schwartz function. -/
private noncomputable def toSchwartzMap : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun ξ ↦ (φ ξ : ℂ))
    (φ.hasCompactSupport.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp φ.contDiff)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_toSchwartzMap : (φ.toSchwartzMap : E → ℂ) = fun ξ ↦ (φ ξ : ℂ) :=
  funext (HasCompactSupport.toSchwartzMap_toFun _ _)

private theorem fourierInv_eq_toSchwartzMap :
    𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) = ⇑(𝓕⁻ φ.toSchwartzMap : 𝓢(E, ℂ)) := by
  rw [SchwartzMap.fourierInv_coe, coe_toSchwartzMap]

/-- The inverse Fourier transform `𝓕⁻ φ` of a bump function, the kernel of the low-frequency
truncations, is integrable. -/
theorem integrable_fourierInv : MeasureTheory.Integrable (𝓕⁻ (fun ξ ↦ (φ ξ : ℂ))) := by
  rw [fourierInv_eq_toSchwartzMap]
  exact (𝓕⁻ φ.toSchwartzMap : 𝓢(E, ℂ)).integrable

/-- The inverse Fourier transform `𝓕⁻ φ` of a bump function has integral `φ 0 = 1`. -/
theorem integral_fourierInv : ∫ x, 𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x = 1 := by
  -- `∫ 𝓕⁻ φ = 𝓕 (𝓕⁻ φ) 0 = φ 0`.
  have h0 : (𝓕 (𝓕⁻ φ.toSchwartzMap : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) = φ.toSchwartzMap :=
    FourierTransform.fourier_fourierInv_eq _
  have h := congrArg (fun g : 𝓢(E, ℂ) ↦ g 0) h0
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq, inner_zero_right, neg_zero,
    AddChar.map_zero_eq_one, one_smul] at h
  rw [fourierInv_eq_toSchwartzMap, h, coe_toSchwartzMap]
  simp [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)]

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

variable (F) in
/-- The **low-frequency truncation** `Sⱼ = ∑_{k < j} Δₖ`, the sum of the Littlewood–Paley blocks of
index below `j`. For `j ≥ 1` it is the Fourier multiplier by `φ (2^{1-j} ·)`
(`TemperedDistribution.littlewoodPaleyLowPass_succ_eq_fourierMultiplierCLM`), and `S₀ = 0`. These
are the truncations from which Bony's paraproducts are built. -/
noncomputable def littlewoodPaleyLowPass (φ : ContDiffBump (0 : E)) (j : ℕ) :
    𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  ∑ k ∈ Finset.range j, littlewoodPaleyBlock F φ k

theorem littlewoodPaleyLowPass_def (j : ℕ) :
    littlewoodPaleyLowPass F φ j = ∑ k ∈ Finset.range j, littlewoodPaleyBlock F φ k :=
  (rfl)

@[simp]
theorem littlewoodPaleyLowPass_zero : littlewoodPaleyLowPass F φ 0 = 0 := by
  simp [littlewoodPaleyLowPass_def]

theorem littlewoodPaleyLowPass_succ (j : ℕ) :
    littlewoodPaleyLowPass F φ (j + 1) =
      littlewoodPaleyLowPass F φ j + littlewoodPaleyBlock F φ j := by
  simp only [littlewoodPaleyLowPass_def, Finset.sum_range_succ]

/-- `S_{j+1}` is the Fourier multiplier by `φ (2^{-j} ·)`. -/
theorem littlewoodPaleyLowPass_succ_eq_fourierMultiplierCLM (j : ℕ) :
    littlewoodPaleyLowPass F φ (j + 1) =
      fourierMultiplierCLM F fun ξ ↦ (φ (((2 : ℝ) ^ j)⁻¹ • ξ) : ℂ) :=
  sum_littlewoodPaleyBlock_range φ j

/-- The low-frequency truncations converge to the identity: `Sⱼ u → u` in `𝓢'(E, F)`. -/
theorem tendsto_littlewoodPaleyLowPass (u : 𝓢'(E, F)) :
    Tendsto (fun j ↦ littlewoodPaleyLowPass F φ j u) atTop (𝓝 u) := by
  simpa only [littlewoodPaleyLowPass_def, _root_.sum_apply] using
    tendsto_sum_littlewoodPaleyBlock φ u

open Distribution in
/-- **The spectrum of a low-frequency truncation.** The Fourier transform of `S_{j+1} u` vanishes
outside the closed ball of radius `2^j φ.rOut`. -/
theorem isVanishingOn_fourier_littlewoodPaleyLowPass_succ (j : ℕ) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (littlewoodPaleyLowPass F φ (j + 1) u) : 𝓢'(E, F))
      (Metric.closedBall 0 (2 ^ j * φ.rOut))ᶜ := by
  rw [littlewoodPaleyLowPass_succ_eq_fourierMultiplierCLM]
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ ?_) u
  have hξ' : 2 ^ j * φ.rOut < ‖ξ‖ := by simpa using hξ
  rw [φ.zero_of_le_dist ?_, Complex.ofReal_zero]
  rw [dist_zero_right, norm_smul, norm_inv, norm_pow, Real.norm_two,
    le_inv_mul_iff₀ (by positivity)]
  exact hξ'.le

open Distribution in
/-- **The spectrum of a dyadic block.** For `j ≥ 0` the Fourier transform of `Δ_{j+1} u` vanishes
outside the closed annulus `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`, which carries `ψ_{j+1}`. -/
theorem isVanishingOn_fourier_littlewoodPaleyBlock_succ (j : ℕ) (u : 𝓢'(E, F)) :
    IsVanishingOn (𝓕 (littlewoodPaleyBlock F φ (j + 1) u) : 𝓢'(E, F))
      {ξ | 2 ^ j * φ.rIn ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 ^ (j + 1) * φ.rOut}ᶜ := by
  rw [littlewoodPaleyBlock_apply]
  refine isVanishingOn_fourier_fourierMultiplierCLM (fun ξ hξ ↦ ?_) u
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hξ
  rcases hξ with hξ | hξ
  · rw [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le hξ.le, Complex.ofReal_zero]
  · rw [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hξ.le, Complex.ofReal_zero]
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
  -- The symbol `ψⱼ` is smooth and compactly supported, hence a Schwartz function.
  have hσ := (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).comp_left Complex.ofReal_zero
  set σ : 𝓢(E, ℂ) :=
    hσ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (φ.contDiff_inhomogeneousLittlewoodPaley j))
  have hσ_coe : (σ : E → ℂ) = fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ f
  rw [hσ_coe] at hg hgf
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

/-- The symbol `φ (2^{-j} ·)` of `S_{j+1}`, as a Schwartz function. -/
private noncomputable def lowPassSymbol (j : ℕ) : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun ξ ↦ (φ (((2 : ℝ) ^ j)⁻¹ • ξ) : ℂ))
    ((φ.hasCompactSupport.comp_smul (inv_ne_zero (pow_ne_zero j two_ne_zero))).comp_left
      Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp (contDiff_const_smul _)))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_lowPassSymbol (j : ℕ) :
    (lowPassSymbol φ j : E → ℂ) = fun ξ ↦ (φ (((2 : ℝ) ^ j)⁻¹ • ξ) : ℂ) :=
  funext (HasCompactSupport.toSchwartzMap_toFun _ _)

/-- **The low-frequency truncations are bounded on `Lᵖ` uniformly in `j`.** For every
`1 ≤ p ≤ ∞`, every `j` and every `f ∈ Lᵖ`, the truncation `Sⱼ f` is a function in `Lᵖ` with
`‖Sⱼ f‖_p ≤ ‖𝓕⁻ φ‖₁ ‖f‖_p`. The kernel of `S_{j+1}` is the `L¹`-normalised dilate
`2^{jn} 𝓕⁻ φ (2^j ·)` of `𝓕⁻ φ`. -/
theorem exists_littlewoodPaleyLowPass_eq_and_norm_le [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (j : ℕ) (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), littlewoodPaleyLowPass F φ j (f : 𝓢'(E, F)) = g ∧
      ‖g‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖f‖ := by
  rcases j with _ | j
  · refine ⟨0, ?_, ?_⟩
    · rw [littlewoodPaleyLowPass_zero, _root_.zero_apply,
        ← Lp.toTemperedDistributionCLM_apply, map_zero]
    · rw [norm_zero]
      exact mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg f)
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le (lowPassSymbol φ j) f
  rw [coe_lowPassSymbol, TauCeti.integral_norm_fourierInv_comp_smul (fun ξ ↦ (φ ξ : ℂ))
    (inv_ne_zero (pow_ne_zero j two_ne_zero))] at hgf
  rw [coe_lowPassSymbol] at hg
  exact ⟨g, by rw [littlewoodPaleyLowPass_succ_eq_fourierMultiplierCLM, hg], hgf⟩

/-- **`S_{j+1}` averages against the dilates of `𝓕⁻ φ`.** If `f ∈ Lᵖ` and the truncation
`S_{j+1} f` is the `Lᵖ` function `g`, then almost everywhere

`g x = ∫ 𝓕⁻ φ (s) • f (x - 2^{-j} s) ds`.

Since `∫ 𝓕⁻ φ = φ 0 = 1`, this exhibits `S_{j+1}` as an approximate identity. -/
theorem ae_eq_integral_of_littlewoodPaleyLowPass_succ_eq [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (j : ℕ) {f g : Lp F p (volume : Measure E)}
    (hg : littlewoodPaleyLowPass F φ (j + 1) (f : 𝓢'(E, F)) = g) :
    g =ᵐ[volume] fun x ↦ ∫ s, 𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) s • f (x - ((2 : ℝ) ^ j)⁻¹ • s) := by
  obtain ⟨g', hg', hconv, -⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq
    (lowPassSymbol φ j) f (q := p) (r := 1) le_rfl (by rw [inv_one, add_comm])
  rw [coe_lowPassSymbol, ← littlewoodPaleyLowPass_succ_eq_fourierMultiplierCLM, hg] at hg'
  have hgg' : g = g' := LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simpa only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply] using hg'
  rw [hgg']
  refine hconv.trans (Eventually.of_forall fun x ↦ ?_)
  -- Substitute `t = 2^{-j} s` in the convolution integral.
  set c : ℝ := ((2 : ℝ) ^ j)⁻¹ with hc_def
  have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero j two_ne_zero)
  rw [coe_lowPassSymbol, convolution_def, ← hc_def]
  dsimp only
  simp only [ContinuousLinearMap.lsmul_apply]
  simp_rw [TauCeti.fourierInv_comp_smul (fun ξ ↦ (φ ξ : ℂ)) c, smul_assoc]
  rw [integral_smul]
  have h := Measure.integral_comp_smul volume
    (fun t ↦ 𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) (c⁻¹ • t) • f (x - t)) c
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  rw [h, abs_inv]

end Lp

end TemperedDistribution
