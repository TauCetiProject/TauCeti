/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
public import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Convolution.Commutator
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Data.Nat.Interval
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

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
is deduced, by duality, from the convergence of the truncations `φ (R⁻¹ ·) • f → f` of Schwartz
functions as `R → ∞` (`SchwartzMap.tendsto_smulLeftCLM_contDiffBump`).

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

The same dilation makes the `k`-th moment `∫ ‖x‖ ^ k ‖𝓕⁻ ψⱼ x‖` of the kernel `O(2^{-jk})`: the
kernel lives at the spatial scale `2^{-j}`. Hence, by the first moment bound, the commutator of
`Δⱼ` with multiplication by a
`K`-Lipschitz function `f` gains one derivative,
`‖Δⱼ (f • g) - f • Δⱼ g‖_p ≤ C 2^{-j} K ‖g‖_p` for `1 ≤ p ≤ ∞`, with `C` depending only on `φ`:
the commutator gains the factor `2^{-j}` over the uniform bound `‖Δⱼ g‖_p ≤ C ‖g‖_p`, and the
estimate involves only the Lipschitz constant of `f`, not its size. This is the commutator
estimate used for paraproducts and transport equations (Bahouri–Chemin–Danchin, Lemma 2.97).

In `L²` the blocks are Fourier multipliers by the real symbols `ψⱼ`. The blocks of an `L²`
function are square summable, `∑ⱼ ‖Δⱼ f‖₂² ≤ C ‖f‖₂²`, by the `L²` Littlewood–Paley inequality
`TauCeti.exists_sum_norm_fourierMultiplierCLM_sq_le`. Conversely, if the blocks `gⱼ = Δⱼ v` of a
tempered distribution are `L²` functions, each `gⱼ` is fixed by the multiplier by the enlarged
cutoff `Ψⱼ` (`ContDiffBump.enlargedLittlewoodPaley`), which annihilates `gₖ` for `k` far above
`j`. That multiplier is self-adjoint, so `gⱼ` and `gₖ` are orthogonal, and when `∑ⱼ ‖gⱼ‖₂² < ∞`
the series `∑ⱼ gⱼ` converges in `L²`; by reconstruction its sum is `v`.

This decomposition underlies the dyadic description of Besov spaces and of the Bessel-potential
spaces `H^{s,p}`: the Besov norm of `u` is a weighted sequence norm of the `Lᵖ` norms of the
blocks `Δⱼ u`.

## Main declarations

* `TemperedDistribution.littlewoodPaleyBlock`: the Littlewood–Paley block `Δⱼ`.
* `TemperedDistribution.sum_littlewoodPaleyBlock_range`: the partial sums are the low-pass
  truncations by `φ (2^{-N} ·)`.
* `TemperedDistribution.tendsto_fourierMultiplierCLM_contDiffBump`: the low-pass truncations
  `𝓕⁻ (φ (R⁻¹ ·) • 𝓕 u)` converge to `u` as `R → ∞`.
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
  between the blocks of two bump functions, and
  `TemperedDistribution.exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock`,
  `TemperedDistribution.exists_littlewoodPaleyBlock_sub_sum_range_eq`: its forms for the low-pass
  truncations and their remainders.
* `TemperedDistribution.enlargedLittlewoodPaleyBlock`: the enlarged multiplier `Δ'ⱼ` by the cutoff
  `ContDiffBump.enlargedLittlewoodPaley L j`, equal to `∑_{j + 1 - L ≤ m < j + L} Δₘ`
  (`TemperedDistribution.enlargedLittlewoodPaleyBlock_eq_sum_Ico`), fixing `Δⱼ`
  (`TemperedDistribution.enlargedLittlewoodPaleyBlock_compL_littlewoodPaleyBlock`) and annihilated
  by distant blocks
  (`TemperedDistribution.littlewoodPaleyBlock_compL_enlargedLittlewoodPaleyBlock_eq_zero`).
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico`: each block of one bump function
  is a sum of boundedly many blocks of another, composed with it.
* `TemperedDistribution.littlewoodPaleyBlock_besselPotential_comm`,
  `TemperedDistribution.littlewoodPaleyBlock_postcomp`,
  `TemperedDistribution.littlewoodPaleyBlock_postcomp_eq_compLp`: the blocks commute with the
  Bessel potentials and with post-composition by continuous linear maps on the fiber.
* `TemperedDistribution.littlewoodPaleyBlock_apply_apply`: the blocks are symmetric for the
  pairing with Schwartz functions, `(Δⱼ u) f = u (Δⱼ f)`.
* `TemperedDistribution.littlewoodPaleyBlock_toTemperedDistributionCLM_eq_ite`: a Schwartz function
  whose Fourier transform is carried by the region where `ψⱼ = 1` is its own `j`-th block and has
  no other block.
* `ContDiffBump.integral_norm_fourierInv_inhomogeneousLittlewoodPaley_succ`: the dyadic kernels
  `𝓕⁻ ψⱼ`, `j ≥ 1`, all have the same `L¹` norm, and
  `ContDiffBump.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_succ`,
  `ContDiffBump.norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ`,
  `ContDiffBump.rpow_mul_norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ`: their
  `Lʳ` norms grow like `2^{j n (1 - 1/r)}`;
  `ContDiffBump.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_ne_zero`,
  `ContDiffBump.norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_pos`: each kernel `𝓕⁻ ψⱼ`
  is nonzero in every `Lʳ`.
* `ContDiffBump.integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ` and
  `ContDiffBump.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le`: the
  `k`-th moments of the kernels `𝓕⁻ ψⱼ` are `O(2^{-jk})`.
* `ContDiffBump.integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ`: the
  moments of real order `s` of the kernels `𝓕⁻ ψ_{j+1}` are `2^{-js}` times those of `𝓕⁻ ψ₁`.
* `ContDiffBump.integral_fourierInv_inhomogeneousLittlewoodPaley_succ_smul_apply_eq_zero`: the
  kernels `𝓕⁻ ψ_{j+1}` annihilate every homogeneous polynomial, since `ψ_{j+1}` vanishes near the
  origin.
* `exists_integrable_and_integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le`,
  in the namespace `ContDiffBump`: the moments of real order `α ≥ 0` of the kernels `𝓕⁻ ψⱼ` are
  `O(2^{-jα})`.
* `ContDiffBump.integral_fourierInv_inhomogeneousLittlewoodPaley_succ`: the kernels `𝓕⁻ ψⱼ`,
  `j ≥ 1`, have integral zero.
* `ContDiffBump.fourierInv_inhomogeneousLittlewoodPaley_neg`: the kernels `𝓕⁻ ψⱼ` are even.
* `TemperedDistribution.littlewoodPaleyBlock_delta_zero` and
  `TemperedDistribution.littlewoodPaleyBlock_delta_zero_eq_toLp`: the blocks of the Dirac mass `δ₀`
  are the kernels `𝓕⁻ ψⱼ`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le` and
  `TemperedDistribution.exists_enlargedLittlewoodPaleyBlock_eq_and_norm_le`: the blocks and
  enlarged blocks are bounded on `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`; and so are the low-pass
  truncations `𝓕⁻ (φ (R⁻¹ ·) • 𝓕 ·)`, uniformly in the scale `R ≠ 0`, by `‖𝓕⁻ φ‖₁`
  (`TemperedDistribution.exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le`), in particular the
  partial sums `∑_{j ≤ N} Δⱼ`
  (`TemperedDistribution.exists_sum_littlewoodPaleyBlock_eq_and_norm_le`).
* `TemperedDistribution.ae_eq_convolution_of_littlewoodPaleyBlock_eq`: on `Lᵖ`, the block `Δⱼ` is
  convolution with `𝓕⁻ ψⱼ`.
* `TemperedDistribution.exists_eLpNorm_littlewoodPaleyBlock_smul_sub_smul_le`: the commutator of
  `Δⱼ` with a Lipschitz function is `O(2^{-j})` on `Lᵖ`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le_of_le`: Bernstein's inequality
  `‖Δⱼ u‖_r ≤ C 2^{j n (1/p - 1/r)} ‖Δⱼ u‖_p` for `p ≤ r`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_sum_norm_sq_le`: the blocks of an
  `L²` function are square summable in `L²`.
* `TemperedDistribution.exists_inner_eq_zero_of_littlewoodPaleyBlock_eq`: `L²` blocks with indices
  far apart are orthogonal, also for blocks of two distributions built from two bump functions.
* `TemperedDistribution.exists_eq_and_norm_sq_le_of_littlewoodPaleyBlock_eq`: a tempered
  distribution whose blocks are square-summable `L²` functions is an `L²` function.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.2 and Lemma 2.97 (the commutator estimate).
-/

public section

open Filter Topology
open FourierTransform
open scoped SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace ContDiffBump

variable (φ : ContDiffBump (0 : E))

/-- The Schwartz kernel `𝓕⁻ ψⱼ`, as a function, is the inverse Fourier transform of the function
`ψⱼ`. -/
theorem coe_fourierInv_inhomogeneousLittlewoodPaleySchwartz (j : ℕ) :
    ⇑(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) : 𝓢(E, ℂ)) =
      𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
  rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]

/-- **The moments of the dyadic kernels scale with `j`.** Since `𝓕⁻ ψ_{j+1}` is the
`L¹`-normalised dilate `2^{jn} 𝓕⁻ ψ₁ (2^j ·)` in dimension `n`, its moment of real order `s`,
`∫ ‖x‖ ^ s ‖𝓕⁻ ψ_{j+1} x‖`, is `2^{-js}` times that of `𝓕⁻ ψ₁`. -/
theorem integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (s : ℝ) (j : ℕ) :
    ∫ x, ‖x‖ ^ s * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) x‖ =
      ((2 ^ j : ℝ) ^ s)⁻¹ *
        ∫ x, ‖x‖ ^ s * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) x‖ := by
  simp_rw [φ.inhomogeneousLittlewoodPaley_succ_apply_eq_one_apply j]
  rw [TauCeti.integral_norm_rpow_mul_norm_fourierInv_comp_smul
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) s (inv_ne_zero (pow_ne_zero _ two_ne_zero)),
    abs_of_pos (by positivity), Real.inv_rpow (by positivity)]

/-- **The moments of the dyadic kernels scale with `j`.** The `k`-th moment
`∫ ‖x‖ ^ k ‖𝓕⁻ ψ_{j+1} x‖` is `2^{-jk}` times that of `𝓕⁻ ψ₁`. -/
theorem integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (k j : ℕ) :
    ∫ x, ‖x‖ ^ k * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) x‖ =
      ((2 ^ j) ^ k)⁻¹ *
        ∫ x, ‖x‖ ^ k * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) x‖ := by
  simpa only [Real.rpow_natCast] using
    φ.integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ k j

/-- **The dyadic kernels have vanishing moments.** Since `ψ_{j+1}` vanishes near the origin, the
kernel `𝓕⁻ ψ_{j+1}` annihilates every homogeneous polynomial: `∫ 𝓕⁻ ψ_{j+1} y • A (y, …, y) = 0`
for every continuous multilinear map `A`. -/
theorem integral_fourierInv_inhomogeneousLittlewoodPaley_succ_smul_apply_eq_zero (j : ℕ) {n : ℕ}
    (A : E [×n]→L[ℝ] F) :
    ∫ y, 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) y • A (fun _ ↦ y) = 0 := by
  rw [← φ.coe_inhomogeneousLittlewoodPaleySchwartz, ← SchwartzMap.fourierInv_coe]
  refine SchwartzMap.integral_smul_apply_eq_zero_of_iteratedFDeriv_fourier_eq_zero _ ?_ A
  have h0 : (𝓕 ⇑(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz (j + 1)) : 𝓢(E, ℂ))) =ᶠ[𝓝 0] 0 := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) (mul_pos (pow_pos two_pos j) φ.rIn_pos)]
      with ξ hξ
    simp [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le (mem_closedBall_zero_iff.1 hξ)]
  simpa using (h0.iteratedFDeriv ℝ n).eq_of_nhds

/-- **The dyadic kernels are `L¹`-dilates of one another.** Since `ψ_{j+1} = ψ₁ (2^{-j} ·)`, the
kernel `𝓕⁻ ψ_{j+1}` is `2^{jn} 𝓕⁻ ψ₁ (2^j ·)` in dimension `n`, so it has the same `L¹` norm as
`𝓕⁻ ψ₁`. -/
theorem integral_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (j : ℕ) :
    ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) x‖ =
      ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) x‖ := by
  simpa using φ.integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ 0 j

open scoped NNReal in
/-- **The `k`-th moments of the kernels `𝓕⁻ ψⱼ` are `O(2^{-jk})`.** There is `C`, depending only
on `φ` and `k`, with `∫ ‖x‖ ^ k ‖𝓕⁻ ψⱼ x‖ ≤ 2^{-jk} C` for every `j`. -/
theorem exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le (k : ℕ) :
    ∃ C : ℝ≥0, ∀ j : ℕ,
      ∫ x, ‖x‖ ^ k * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖ ≤
        ((2 ^ j) ^ k)⁻¹ * C := by
  set M : ℕ → ℝ := fun j ↦
    ∫ x, ‖x‖ ^ k * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖
  have hM0 : 0 ≤ M 0 := MeasureTheory.integral_nonneg fun x ↦ by positivity
  refine ⟨⟨max (M 0) (2 ^ k * M 1), hM0.trans (le_max_left _ _)⟩, fun j ↦ ?_⟩
  rcases j with _ | j
  · rw [pow_zero, one_pow, inv_one, one_mul]
    exact le_max_left _ _
  · calc M (j + 1) = ((2 ^ (j + 1)) ^ k)⁻¹ * (2 ^ k * M 1) := by
          rw [pow_succ, mul_pow, mul_inv, mul_assoc, inv_mul_cancel_left₀ (by positivity)]
          exact φ.integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ k j
      _ ≤ _ := by gcongr; exact le_max_right _ _

open MeasureTheory in
/-- **The moments of order `α ≥ 0` of the kernels `𝓕⁻ ψⱼ` are `O(2^{-jα})`.** There is `C`,
depending only on `φ` and `α`, such that `x ↦ ‖x‖ ^ α ‖𝓕⁻ ψⱼ x‖` is integrable with
`∫ ‖x‖ ^ α ‖𝓕⁻ ψⱼ x‖ ≤ 2^{-jα} C` for every `j`. This is the real-exponent form of
`ContDiffBump.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le`. -/
theorem exists_integrable_and_integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le
    {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      Integrable (fun x ↦ ‖x‖ ^ α * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖) ∧
      ∫ x, ‖x‖ ^ α * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖ ≤
        ((2 : ℝ) ^ (α * j))⁻¹ * C := by
  -- With `n = ⌈α⌉₊`, the scaled weight satisfies `(2^j ‖x‖) ^ α ≤ 1 + (2^j ‖x‖) ^ n`, which
  -- reduces the claim to the moments of orders `0` and `n`.
  set n := ⌈α⌉₊
  obtain ⟨C₀, hC₀⟩ :=
    φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 0
  obtain ⟨Cₙ, hCₙ⟩ :=
    φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le n
  refine ⟨C₀ + Cₙ, by positivity, fun j ↦ ?_⟩
  set κ : 𝓢(E, ℂ) := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hκ : (κ : E → ℂ) = 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
    φ.coe_fourierInv_inhomogeneousLittlewoodPaleySchwartz j
  rw [← hκ, mul_comm α, Real.rpow_mul zero_le_two, Real.rpow_natCast]
  set c : ℝ := 2 ^ j
  have hle (x : E) : ‖x‖ ^ α * ‖κ x‖ ≤ (c ^ α)⁻¹ * (‖κ x‖ + c ^ n * (‖x‖ ^ n * ‖κ x‖)) := by
    have hy : 0 ≤ c * ‖x‖ := by positivity
    have h : (c * ‖x‖) ^ α ≤ 1 + (c * ‖x‖) ^ n := by
      rcases le_total (c * ‖x‖) 1 with h1 | h1
      · linarith [Real.rpow_le_one hy h1 hα, pow_nonneg hy n]
      · linarith [Real.rpow_natCast (c * ‖x‖) n ▸
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil α)]
    rw [Real.mul_rpow (by positivity) (norm_nonneg x), mul_pow] at h
    calc ‖x‖ ^ α * ‖κ x‖ = (c ^ α)⁻¹ * (c ^ α * ‖x‖ ^ α * ‖κ x‖) := by
          rw [mul_assoc (c ^ α), inv_mul_cancel_left₀ (by positivity)]
      _ ≤ (c ^ α)⁻¹ * ((1 + c ^ n * ‖x‖ ^ n) * ‖κ x‖) := by gcongr
      _ = _ := by ring
  have hint₀ : Integrable fun x ↦ ‖κ x‖ := κ.integrable.norm
  have hintₙ : Integrable fun x ↦ ‖x‖ ^ n * ‖κ x‖ := κ.integrable_pow_mul volume n
  have hdom : Integrable fun x ↦ (c ^ α)⁻¹ * (‖κ x‖ + c ^ n * (‖x‖ ^ n * ‖κ x‖)) :=
    (hint₀.add (hintₙ.const_mul _)).const_mul _
  have hint : Integrable fun x ↦ ‖x‖ ^ α * ‖κ x‖ :=
    hdom.mono' ((continuous_norm.rpow_const fun _ ↦ Or.inr hα).mul
      κ.continuous.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ (Real.norm_of_nonneg (by positivity)).trans_le (hle x))
  refine ⟨hint, (integral_mono hint hdom hle).trans ?_⟩
  have h₀ : ∫ x, ‖κ x‖ ≤ C₀ := by simpa [hκ] using hC₀ j
  have hₙ : ∫ x, ‖x‖ ^ n * ‖κ x‖ ≤ (c ^ n)⁻¹ * Cₙ := by simpa [hκ, c] using hCₙ j
  rw [integral_const_mul, integral_add hint₀ (hintₙ.const_mul _), integral_const_mul]
  calc (c ^ α)⁻¹ * ((∫ x, ‖κ x‖) + c ^ n * ∫ x, ‖x‖ ^ n * ‖κ x‖)
      ≤ (c ^ α)⁻¹ * (C₀ + c ^ n * ((c ^ n)⁻¹ * Cₙ)) := by gcongr
    _ = (c ^ α)⁻¹ * (C₀ + Cₙ) := by rw [mul_inv_cancel_left₀ (by positivity)]

open MeasureTheory in
/-- **The dyadic kernels have integral zero.** For `j ≥ 1` the symbol `ψⱼ` vanishes at the
origin, so its kernel `𝓕⁻ ψⱼ` has integral `ψⱼ 0 = 0`: the blocks `Δⱼ` with `j ≥ 1` annihilate
constants. -/
theorem integral_fourierInv_inhomogeneousLittlewoodPaley_succ (j : ℕ) :
    ∫ x, 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) x = 0 := by
  set σ : 𝓢(E, ℂ) := φ.inhomogeneousLittlewoodPaleySchwartz (j + 1) with hσ
  -- The integral of `𝓕⁻ σ` is the value at `0` of its Fourier transform `𝓕 (𝓕⁻ σ) = σ`.
  have h0 : (𝓕 (𝓕⁻ σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) 0 = σ 0 := by rw [fourier_fourierInv_eq]
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq, inner_zero_right, neg_zero,
    AddChar.map_zero_eq_one, one_smul, SchwartzMap.fourierInv_coe, hσ,
    φ.coe_inhomogeneousLittlewoodPaleySchwartz] at h0
  rw [h0, φ.inhomogeneousLittlewoodPaley_succ_apply]
  simp

/-- The kernels `𝓕⁻ ψⱼ` are even, since the symbols `ψⱼ` are. -/
theorem fourierInv_inhomogeneousLittlewoodPaley_neg (j : ℕ) (x : E) :
    𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (-x) =
      𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x := by
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, Real.fourierInv_eq_fourier_comp_neg]
  simp only [φ.inhomogeneousLittlewoodPaley_neg]

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
/-- **The `Lʳ` norms of the Schwartz dyadic kernels.** In dimension `n`, the `Lʳ` norm of
`𝓕⁻ ψ_{j+1}` is `2^{n (1 - 1/r) j}` times that of `𝓕⁻ ψ₁`, where `1/∞ = 0`. -/
theorem norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ (j : ℕ) (r : ENNReal) :
    ‖(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz (j + 1))).toLp r (volume : Measure E)‖ =
      (2 : ℝ) ^ ((Module.finrank ℝ E * (1 - r.toReal⁻¹)) * j) *
        ‖(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz 1)).toLp r (volume : Measure E)‖ := by
  simp only [SchwartzMap.norm_toLp, SchwartzMap.fourierInv_coe,
    φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  rw [φ.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_succ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  congr 2
  rw [div_eq_mul_inv]
  ring

open MeasureTheory in
/-- **Geometric-sequence law for weighted dyadic kernel norms.** For every `s : ℝ` and
`r : ℝ≥0∞`, `2^{s (j+1)} ‖𝓕⁻ ψ_{j+1}‖_r = (2^s ‖𝓕⁻ ψ₁‖_r) (2^{s + n (1 - 1/r)})^j`. -/
theorem rpow_mul_norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ (s : ℝ) (j : ℕ)
    (r : ENNReal) :
    (2 : ℝ) ^ (s * (j + 1 : ℕ)) *
        ‖(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz (j + 1))).toLp r (volume : Measure E)‖ =
      2 ^ s * ‖(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz 1)).toLp r (volume : Measure E)‖ *
        (2 ^ (s + Module.finrank ℝ E * (1 - r.toReal⁻¹))) ^ j := by
  set m : ℝ := Module.finrank ℝ E * (1 - r.toReal⁻¹)
  set c : ℝ := ‖(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz 1)).toLp r (volume : Measure E)‖
  rw [φ.norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ,
    ← Real.rpow_mul_natCast zero_le_two]
  calc (2 : ℝ) ^ (s * (j + 1 : ℕ)) * (2 ^ (m * j) * c)
      = 2 ^ (s * (j + 1 : ℕ) + m * j) * c := by rw [Real.rpow_add two_pos]; ring
    _ = 2 ^ (s + (s + m) * j) * c := by push_cast; ring_nf
    _ = 2 ^ s * c * 2 ^ ((s + m) * j) := by rw [Real.rpow_add two_pos]; ring

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The outer radius `2^{k+1} φ.rOut` of the `(k+1)`-st dyadic annulus is `B` times its inner
radius `2^k φ.rIn`, for `B = 2 φ.rOut / φ.rIn`. -/
theorem two_mul_rOut_div_rIn_mul (k : ℕ) :
    2 * φ.rOut / φ.rIn * (2 ^ k * φ.rIn) = 2 ^ (k + 1) * φ.rOut := by
  field_simp [φ.rIn_pos.ne']
  ring

open MeasureTheory in
/-- On a nontrivial space, each Schwartz dyadic kernel `𝓕⁻ ψⱼ` has strictly positive `Lʳ` norm
for every `r ≠ 0`. -/
theorem norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_pos [Nontrivial E] (j : ℕ)
    {r : ENNReal} (hr : r ≠ 0) :
    0 < ‖(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).toLp r (volume : Measure E)‖ := by
  rw [SchwartzMap.norm_toLp]
  refine ENNReal.toReal_pos ?_ (SchwartzMap.eLpNorm_lt_top _ r volume).ne
  rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  exact φ.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_ne_zero j hr

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

/-- **The Littlewood–Paley blocks are symmetric.** For a tempered distribution `u` and a Schwartz
function `f`, `(Δⱼ u) f = u (Δⱼ f)`, where on the right `Δⱼ` is the Fourier multiplier by `ψⱼ` on
Schwartz functions. This holds because `ψⱼ` is even
(`ContDiffBump.inhomogeneousLittlewoodPaley_neg`). -/
theorem littlewoodPaleyBlock_apply_apply (j : ℕ) (u : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    littlewoodPaleyBlock F φ j u f =
      u (SchwartzMap.fourierMultiplierCLM ℂ
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f) :=
  fourierMultiplierCLM_apply_apply_of_even
    (fun ξ ↦ by simp only [φ.inhomogeneousLittlewoodPaley_neg]) u f

/-- The partial sums of the Littlewood–Paley blocks are the low-pass truncations:
`∑_{j ≤ N} Δⱼ = 𝓕⁻ (φ (2^{-N} ·) • 𝓕 ·)`. -/
theorem sum_littlewoodPaleyBlock_range (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ j =
      fourierMultiplierCLM F fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ) := by
  simp_rw [littlewoodPaleyBlock_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_sum F
    fun j _ ↦ φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j]
  simp_rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range]

/-- **Convergence of the low-pass truncations.** For every tempered distribution `u`, the
truncations `𝓕⁻ (φ (R⁻¹ ·) • 𝓕 u)` converge to `u` along any family of scales `R → ∞`. -/
theorem tendsto_fourierMultiplierCLM_contDiffBump {α : Type*} {l : Filter α} {R : α → ℝ}
    (hR : Tendsto R l atTop) (u : 𝓢'(E, F)) :
    Tendsto (fun a ↦ fourierMultiplierCLM F (fun ξ ↦ (φ ((R a)⁻¹ • ξ) : ℂ)) u) l (𝓝 u) := by
  refine PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 fun f ↦ ?_
  simp only [fourierMultiplierCLM_apply_apply]
  have h := ((map_continuous u).tendsto _).comp <|
    ((fourierCLM ℂ 𝓢(E, ℂ)).continuous.tendsto _).comp
      (SchwartzMap.tendsto_smulLeftCLM_contDiffBump hR φ (𝓕⁻ f))
  rwa [fourierCLM_apply, FourierTransform.fourier_fourierInv_eq] at h

/-- **Littlewood–Paley reconstruction.** Every tempered distribution is the limit in `𝓢'(E, F)`
of the partial sums of its Littlewood–Paley blocks: `u = ∑ⱼ Δⱼ u`. -/
theorem tendsto_sum_littlewoodPaleyBlock (u : 𝓢'(E, F)) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u) atTop (𝓝 u) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [← _root_.sum_apply, sum_littlewoodPaleyBlock_range]
  exact tendsto_fourierMultiplierCLM_contDiffBump φ
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) u

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

variable (F) in
/-- The **enlarged Littlewood–Paley block** `Δ'ⱼ u = 𝓕⁻ (Ψⱼ • 𝓕 u)` of width `L`, the Fourier
multiplier by the enlarged cutoff `ContDiffBump.enlargedLittlewoodPaley L j`, i.e., the sum
`∑_{j + 1 - L ≤ m < j + L} Δₘ` (`enlargedLittlewoodPaleyBlock_eq_sum_Ico`). When pieces of `φ` at
index distance at least `L` have disjoint supports (for instance `L = φ.littlewoodPaleyOverlap φ`),
it fixes `Δⱼ` (`enlargedLittlewoodPaleyBlock_compL_littlewoodPaleyBlock`) and is annihilated by
distant blocks (`littlewoodPaleyBlock_compL_enlargedLittlewoodPaleyBlock_eq_zero`). -/
noncomputable def enlargedLittlewoodPaleyBlock (L j : ℕ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F fun ξ ↦ (φ.enlargedLittlewoodPaley L j ξ : ℂ)

/-- Unfolding `TemperedDistribution.enlargedLittlewoodPaleyBlock`. -/
theorem enlargedLittlewoodPaleyBlock_eq_fourierMultiplierCLM (L j : ℕ) :
    enlargedLittlewoodPaleyBlock F φ L j =
      fourierMultiplierCLM F fun ξ ↦ (φ.enlargedLittlewoodPaley L j ξ : ℂ) :=
  (rfl)

/-- Unfolding `TemperedDistribution.enlargedLittlewoodPaleyBlock` on a tempered distribution. -/
theorem enlargedLittlewoodPaleyBlock_apply (L j : ℕ) (u : 𝓢'(E, F)) :
    enlargedLittlewoodPaleyBlock F φ L j u =
      fourierMultiplierCLM F (fun ξ ↦ (φ.enlargedLittlewoodPaley L j ξ : ℂ)) u :=
  (rfl)

/-- The enlarged Littlewood–Paley block is the finite sum of the blocks of index in
`[j + 1 - L, j + L)`. -/
theorem enlargedLittlewoodPaleyBlock_eq_sum_Ico (L j : ℕ) :
    enlargedLittlewoodPaleyBlock F φ L j =
      ∑ m ∈ Finset.Ico (j + 1 - L) (j + L), littlewoodPaleyBlock F φ m := by
  rw [enlargedLittlewoodPaleyBlock_eq_fourierMultiplierCLM]
  simp_rw [littlewoodPaleyBlock_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_sum F
    fun m _ ↦ φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley m]
  congr 1
  funext ξ
  rw [φ.enlargedLittlewoodPaley_apply, Complex.ofReal_sum]

/-- **The enlarged block fixes the corresponding Littlewood–Paley block.** If pieces of `φ` whose
indices differ by at least `L` have disjoint supports (for instance `L = φ.littlewoodPaleyOverlap φ`
via `ContDiffBump.inhomogeneousLittlewoodPaley_mul_eq_zero`), then `Δ'ⱼ ∘ Δⱼ = Δⱼ`. -/
theorem enlargedLittlewoodPaleyBlock_compL_littlewoodPaleyBlock {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : E,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (j : ℕ) :
    enlargedLittlewoodPaleyBlock F φ L j ∘L littlewoodPaleyBlock F φ j =
      littlewoodPaleyBlock F φ j := by
  rw [enlargedLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    littlewoodPaleyBlock_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_compL_fourierMultiplierCLM
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)
      (φ.hasTemperateGrowth_ofReal_enlargedLittlewoodPaley L j)]
  congr 1
  funext ξ
  rw [Pi.mul_apply, ← Complex.ofReal_mul, mul_comm,
    φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]

/-- Applied form of `enlargedLittlewoodPaleyBlock_compL_littlewoodPaleyBlock`:
`Δ'ⱼ (Δⱼ u) = Δⱼ u`. -/
theorem enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : E,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (j : ℕ) (u : 𝓢'(E, F)) :
    enlargedLittlewoodPaleyBlock F φ L j (littlewoodPaleyBlock F φ j u) =
      littlewoodPaleyBlock F φ j u :=
  congr($(enlargedLittlewoodPaleyBlock_compL_littlewoodPaleyBlock (F := F) φ hL j) u)

/-- **Almost orthogonality of single and enlarged blocks.** If pieces of `φ` whose indices differ
by at least `L'` have disjoint supports (for instance `L' = φ.littlewoodPaleyOverlap φ`), then
`Δₖ ∘ Δ'ⱼ = 0` whenever `|k - j| ≥ L + L'`, where `Δ'ⱼ` has width `L`. -/
theorem littlewoodPaleyBlock_compL_enlargedLittlewoodPaleyBlock_eq_zero {L L' : ℕ}
    (hL' : ∀ j k : ℕ, j + L' ≤ k → ∀ ξ : E,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    {j k : ℕ} (hjk : k + (L + L') ≤ j ∨ j + (L + L') ≤ k) :
    littlewoodPaleyBlock F φ k ∘L enlargedLittlewoodPaleyBlock F φ L j = 0 := by
  rw [littlewoodPaleyBlock_eq_fourierMultiplierCLM,
    enlargedLittlewoodPaleyBlock_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_compL_fourierMultiplierCLM
      (φ.hasTemperateGrowth_ofReal_enlargedLittlewoodPaley L j)
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k)]
  have hfn : ((fun ξ ↦ (φ.enlargedLittlewoodPaley L j ξ : ℂ)) *
      fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) = fun _ ↦ 0 := by
    funext ξ
    rw [Pi.mul_apply, ← Complex.ofReal_mul, φ.enlargedLittlewoodPaley_apply, Finset.sum_mul,
      Finset.sum_eq_zero fun m hm ↦ ?_, Complex.ofReal_zero]
    rw [Finset.mem_Ico] at hm
    rcases hjk with hjk | hjk
    · rw [mul_comm]
      exact hL' k m (by omega) ξ
    · exact hL' m k (by omega) ξ
  rw [hfn, fourierMultiplierCLM_const, zero_smul]

/-- Applied form of `littlewoodPaleyBlock_compL_enlargedLittlewoodPaleyBlock_eq_zero`:
`Δₖ (Δ'ⱼ u) = 0` whenever `|k - j| ≥ L + L'`. -/
theorem littlewoodPaleyBlock_enlargedLittlewoodPaleyBlock_eq_zero {L L' : ℕ}
    (hL' : ∀ j k : ℕ, j + L' ≤ k → ∀ ξ : E,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    {j k : ℕ} (hjk : k + (L + L') ≤ j ∨ j + (L + L') ≤ k) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ k (enlargedLittlewoodPaleyBlock F φ L j u) = 0 :=
  congr($(littlewoodPaleyBlock_compL_enlargedLittlewoodPaleyBlock_eq_zero (F := F) φ hL' hjk) u)

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

/-- **Low-pass truncations against single blocks.** There is `L`, depending only on `φ`, such
that the low-pass truncation `S_N = ∑_{j ≤ N} Δⱼ` fixes the block `Δₖ u` when `k + L ≤ N`, and the
block `Δₖ` annihilates `S_N u` when `N + L ≤ k`. -/
theorem exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock :
    ∃ L : ℕ, ∀ k N : ℕ,
      (k + L ≤ N → ∀ u : 𝓢'(E, F),
        ∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ j (littlewoodPaleyBlock F φ k u) =
          littlewoodPaleyBlock F φ k u) ∧
      (N + L ≤ k → ∀ u : 𝓢'(E, F),
        littlewoodPaleyBlock F φ k (∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ j u) =
          0) := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ φ
  refine ⟨L, fun k N ↦ ⟨fun hkN u ↦ ?_, fun hNk u ↦ ?_⟩⟩
  · refine sum_littlewoodPaleyBlock_eq_self φ _ fun j hj ↦ ?_
    have hkj : k + L ≤ j := by
      have := Finset.mem_range.not.1 hj
      omega
    simpa using DFunLike.congr_fun (hL k j hkj).2 u
  · rw [map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjk : j + L ≤ k := by
      have := Finset.mem_range.1 hj
      omega
    simpa using DFunLike.congr_fun (hL j k hjk).2 u

/-- **Window-sum formula for low-pass truncation remainders.** There is `L`, depending only on `φ`,
such that for every `k` and `N`, the block `Δₖ (u - ∑_{j < N} Δⱼ u)` is the finite window sum of
`Δₖ Δⱼ u` over `k - L ≤ j < k + L` with `N ≤ j`. -/
theorem exists_littlewoodPaleyBlock_sub_sum_range_eq :
    ∃ L : ℕ, ∀ (N k : ℕ) (u : 𝓢'(E, F)),
      littlewoodPaleyBlock F φ k (u - ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u) =
        ∑ j ∈ Finset.Ico (k - L) (k + L),
          if N ≤ j then littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) else 0 := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ φ
  refine ⟨L, fun N k u ↦ ?_⟩
  have hvanish {j : ℕ} (hj : j ∉ Finset.Ico (k - L) (k + L)) :
      littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) = 0 := by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hj
    rcases hj with hj | hj
    · exact congr($((hL j k (by omega)).2) u)
    · exact congr($((hL k j (by omega)).1) u)
  have hfull : littlewoodPaleyBlock F φ k u =
      ∑ j ∈ Finset.Ico (k - L) (k + L),
        littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) := by
    refine tendsto_nhds_unique
      (((map_continuous (littlewoodPaleyBlock F φ k)).tendsto u).comp
        (tendsto_sum_littlewoodPaleyBlock φ u))
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop (k + L)] with M hM
    simp only [Function.comp_apply, map_sum]
    exact Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 ((Finset.mem_Ico.1 hj).2.trans_le hM))
      fun j _ hj ↦ hvanish hj
  have hpart : littlewoodPaleyBlock F φ k (∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u) =
      ∑ j ∈ Finset.Ico (k - L) (k + L),
        if j < N then littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) else 0 := by
    rw [map_sum, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 (Finset.mem_filter.1 hj).2)
      fun j hj hj' ↦ hvanish fun hIco ↦
        hj' (Finset.mem_filter.2 ⟨hIco, Finset.mem_range.1 hj⟩)).symm
  rw [map_sub, hfull, hpart, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases lt_or_ge j N with hj | hj
  · simp [hj, not_le.2 hj]
  · simp [hj, not_lt.2 hj]

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

/-- Littlewood–Paley blocks commute with post-composition by a continuous linear map on the fiber:
`Δⱼ` acts on test functions, whereas `L` acts on values. -/
theorem littlewoodPaleyBlock_postcomp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (j : ℕ) (L : F →L[ℂ] G) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock G φ j (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u) =
      PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L (littlewoodPaleyBlock F φ j u) := by
  ext ψ
  simp only [littlewoodPaleyBlock_apply, PointwiseConvergenceCLM.postcomp_apply_apply,
    fourierMultiplierCLM_apply_apply]

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
open scoped ENNReal NNReal

/-- For every `1 ≤ p ≤ ∞`, the block `Δⱼ δ₀` is the `Lᵖ` function `𝓕⁻ ψⱼ`. -/
theorem littlewoodPaleyBlock_delta_zero_eq_toLp (j : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    littlewoodPaleyBlock ℂ φ j (delta 0) =
      ((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).toLp p (volume : Measure E) :
        𝓢'(E, ℂ)) := by
  rw [Lp.toTemperedDistribution_toLp_eq, littlewoodPaleyBlock_delta_zero]

variable {φ} in
/-- If the `j`-th Littlewood–Paley block of `u` is the `Lᵖ` function `f`, then the `j`-th block of
`L ∘ u` is `L.compLp f`. -/
theorem littlewoodPaleyBlock_postcomp_eq_compLp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace F] [CompleteSpace G] {j : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : F →L[ℂ] G) {u : 𝓢'(E, F)} {f : Lp F p (volume : Measure E)}
    (hf : littlewoodPaleyBlock F φ j u = f) :
    littlewoodPaleyBlock G φ j (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u) =
      (L.compLp f : 𝓢'(E, G)) := by
  rw [littlewoodPaleyBlock_postcomp, hf]
  ext ψ
  rw [PointwiseConvergenceCLM.postcomp_apply_apply, Lp.toTemperedDistribution_compLp_apply]

/-- **The Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in `j`.** There is `C`, depending
only on `φ`, such that for every `1 ≤ p ≤ ∞`, every `j` and every `f ∈ Lᵖ`, the block `Δⱼ f` is a
function in `Lᵖ` with `‖Δⱼ f‖_p ≤ C ‖f‖_p`. -/
theorem exists_littlewoodPaleyBlock_eq_and_norm_le [CompleteSpace F] :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  -- The kernels `𝓕⁻ ψⱼ` are bounded in `L¹`: this is the zeroth moment bound.
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 0
  refine ⟨C, fun {p} _ j f ↦ ?_⟩
  have hK : ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖ ≤ C := by
    simpa using hC j
  obtain ⟨g, hg, hgf⟩ :=
    exists_fourierMultiplierCLM_eq_and_norm_le (φ.inhomogeneousLittlewoodPaleySchwartz j) f
  rw [φ.coe_inhomogeneousLittlewoodPaleySchwartz] at hg hgf
  exact ⟨g, hg, hgf.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg f))⟩

/-- **The enlarged Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in `j` and `p`.** For
every width `L`, there is `C ≥ 0`, depending only on `φ` and `L`, such that for every `1 ≤ p ≤ ∞`,
every `j`, and every `f ∈ Lᵖ`, the enlarged block `Δ'ⱼ f` is a function in `Lᵖ` with
`‖Δ'ⱼ f‖_p ≤ C ‖f‖_p`. -/
theorem exists_enlargedLittlewoodPaleyBlock_eq_and_norm_le [CompleteSpace F] (L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        enlargedLittlewoodPaleyBlock F φ L j (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨2 * L * max C₀ 0, by positivity, fun {p} _ j f ↦ ?_⟩
  choose g hg hgC using fun m ↦ hC₀ (p := p) m f
  refine ⟨∑ m ∈ Finset.Ico (j + 1 - L) (j + L), g m, ?_, ?_⟩
  · rw [enlargedLittlewoodPaleyBlock_eq_sum_Ico, _root_.sum_apply, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun m _ ↦ hg m
  · calc ‖∑ m ∈ Finset.Ico (j + 1 - L) (j + L), g m‖
        ≤ ∑ _ ∈ Finset.Ico (j + 1 - L) (j + L), max C₀ 0 * ‖f‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦
            (hgC m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)))
      _ = (Finset.Ico (j + 1 - L) (j + L)).card * (max C₀ 0 * ‖f‖) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * L * (max C₀ 0 * ‖f‖) := by
          gcongr
          exact_mod_cast Nat.card_Ico_add_le_two_mul_of_sub_le j L
            (Nat.sub_le_sub_right (Nat.le_add_right j 1) L)
      _ = 2 * L * max C₀ 0 * ‖f‖ := by ring

/-- **The low-pass truncations are bounded on `Lᵖ` uniformly in the scale.** For every
`1 ≤ p ≤ ∞`, every `R ≠ 0` and every `f ∈ Lᵖ`, the truncation `𝓕⁻ (φ (R⁻¹ ·) • 𝓕 f)` is a
function in `Lᵖ` with norm at most `‖𝓕⁻ φ‖₁ ‖f‖_p`: its kernel is an `L¹`-normalised dilate of
`𝓕⁻ φ`. -/
theorem exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {R : ℝ} (hR : R ≠ 0) (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E),
      fourierMultiplierCLM F (fun ξ ↦ (φ (R⁻¹ • ξ) : ℂ)) (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖f‖ := by
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le (φ.lowPassSchwartz hR) f
  rw [φ.coe_lowPassSchwartz, TauCeti.integral_norm_fourierInv_comp_smul (fun ξ ↦ (φ ξ : ℂ))
    (inv_ne_zero hR)] at hgf
  exact ⟨g, by rw [← hg, φ.coe_lowPassSchwartz], hgf⟩

/-- **The partial sums of the blocks are bounded on `Lᵖ` uniformly in `N`.** For every
`1 ≤ p ≤ ∞`, every `N` and every `f ∈ Lᵖ`, the truncation `S_N f = ∑_{j ≤ N} Δⱼ f` is a function
in `Lᵖ` with `‖S_N f‖_p ≤ ‖𝓕⁻ φ‖₁ ‖f‖_p`. -/
theorem exists_sum_littlewoodPaleyBlock_eq_and_norm_le [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (N : ℕ) (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E),
      ∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ j (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖f‖ := by
  rw [← _root_.sum_apply, sum_littlewoodPaleyBlock_range]
  exact exists_fourierMultiplierCLM_inv_smul_eq_and_norm_le φ (by positivity) f

open ContinuousLinearMap in
open scoped Convolution in
open ContinuousLinearMap in
open scoped Convolution in
/-- **The blocks of an `Lᵖ` function are convolutions.** For `1 ≤ p, q ≤ ∞` and `h ∈ Lᵖ`, if the
block `Δⱼ h` is an `Lᵠ` function `v` (as it is for `q = p`, by
`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`), then `v` is almost
everywhere the convolution `𝓕⁻ ψⱼ ⋆ h` of `h` with the kernel of `Δⱼ`. -/
theorem ae_eq_convolution_of_littlewoodPaleyBlock_eq [CompleteSpace F] (j : ℕ) {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {h : Lp F p (volume : Measure E)}
    {v : Lp F q (volume : Measure E)} (hv : littlewoodPaleyBlock F φ j (h : 𝓢'(E, F)) = v) :
    (v : E → F) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ⋆[lsmul ℂ ℂ] (h : E → F) := by
  rw [littlewoodPaleyBlock_apply, ← φ.coe_inhomogeneousLittlewoodPaleySchwartz] at hv
  rw [← φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  exact ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq hv

open ContinuousLinearMap in
open scoped Convolution in
/-- **The commutator of a Littlewood–Paley block with a Lipschitz function gains one
derivative.** There is `C`, depending only on `φ`, with the following property. Let
`1 ≤ p, q, r, s ≤ ∞`, let `f : E → ℂ` be `K`-Lipschitz, and let `g ∈ Lᵖ` be such that `f • g` is in
`Lᵠ`, represented by `fg`. If `u ∈ Lʳ` and `w ∈ Lˢ` are the functions `Δⱼ g` and `Δⱼ (f • g)`
(for instance with `r = p` and `s = q`, by
`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le`), then the commutator satisfies

`‖Δⱼ (f • g) - f • Δⱼ g‖_p ≤ C 2^{-j} K ‖g‖_p`.

Compared with the uniform bound `‖Δⱼ g‖_p ≤ C ‖g‖_p`, the commutator gains the factor `2^{-j}`,
one derivative at the frequency scale `2^j` of the block. The bound does not involve the size of
`f`, which may be unbounded, only its Lipschitz constant. -/
theorem exists_eLpNorm_littlewoodPaleyBlock_smul_sub_smul_le [CompleteSpace F] :
    ∃ C : ℝ≥0, ∀ {p q r s : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ s)]
      (j : ℕ) {f : E → ℂ} {K : ℝ≥0}, LipschitzWith K f →
      ∀ (g : Lp F p (volume : Measure E)) (fg : Lp F q (volume : Measure E))
        (u : Lp F r (volume : Measure E)) (w : Lp F s (volume : Measure E)),
        fg =ᵐ[volume] (fun x ↦ f x • g x) →
        littlewoodPaleyBlock F φ j (g : 𝓢'(E, F)) = u →
        littlewoodPaleyBlock F φ j (fg : 𝓢'(E, F)) = w →
        eLpNorm (fun x ↦ w x - f x • u x) p volume ≤
          C * (2 ^ j)⁻¹ * K * eLpNorm g p volume := by
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 1
  simp only [pow_one] at hC
  refine ⟨C, fun {p q r s} _ _ _ _ j f K hf g fg u w hfg hu hw ↦ ?_⟩
  -- The kernel `κ = 𝓕⁻ ψⱼ` of `Δⱼ` is a Schwartz function.
  set κ : 𝓢(E, ℂ) := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hκ : (κ : E → ℂ) = 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
    φ.coe_fourierInv_inhomogeneousLittlewoodPaleySchwartz j
  -- Both convolutions with `κ` exist everywhere, by Hölder's inequality, so the commutator is
  -- the integral of `MeasureTheory.eLpNorm_integral_sub_smul_smul_le`.
  have hex {e : ℝ≥0∞} (he : 1 ≤ e) {h : E → F} (hh : MemLp h e volume) (x : E) :
      ConvolutionExistsAt (κ : E → ℂ) h x (lsmul ℂ ℂ) volume :=
    have : ((1 - e⁻¹)⁻¹).HolderConjugate e := (ENNReal.HolderConjugate.inv_one_sub_inv' he).symm
    ConvolutionExists.of_memLp_memLp _ (κ.memLp (1 - e⁻¹)⁻¹) hh x
  have hae : (fun x ↦ w x - f x • u x) =ᵐ[volume]
      fun x ↦ ∫ t, (f (x - t) - f x) • κ t • g (x - t) := by
    filter_upwards [ae_eq_convolution_of_littlewoodPaleyBlock_eq φ j hu,
      ae_eq_convolution_of_littlewoodPaleyBlock_eq φ j hw] with x hux hwx
    rw [hux, hwx, ← hκ, convolution_congr (lsmul ℂ ℂ) (Filter.EventuallyEq.refl _ _) hfg,
      convolution_smul_sub_smul_convolution (hex (Fact.out : 1 ≤ q) ((Lp.memLp fg).ae_eq hfg) x)
        (hex (Fact.out : 1 ≤ p) (Lp.memLp g) x)]
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


section L2

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Littlewood–Paley blocks of an `L²` function are square summable.** There is `C ≥ 0`,
depending only on `φ`, such that the blocks `Δⱼ f` of every `f ∈ L²` are `L²` functions with
`∑ⱼ ‖Δⱼ f‖² ≤ C ‖f‖²`. -/
theorem exists_littlewoodPaleyBlock_eq_and_sum_norm_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp H 2 (volume : Measure E), ∃ g : ℕ → Lp H 2 (volume : Measure E),
      (∀ j, littlewoodPaleyBlock H φ j (f : 𝓢'(E, H)) = g j) ∧
        ∀ t : Finset ℕ, ∑ j ∈ t, ‖g j‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := TauCeti.exists_sum_norm_fourierMultiplierCLM_sq_le (F := H) φ
  have hm : ∀ j, MemLp (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ∞
      (volume : Measure E) := fun j ↦
    ((φ.contDiff_inhomogeneousLittlewoodPaley j (n := 0)).continuous.memLp_top_of_hasCompactSupport
      (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j) volume).ofReal
  refine ⟨C, hC0, fun f ↦ ⟨fun j ↦ Lp.fourierMultiplierCLM H ((hm j).toLp _) f, fun j ↦ ?_,
    hC _ (fun j ↦ (hm j).coeFn_toLp) f⟩⟩
  rw [littlewoodPaleyBlock_apply]
  exact Lp.fourierMultiplierCLM_toTemperedDistribution_eq f
    (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j) (hm j)

/-- **Almost orthogonality of `L²` blocks.** Let `Δ` and `Δ'` be the Littlewood–Paley blocks built
from `φ` and `φ'`. There is `L`, depending only on `φ` and `φ'`, such that if the block `Δᵢ u` of a
tempered distribution `u` is an `L²` function `f` and the block `Δ'ₖ v` of a tempered distribution
`v` is an `L²` function `g`, then `⟪f, g⟫ = 0` whenever `i + L ≤ k`. -/
theorem exists_inner_eq_zero_of_littlewoodPaleyBlock_eq (φ' : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ {u v : 𝓢'(E, H)} {i k : ℕ} {f g : Lp H 2 (volume : Measure E)},
      littlewoodPaleyBlock H φ i u = f → littlewoodPaleyBlock H φ' k v = g → i + L ≤ k →
        ⟪f, g⟫_ℂ = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  obtain ⟨L', hL'⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ'
  refine ⟨L + L', fun {u v i k f g} hf hg hik ↦ ?_⟩
  -- The enlarged cutoff `Ψᵢ` is `1` on the support of `ψᵢ` and vanishes on the support of `ψ'ₖ`
  -- for `k ≥ i + L + L'`.
  have hΨ : ∀ ξ, φ.enlargedLittlewoodPaley L i ξ * φ'.inhomogeneousLittlewoodPaley k ξ = 0 := by
    intro ξ
    rw [φ.enlargedLittlewoodPaley_apply, Finset.sum_mul]
    exact Finset.sum_eq_zero fun l hl ↦ hL' l k (by rw [Finset.mem_Ico] at hl; omega) ξ
  have hgrowth : (fun ξ ↦ (φ.enlargedLittlewoodPaley L i ξ : ℂ)).HasTemperateGrowth :=
    ((φ.hasCompactSupport_enlargedLittlewoodPaley L i).comp_left
      Complex.ofReal_zero).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp (φ.contDiff_enlargedLittlewoodPaley L i))
  have hM : MemLp (fun ξ ↦ (φ.enlargedLittlewoodPaley L i ξ : ℂ)) ∞ (volume : Measure E) :=
    ((φ.contDiff_enlargedLittlewoodPaley L i (n := 0)).continuous.memLp_top_of_hasCompactSupport
      (φ.hasCompactSupport_enlargedLittlewoodPaley L i) volume).ofReal
  set T : Lp H 2 (volume : Measure E) →L[ℂ] Lp H 2 (volume : Measure E) :=
    Lp.fourierMultiplierCLM H (hM.toLp _)
  -- `Ψᵢ` is real, so `T` is self-adjoint.
  have hTs : IsSelfAdjoint T :=
    Lp.isSelfAdjoint_fourierMultiplierCLM (Lp.star_eq_self_of_ae_eq_ofReal hM.coeFn_toLp)
  -- `T` applied to the `L²` block `Δ''ₖ w = h` is the multiplier by `ψ''ₖ Ψᵢ` applied to `w`.
  have hT : ∀ (φ'' : ContDiffBump (0 : E)) (k : ℕ) (w : 𝓢'(E, H)) (h : Lp H 2 (volume : Measure E)),
      littlewoodPaleyBlock H φ'' k w = h → (T h : 𝓢'(E, H)) = fourierMultiplierCLM H (fun ξ ↦
        ((φ''.inhomogeneousLittlewoodPaley k ξ * φ.enlargedLittlewoodPaley L i ξ : ℝ) : ℂ)) w := by
    intro φ'' k w h hh
    rw [← Lp.fourierMultiplierCLM_toTemperedDistribution_eq _ hgrowth hM, ← hh,
      littlewoodPaleyBlock_apply, fourierMultiplierCLM_fourierMultiplierCLM_apply
        (φ''.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley k) hgrowth]
    congr 2
    funext ξ
    simp
  have hTf : T f = f := Lp.toTemperedDistribution_injective <| by
    simp only [hT φ i u f hf, ← hf, littlewoodPaleyBlock_apply]
    congr 2
    funext ξ
    rw [mul_comm, φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]
  have hTg : T g = 0 := Lp.toTemperedDistribution_injective <| by
    simp only [hT φ' k v g hg, mul_comm _ (φ.enlargedLittlewoodPaley L i _), hΨ,
      Complex.ofReal_zero, Lp.toTemperedDistribution_zero]
    simp [fourierMultiplierCLM_const]
  rw [← hTf, ← hTs.adjoint_eq, ContinuousLinearMap.adjoint_inner_left, hTg, inner_zero_right]

/-- **A tempered distribution with square-summable `L²` blocks is an `L²` function.** There is
`C`, depending only on `φ`, such that if every block `Δⱼ v` of `v ∈ 𝓢'` is an `L²` function `gⱼ`
with `∑ⱼ ‖gⱼ‖² < ∞`, then `v = ∑ⱼ gⱼ` is an `L²` function `f` with `‖f‖² ≤ C ∑ⱼ ‖gⱼ‖²`. -/
theorem exists_eq_and_norm_sq_le_of_littlewoodPaleyBlock_eq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : 𝓢'(E, H)) (g : ℕ → Lp H 2 (volume : Measure E)),
      (∀ j, littlewoodPaleyBlock H φ j v = g j) → Summable (fun j ↦ ‖g j‖ ^ 2) →
        ∃ f : Lp H 2 (volume : Measure E), v = f ∧ ‖f‖ ^ 2 ≤ C * ∑' j, ‖g j‖ ^ 2 := by
  obtain ⟨L, hL⟩ := exists_inner_eq_zero_of_littlewoodPaleyBlock_eq (H := H) φ φ
  refine ⟨L, by positivity, fun v g hg hsq ↦ ?_⟩
  have hv : ∀ i j, i + L ≤ j → ⟪g i, g j⟫_ℂ = 0 := fun i j ↦ hL (hg i) (hg j)
  refine ⟨∑' j, g j, ?_, TauCeti.norm_tsum_sq_le_mul_tsum_norm_sq_of_inner_eq_zero_nat hv hsq⟩
  -- In `𝓢'`, the partial sums `∑_{j < N} gⱼ` tend both to `v` and to `∑' j, gⱼ`.
  have h1 := tendsto_sum_littlewoodPaleyBlock φ v
  simp_rw [hg] at h1
  refine tendsto_nhds_unique h1 ?_
  have h2 := ((Lp.toTemperedDistributionCLM H (volume : Measure E) 2).continuous.tendsto _).comp
    (TauCeti.summable_of_inner_eq_zero_nat hv hsq).hasSum.tendsto_sum_nat
  simpa [Function.comp_def, map_sum] using h2

end L2

end Lp

end TemperedDistribution
