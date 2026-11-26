/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.Algebra.BigOperators.Finset.BoundedOverlap
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Function.Lp.One
import TauCeti.MeasureTheory.Function.Lp.SequenceValued
import TauCeti.MeasureTheory.Function.Lp.SquareFunction
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace

/-!
# The Littlewood–Paley square function theorem

Let `V` be a finite-dimensional real inner product space and let `φ` be a smooth bump function
on `V`. Two families of Littlewood–Paley cutoffs are built from `φ`: the inhomogeneous
partition `ψ₀ = φ, ψ₁, ψ₂, …` (`ContDiffBump.inhomogeneousLittlewoodPaley`), which sums to `1`
everywhere, and the homogeneous cutoffs `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`, `j ∈ ℤ`
(`ContDiffBump.littlewoodPaley`), which sum to `1` away from the origin. The Littlewood–Paley
blocks `Δⱼ` (respectively `Pⱼ`) are the `L²` Fourier multipliers with these symbols, and the
**Littlewood–Paley square function** of `f` is

`S f = (∑ⱼ ‖Δⱼ f‖²)^{1/2}`, respectively `S f = (∑_{j ∈ ℤ} ‖Pⱼ f‖²)^{1/2}`.

This file proves the Littlewood–Paley theorem for both families: for a complex Hilbert space `F`
and `1 < p < ∞` there is a constant `C`, depending on `φ`, `p` and `F`, with

`‖S f‖_p ≤ C ‖f‖_p` and `‖f‖_p ≤ C ‖S f‖_p`

for every `f ∈ L²(V, F)` (`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le` and
`TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow`), and the same for
the homogeneous square function
(`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow_le` and
`TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow`).
Only the reverse homogeneous inequality assumes `V` nontrivial: in dimension `0` every homogeneous
cutoff vanishes, and so does the homogeneous square function. Neither side is assumed finite, so
`f ∈ Lᵖ` exactly when `S f ∈ Lᵖ`: in every dimension for the inhomogeneous square function, and
for nontrivial `V` for the homogeneous one. The constants of the homogeneous inequalities do not
see any scale, which is what estimates with homogeneous Sobolev and Besov norms, such as the
Strichartz estimates for the wave equation, need.

At `p = 2` the first inequality is stated for finite sums of inhomogeneous blocks as
`TauCeti.exists_sum_norm_fourierMultiplierCLM_sq_le`: `∑_{j ∈ s} ‖Δⱼ f‖₂² ≤ L ‖f‖₂²`.

## The argument for `‖S f‖_p ≤ C ‖f‖_p`

Both families are *dyadic*: the pieces are smooth, the `i`-th one is supported in a ball of radius
`2 ^ e i` for an injective `e` with values in `ℤ`, its derivatives of order `k` are
`O(2^{-k e i})`, and the sums of squares of the pieces are bounded. The proof works for any dyadic
family, uniformly over its finite sets `s` of indices, and passes to the full square sum by monotone
convergence (`MeasureTheory.eLpNorm_iSup_eq_iSup_eLpNorm`).

The truncation `f ↦ (Δᵢ f)_{i ∈ s}` (`MeasureTheory.Lp.lpPi`) is a bounded operator
`L²(V, F) → L²(V, ℓ²(F))` and the inequality is the Calderón–Zygmund theorem for it, applied
uniformly in `s` (`TauCeti.exists_eLpNorm_le_of_hormander`).

* **`L²` bound.** Write `T` for the truncation; its adjoint is `T† (gᵢ) = ∑ᵢ Δᵢ gᵢ`. The operator
  `T† T = ∑_{i ∈ s} Δᵢ²` on `L²(V, F)` is the multiplier with symbol `∑_{i ∈ s} ψᵢ²`, which is
  bounded independently of `s`.
* **Kernel.** Both the truncation and its adjoint are given by kernels dominated by differences
  of the `ℓ²`-valued Schwartz function `K_s z = ∑_{i ∈ s} (𝓕⁻ ψᵢ) z eᵢ`, the inverse Fourier
  transform of `ξ ↦ ∑_{i ∈ s} ψᵢ ξ eᵢ`.
* **Hörmander's condition.** The pieces `ξ ↦ ψᵢ ξ eᵢ` are band-limited at the scales `2 ^ e i`
  with derivatives `O(2^{-k e i})`, so `K_s` satisfies Hörmander's condition
  `∫_{‖x‖ > 2 ‖h‖} ‖K_s (x - h) - K_s x‖ dx ≤ B` uniformly in `s`
  (`SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le`).

The Calderón–Zygmund constant must not depend on `s`, so the vectors `(Δᵢ f)_{i ∈ s}` are placed
in the single Hilbert space `ℓ²(F)` of all indices rather than in a space depending on `s`.

## The argument for `‖f‖_p ≤ C ‖S f‖_p`

The reverse inequality follows from the first one at the conjugate exponent `q` by duality
(`MeasureTheory.Lp.exists_eLpNorm_le_one_and_lt_re_inner`). The pieces
`ψⱼ` and `ψₖ` have disjoint supports once `|j - k| ≥ L`
(`ContDiffBump.exists_inhomogeneousLittlewoodPaley_mul_eq_zero`,
`ContDiffBump.exists_littlewoodPaley_mul_eq_zero`), so `∑_{|k - j| < L} ψₖ ψⱼ = ψⱼ`
(`ContDiffBump.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley`,
`ContDiffBump.sum_littlewoodPaley_mul_littlewoodPaley`), and the blocks are self-adjoint.
Hence, for `f, g ∈ L²(V, F)` and a finite set `t` of indices,

`⟪∑_{j ∈ t} Δⱼ f, g⟫ = ∑_{j ∈ t} ∑_{|k - j| < L} ⟪Δⱼ f, Δₖ g⟫`,

which Cauchy–Schwarz for the banded double sum (`ENNReal.tsum_sum_mul_le_of_card_le`) bounds
by `2 L ∫ S f · S g` (`TauCeti.enorm_inner_sum_le_mul_lintegral_tsum_enorm_sq_rpow`). The partial
sums `∑_{j ∈ t} Δⱼ f` converge to `f` in `L²` along suitable finite sets `t`
(`MeasureTheory.Lp.tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley`,
`ContDiffBump.tendsto_sum_fourierMultiplierCLM_littlewoodPaley`, both instances of
`MeasureTheory.Lp.tendsto_sum_fourierMultiplierCLM_of_tendsto`), and Hölder's inequality and
the first inequality at the exponent `q` give `|⟪f, g⟫| ≤ 2 L C_q ‖S f‖_p ‖g‖_q`. This duality
argument holds for any family of operators on `L²` with these properties
(`TauCeti.eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow`).

## Homogeneous blocks on `Lᵖ`

The last section bounds a single homogeneous block `Pⱼ`, whose symbol is the dilate
`ψ₀ (2^{-j} ·)` (`ContDiffBump.ae_eq_littlewoodPaley_zero_comp_smul`), on every `Lᵖ`,
`1 ≤ p ≤ ∞`, uniformly in the scale: `‖Pⱼ f‖_p ≤ ‖𝓕⁻ ψ₀‖₁ ‖f‖_p` for `f ∈ L²`
(`ContDiffBump.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le`), and `‖Pⱼ‖ ≤ 1` on `L²`
(`ContDiffBump.norm_fourierMultiplierCLM_littlewoodPaley_le`). In dimension `0` every block
vanishes (`ContDiffBump.fourierMultiplierCLM_littlewoodPaley_eq_zero`). The blocks near `Pⱼ`
reproduce it (`ContDiffBump.sum_fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley`). On a
nontrivial `V`, together with the reconstruction `∑_{-N < j ≤ N} Pⱼ f → f`
(`ContDiffBump.tendsto_sum_fourierMultiplierCLM_littlewoodPaley`), this gives the duality of the
dyadic `ℓ¹` and `ℓ^∞` norms: if `‖Pₖ g‖₂ ≤ A 2^{kγ}` for every `k`, then
`|⟪f, g⟫| ≤ K A ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂` (`ContDiffBump.exists_enorm_inner_le_mul_tsum`), the pairing of
the homogeneous Besov spaces `\dot B^γ_{2,1}` and `\dot B^{-γ}_{2,∞}`. Since the `Lʳ` seminorm
is lower semicontinuous on `L²`, the reconstruction also gives `‖A f‖_r ≤ ∑ⱼ ‖A Pⱼ f‖_r` for
every bounded operator `A` on `L²` and `1 ≤ r ≤ ∞`
(`ContDiffBump.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM`).

Blocks `L` or more apart, for the overlap length `L` of the cutoffs, compose to zero
(`ContDiffBump.fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley_eq_zero`), so a nonzero
block is a nonzero datum with finitely many nonzero blocks
(`ContDiffBump.exists_ne_zero_forall_notMem_fourierMultiplierCLM_eq_zero`). The blocks under the
dyadic dilations of `L²` are in `TauCeti.Analysis.Fourier.LittlewoodPaley.Dilation`.

## Dyadic multipliers and squared blocks

For a symbol `a` smooth and nonvanishing away from the origin, the dyadic dilates
`σ (2^{-j} ·)` of one Schwartz function `σ` invert `a (2^{-j} ·)` on the support of every `ψⱼ`;
this is `1 / a` when `a` is invariant under `ξ ↦ 2 ξ`, as for `Ψ`
(`ContDiffBump.exists_eqOn_inv_of_contDiffOn`, `ContDiffBump.dyadicDilate`,
`ContDiffBump.dyadicDilate_apply_of_littlewoodPaley_ne_zero`). The kernels of the corresponding
multipliers are `L¹`-normalised dilates of `𝓕⁻ σ`, so the multipliers are bounded on every `Lᵖ`
and in every mixed norm uniformly in `j` (`ContDiffBump.eLpNorm_dyadicMultiplier_le`,
`ContDiffBump.eLpNorm_eLpNorm_dyadicMultiplier_le`). For the sum of squares `Ψ = ∑ⱼ ψⱼ²`
(`ContDiffBump.sumSqLittlewoodPaley`) the inverting multipliers `Qₗ` reassemble a block from
squared blocks: `Pₗ = ∑_{|j - l| < L} Pⱼ Pⱼ Qₗ Pₗ`
(`ContDiffBump.sum_fourierMultiplierCLM_fourierMultiplierCLM_dyadicMultiplier_invSumSq`).

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Theorem 6.1.2 and Section 5.6
  (vector-valued inequalities).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  Section 1.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap ContDiff LineDeriv InnerProductSpace
  Topology
open FourierTransform MeasureTheory Metric Filter ContinuousLinearMap Module

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace LittlewoodPaleySquare

variable {ι : Type*}

/-- A **dyadic family** of symbols: real smooth functions `ψ i`, given as the complex Schwartz
functions `σ i`, such that `ψ i` vanishes outside the ball of radius `2 ^ e i` for an injective
`e : ι → ℤ`, its derivatives of order `k` are bounded by `B_k / (2 ^ e i) ^ k` uniformly in `i`, and
the sums of squares `∑ᵢ ψ i ξ ²` are bounded uniformly in `ξ` and in the finite set of indices.
These are the hypotheses under which the square function of the Fourier multipliers with these
symbols is bounded on `Lᵖ`. -/
private structure IsDyadic (ψ : ι → V → ℝ) (σ : ι → 𝓢(V, ℂ)) (e : ι → ℤ) : Prop where
  apply_eq : ∀ i ξ, σ i ξ = ψ i ξ
  contDiff : ∀ i, ContDiff ℝ ∞ (ψ i)
  injective : Function.Injective e
  norm_le : ∀ i ξ, ψ i ξ ≠ 0 → ‖ξ‖ ≤ 2 ^ e i
  deriv : ∀ k : ℕ, ∃ B, 0 ≤ B ∧ ∀ i ξ, ‖iteratedFDeriv ℝ k (ψ i) ξ‖ ≤ B / (2 ^ e i) ^ k
  sum_sq : ∃ L, 0 ≤ L ∧ ∀ (s : Finset ι) (ξ : V), ∑ i ∈ s, ψ i ξ ^ 2 ≤ L

variable {ψ : ι → V → ℝ} {σ : ι → 𝓢(V, ℂ)} {e : ι → ℤ}

omit [FiniteDimensional ℝ V] in
/-- A family of symbols supported in the balls of radius `2 ^ a i * R` for an injective
`a : ι → ℤ`, with derivatives of order `k` bounded by `B_k / (2 ^ a i) ^ k` uniformly in `i` and
with bounded sums of squares, is a dyadic family: rescaling `a` by a power of `2` above `R` absorbs
the radius. -/
private theorem IsDyadic.of_scale {a : ι → ℤ} (ha : Function.Injective a)
    (hσ : ∀ i ξ, σ i ξ = ψ i ξ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) {R : ℝ}
    (hR : ∀ i ξ, ψ i ξ ≠ 0 → ‖ξ‖ < 2 ^ a i * R)
    (hderiv : ∀ k : ℕ, ∃ B, 0 ≤ B ∧ ∀ i ξ, ‖iteratedFDeriv ℝ k (ψ i) ξ‖ ≤ B / (2 ^ a i) ^ k)
    (hsum : ∃ L : ℕ, ∀ (s : Finset ι) (ξ : V), ∑ i ∈ s, ψ i ξ ^ 2 ≤ L) :
    ∃ e : ι → ℤ, IsDyadic ψ σ e := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R (one_lt_two (α := ℝ))
  refine ⟨fun i ↦ a i + m, ⟨hσ, hψ, fun i j hij ↦ ha (by simpa using hij), fun i ξ hξ ↦ ?_,
    fun k ↦ ?_, ?_⟩⟩
  · rw [zpow_add₀ two_ne_zero, zpow_natCast]
    exact (hR i ξ hξ).le.trans (mul_le_mul_of_nonneg_left hm.le (by positivity))
  · obtain ⟨B, hB0, hB⟩ := hderiv k
    refine ⟨B * (2 ^ m) ^ k, by positivity, fun i ξ ↦ (hB i ξ).trans_eq ?_⟩
    rw [zpow_add₀ two_ne_zero, zpow_natCast, mul_pow]
    field_simp
  · obtain ⟨L, hL⟩ := hsum
    exact ⟨L, Nat.cast_nonneg L, hL⟩

variable (V ι) in
/-- Schwartz functions with values in `ℓ²(ι, ℂ)`, with the real structure induced by the complex
one, which is the structure the Fourier transform on Schwartz space is stated for. -/
private abbrev L2Schwartz : Type _ :=
  @SchwartzMap V (lp (fun _ : ι ↦ ℂ) 2) _ _ _ NormedSpace.complexToReal

variable (σ) in
/-- The `ℓ²`-valued Schwartz function `ξ ↦ ψᵢ ξ eᵢ`. -/
private def vecSymbol [DecidableEq ι] (i : ι) : L2Schwartz V ι :=
  SchwartzMap.postcompCLM (lp.singleContinuousLinearMap ℂ (fun _ : ι ↦ ℂ) 2 i) (σ i)

omit [FiniteDimensional ℝ V] in
private theorem vecSymbol_apply [DecidableEq ι] (i : ι) (ξ : V) :
    vecSymbol σ i ξ = lp.single 2 i (σ i ξ) :=
  -- This is `SchwartzMap.postcompCLM_apply`, which holds by `rfl`. It does not rewrite here: the
  -- real structure of `L2Schwartz V ι` is not reducibly the one `postcompCLM` produces.
  rfl

omit [FiniteDimensional ℝ V] in
/-- The `k`-th derivative of `ξ ↦ ψᵢ ξ eᵢ` is bounded by that of `ψᵢ`. -/
private theorem norm_iteratedFDeriv_vecSymbol_le [DecidableEq ι] (hP : IsDyadic ψ σ e) (i : ι)
    (k : ℕ) (ξ : V) :
    ‖iteratedFDeriv ℝ k (vecSymbol σ i : V → lp (fun _ : ι ↦ ℂ) 2) ξ‖ ≤
      ‖iteratedFDeriv ℝ k (ψ i) ξ‖ := by
  set L : ℝ →L[ℝ] lp (fun _ : ι ↦ ℂ) 2 :=
    (lp.singleContinuousLinearMap ℝ (fun _ : ι ↦ ℂ) 2 i).comp Complex.ofRealCLM
  have hL : ‖L‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun r ↦ by simp [L]
  have hfun : (vecSymbol σ i : V → lp (fun _ : ι ↦ ℂ) 2) = L ∘ ψ i := funext fun ξ ↦ by
    simp [vecSymbol_apply, L, hP.apply_eq]
  rw [hfun]
  refine (L.norm_iteratedFDeriv_comp_left (hP.contDiff i).contDiffAt (mod_cast le_top)).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) hL

omit [FiniteDimensional ℝ V] in
/-- The function `ξ ↦ ψᵢ ξ eᵢ` is supported in the ball of radius `2 ^ e i`. -/
private theorem support_vecSymbol_subset [DecidableEq ι] (hP : IsDyadic ψ σ e) (i : ι) :
    Function.support (vecSymbol σ i) ⊆ closedBall 0 (2 ^ e i) := by
  intro ξ hξ
  rw [Function.mem_support, vecSymbol_apply, hP.apply_eq] at hξ
  exact mem_closedBall_zero_iff.2 (hP.norm_le i ξ fun h0 ↦ hξ (by simp [h0]))

omit [FiniteDimensional ℝ V] in
/-- A derivative bound `‖D^k ψᵢ‖ ≤ B 2^{-k e i}` gives the same bound for the iterated directional
derivatives of `ξ ↦ ψᵢ ξ eᵢ` along an orthonormal basis. -/
private theorem norm_iterate_lineDerivOp_vecSymbol_le [DecidableEq ι] (hP : IsDyadic ψ σ e)
    {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ V) {k : ℕ} {B : ℝ}
    (hB : ∀ (i : ι) (ξ : V), ‖iteratedFDeriv ℝ k (ψ i) ξ‖ ≤ B / (2 ^ e i) ^ k)
    (i : ι) (i' : κ) (ξ : V) :
    ‖(∂_{b i'})^[k] (vecSymbol σ i) ξ‖ ≤ B / (2 ^ e i) ^ k := by
  rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  refine ((iteratedFDeriv ℝ k (vecSymbol σ i : V → lp (fun _ : ι ↦ ℂ) 2) ξ).le_opNorm
    _).trans ?_
  simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one]
  exact (norm_iteratedFDeriv_vecSymbol_le hP i k ξ).trans (hB i ξ)

variable [MeasurableSpace V] [BorelSpace V]

variable (σ) in
/-- The `ℓ²`-valued kernel `z ↦ ∑_{i ∈ s} (𝓕⁻ ψᵢ) z eᵢ` of the truncated square function. -/
private def kernel [DecidableEq ι] (s : Finset ι) : L2Schwartz V ι :=
  𝓕⁻ (∑ i ∈ s, vecSymbol σ i)

private theorem kernel_apply [DecidableEq ι] (s : Finset ι) (z : V) :
    kernel σ s z = ∑ i ∈ s, lp.single 2 i (𝓕⁻ (σ i) z) := by
  rw [kernel, FourierTransform.fourierInv_sum, sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact SchwartzMap.fourierInv_postcompCLM_apply _ (σ i) z

/-- **Hörmander's condition for the `ℓ²`-valued kernels**, uniformly in the truncation:
`∫_{‖x‖ > 2 ‖h‖} ‖K_s (x - h) - K_s x‖ dx ≤ B`. -/
private theorem exists_setIntegral_norm_kernel_sub_sub_le [DecidableEq ι] (hP : IsDyadic ψ σ e) :
    ∃ B, 0 ≤ B ∧ ∀ (s : Finset ι) (h : V),
      ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖kernel σ s (x - h) - kernel σ s x‖ ≤ B := by
  set N := finrank ℝ V + 1
  have hN : finrank ℝ V < 2 * N := by omega
  obtain ⟨C, hC, hK⟩ := SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le
    (H := lp (fun _ : ι ↦ ℂ) 2) (stdOrthonormalBasis ℝ V) hN
  choose B hB0 hB using hP.deriv
  set A := ∑ k ∈ Finset.range (N + 1), B k
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ ↦ hB0 k
  refine ⟨C * A, mul_nonneg hC hA, fun s h ↦ ?_⟩
  -- Index the pieces by `ℤ` through the injective map `e`.
  set σ' : ℤ → L2Schwartz V ι := Function.extend e (vecSymbol σ) 0
  have hσ' : ∀ i, σ' (e i) = vecSymbol σ i := hP.injective.extend_apply _ _
  set t : Finset ℤ := s.map ⟨e, hP.injective⟩
  have hsum : ∑ z ∈ t, σ' z = ∑ i ∈ s, vecSymbol σ i := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ ↦ hσ' i
  have hmem : ∀ z ∈ t, ∃ i, z = e i ∧ σ' z = vecSymbol σ i := fun z hz ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hz
    exact ⟨i, rfl, hσ' i⟩
  have hsupp : ∀ z ∈ t, Function.support (σ' z) ⊆ closedBall 0 (2 ^ z) := fun z hz ↦ by
    obtain ⟨i, rfl, hσi⟩ := hmem z hz
    rw [hσi]
    exact support_vecSymbol_subset hP i
  have hderiv : ∀ z ∈ t, ∀ k ≤ N, ∀ i' ξ,
      ‖(∂_{stdOrthonormalBasis ℝ V i'})^[k] (σ' z) ξ‖ ≤ A / (2 ^ z) ^ k := by
    intro z hz k hk i' ξ
    obtain ⟨i, rfl, hσi⟩ := hmem z hz
    rw [hσi]
    refine (norm_iterate_lineDerivOp_vecSymbol_le hP _ (hB k) i i' ξ).trans ?_
    exact div_le_div_of_nonneg_right (Finset.single_le_sum (f := B) (fun k _ ↦ hB0 k)
      (Finset.mem_range.2 (by omega))) (by positivity)
  have := hK σ' t hA hsupp hderiv h
  rwa [hsum] at this

/-! ### The truncated square function as a vector-valued operator -/

variable (σ) in
/-- The kernel `v ↦ ((𝓕⁻ ψᵢ) (x - y) v)ᵢ` of `Lp.lpPi 2 s (block σ)`. -/
private def sqKernel [DecidableEq ι] (s : Finset ι) (x y : V) : F →L[ℝ] lp (fun _ : ι ↦ F) 2 :=
  ∑ i ∈ s,
    (lp.singleContinuousLinearMap ℝ (fun _ : ι ↦ F) 2 i).comp (lsmul ℝ ℂ (𝓕⁻ (σ i) (x - y)))

variable (σ) in
/-- The kernel `(wᵢ) ↦ ∑ᵢ (𝓕⁻ ψᵢ) (x - y) wᵢ` of `sqFunAdj σ s`. -/
private def sqKernelAdj (s : Finset ι) (x y : V) : lp (fun _ : ι ↦ F) 2 →L[ℝ] F :=
  ∑ i ∈ s, (lsmul ℝ ℂ (𝓕⁻ (σ i) (x - y))).comp (lp.evalCLM ℝ (fun _ : ι ↦ F) 2 i)

private theorem kernel_sub_kernel [DecidableEq ι] (s : Finset ι) (z z' : V) :
    kernel σ s z - kernel σ s z' =
      ∑ i ∈ s, lp.single 2 i (𝓕⁻ (σ i) z - 𝓕⁻ (σ i) z') := by
  simp only [kernel_apply, ← Finset.sum_sub_distrib, lp.single_sub]

private theorem norm_sqKernel_sub_le [DecidableEq ι] (s : Finset ι) (x y y' : V) :
    ‖sqKernel (F := F) σ s x y - sqKernel σ s x y'‖ ≤
      ‖kernel σ s (x - y) - kernel σ s (x - y')‖ := by
  rw [kernel_sub_kernel, sqKernel, sqKernel, ← Finset.sum_sub_distrib]
  simp_rw [← comp_sub, ← map_sub]
  exact lp.norm_sum_single_comp_lsmul_le _ _

private theorem norm_sqKernelAdj_sub_le [DecidableEq ι] (s : Finset ι) (x y y' : V) :
    ‖sqKernelAdj (F := F) σ s x y - sqKernelAdj σ s x y'‖ ≤
      ‖kernel σ s (x - y) - kernel σ s (x - y')‖ := by
  rw [kernel_sub_kernel, sqKernelAdj, sqKernelAdj, ← Finset.sum_sub_distrib]
  simp_rw [← sub_comp, ← map_sub]
  exact lp.norm_sum_lsmul_comp_evalCLM_le _ _

private theorem stronglyMeasurable_sqKernel [DecidableEq ι] (s : Finset ι) :
    StronglyMeasurable (Function.uncurry (sqKernel (F := F) σ s)) :=
  Finset.stronglyMeasurable_fun_sum s
    (f := fun i (p : V × V) ↦ (lp.singleContinuousLinearMap ℝ (fun _ : ι ↦ F) 2 i).comp
      (lsmul ℝ ℂ (𝓕⁻ (σ i) (p.1 - p.2)))) fun i _ ↦
    (continuous_const.clm_comp (lsmul ℝ ℂ).continuous).comp_stronglyMeasurable
      ((𝓕⁻ (σ i)).continuous.comp continuous_sub).stronglyMeasurable

private theorem stronglyMeasurable_sqKernelAdj (s : Finset ι) :
    StronglyMeasurable (Function.uncurry (sqKernelAdj (F := F) σ s)) :=
  Finset.stronglyMeasurable_fun_sum s
    (f := fun i (p : V × V) ↦
      (lsmul ℝ ℂ (𝓕⁻ (σ i) (p.1 - p.2))).comp (lp.evalCLM ℝ (fun _ : ι ↦ F) 2 i)) fun i _ ↦
    ((lsmul ℝ ℂ).continuous.clm_comp continuous_const).comp_stronglyMeasurable
      ((𝓕⁻ (σ i)).continuous.comp continuous_sub).stronglyMeasurable

variable [CompleteSpace F]

variable (σ) in
/-- The block `Δᵢ` with symbol `ψᵢ` on `L²(V, F)`, as a real-linear operator. -/
private def block (i : ι) : Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  (Lp.fourierMultiplierCLM F ((σ i).toLp ∞)).restrictScalars ℝ

private theorem block_apply (i : ι) (f : Lp F 2 (volume : Measure V)) :
    block σ i f = Lp.fourierMultiplierCLM F ((σ i).toLp ∞) f :=
  (rfl)

private theorem coeFn_toLp_symbol (hP : IsDyadic ψ σ e) (i : ι) :
    (σ i).toLp ∞ (volume : Measure V) =ᵐ[volume] fun ξ ↦ (ψ i ξ : ℂ) :=
  (σ i).coeFn_toLp ∞ volume |>.mono fun ξ h ↦ by rw [h, hP.apply_eq]

/-- Any symbol in `L^∞` almost everywhere equal to `ψᵢ` is `(σ i).toLp ∞`. -/
private theorem eq_toLp_symbol (hP : IsDyadic ψ σ e) {i : ι} {m : Lp ℂ ∞ (volume : Measure V)}
    (hm : m =ᵐ[volume] fun ξ ↦ (ψ i ξ : ℂ)) : m = (σ i).toLp ∞ volume :=
  Lp.ext (hm.trans (coeFn_toLp_symbol hP i).symm)

variable (σ) in
/-- The operator `(gᵢ) ↦ ∑_{i ∈ s} Δᵢ gᵢ`, the adjoint of `Lp.lpPi 2 s (block σ)`. -/
private def sqFunAdj (s : Finset ι) :
    Lp (lp (fun _ : ι ↦ F) 2) 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  ∑ i ∈ s, block σ i ∘L (lp.evalCLM ℝ (fun _ : ι ↦ F) 2 i).compLpL 2 volume

/-- The block `Δᵢ` is convolution with `𝓕⁻ ψᵢ`. -/
private theorem coeFn_block (i : ι) (f : Lp F 2 (volume : Measure V)) :
    block σ i f =ᵐ[volume] fun x ↦ ∫ z, 𝓕⁻ (σ i) (x - z) • f z :=
  (σ i).coeFn_fourierMultiplierCLM_toLp f

private theorem ae_sqFun_eq_integral [DecidableEq ι] (s : Finset ι)
    (f : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, Lp.lpPi 2 s (block σ) f x = ∫ z, sqKernel σ s x z (f z) := by
  filter_upwards [Lp.coeFn_lpPi 2 s (block σ) f,
    s.eventually_all.2 fun i _ ↦ coeFn_block (σ := σ) i f] with x hx hix
  rw [hx]
  simp only [sqKernel, sum_apply, coe_comp, Function.comp_apply, lsmul_apply,
    lp.singleContinuousLinearMap_apply]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hix i hi]
    exact ((lp.singleContinuousLinearMap ℝ (fun _ : ι ↦ F) 2 i).integral_comp_comm
      ((𝓕⁻ (σ i)).integrable_sub_smul one_le_two (Lp.memLp f) x)).symm
  · exact (lp.singleContinuousLinearMap ℝ (fun _ : ι ↦ F) 2 i).integrable_comp
      ((𝓕⁻ (σ i)).integrable_sub_smul one_le_two (Lp.memLp f) x)

private theorem ae_sqFunAdj_eq_integral (s : Finset ι)
    (g : Lp (lp (fun _ : ι ↦ F) 2) 2 (volume : Measure V)) :
    ∀ᵐ x, sqFunAdj σ s g x = ∫ z, sqKernelAdj σ s x z (g z) := by
  set u : ι → Lp F 2 (volume : Measure V) := fun i ↦
    (lp.evalCLM ℝ (fun _ : ι ↦ F) 2 i).compLpL 2 volume g
  have hu : ∀ i, (u i : V → F) =ᵐ[volume] fun z ↦ g z i := fun i ↦
    (lp.evalCLM ℝ (fun _ : ι ↦ F) 2 i).coeFn_compLpL g
  have hint : ∀ i x, Integrable (fun z ↦ 𝓕⁻ (σ i) (x - z) • g z i) := fun i x ↦
    ((𝓕⁻ (σ i)).integrable_sub_smul one_le_two (Lp.memLp (u i)) x).congr
      ((hu i).mono fun z hz ↦ by simp [hz])
  filter_upwards [Lp.coeFn_fun_finsetSum s fun i ↦ block σ i (u i),
    s.eventually_all.2 fun i _ ↦ coeFn_block (σ := σ) i (u i)] with x hx hix
  rw [sqFunAdj, sum_apply]
  simp only [comp_apply]
  rw [hx]
  simp only [sqKernelAdj, sum_apply, coe_comp, Function.comp_apply, lsmul_apply, lp.evalCLM_apply]
  rw [integral_finsetSum _ fun i _ ↦ hint i x]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hix i hi]
  exact integral_congr_ae ((hu i).mono fun z hz ↦ by simp [hz])

/-- The symbols `ψᵢ` are real, so the blocks are self-adjoint. -/
private theorem isSelfAdjoint_fourierMultiplierCLM_toLp_symbol (hP : IsDyadic ψ σ e) (i : ι) :
    IsSelfAdjoint (Lp.fourierMultiplierCLM F ((σ i).toLp ∞ (volume : Measure V))) :=
  Lp.isSelfAdjoint_fourierMultiplierCLM
    (Lp.star_eq_self_of_ae_eq_ofReal (coeFn_toLp_symbol hP i))

private theorem adjoint_block (hP : IsDyadic ψ σ e) (i : ι) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    adjoint (block (F := F) σ i) = block σ i := by
  rw [block, L2.adjoint_restrictScalars,
    (isSelfAdjoint_fourierMultiplierCLM_toLp_symbol hP i).adjoint_eq]

private theorem adjoint_lpPi_block [DecidableEq ι] (hP : IsDyadic ψ σ e) (s : Finset ι) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    adjoint (Lp.lpPi 2 s (block (F := F) σ)) = sqFunAdj σ s := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [Lp.adjoint_lpPi, sqFunAdj]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [adjoint_block hP]

private theorem sqFunAdj_lpPi_block [DecidableEq ι] (s : Finset ι)
    (f : Lp F 2 (volume : Measure V)) :
    sqFunAdj σ s (Lp.lpPi 2 s (block σ) f) = ∑ i ∈ s, block σ i (block σ i f) := by
  simp only [sqFunAdj, sum_apply, comp_apply]
  exact Finset.sum_congr rfl fun i hi ↦ congrArg _ (Lp.evalCLM_compLp_lpPi 2 (block σ) hi f)

/-- The symbol `∑ᵢ ψᵢ²` of `∑ᵢ Δᵢ²` is bounded uniformly in the set of indices. -/
private theorem exists_norm_sum_toLp_symbol_smul_le (hP : IsDyadic ψ σ e) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s : Finset ι,
      ‖∑ i ∈ s, ((σ i).toLp ∞ volume • (σ i).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V))‖ ≤
        L := by
  obtain ⟨L, hL0, hL⟩ := hP.sum_sq
  refine ⟨L, hL0, fun s ↦ ?_⟩
  simp only [Lp.smul_eq_mul]
  refine Lp.norm_le_of_ae_bound_top hL0 ?_
  filter_upwards [Lp.coeFn_fun_finsetSum s fun i ↦
      ((σ i).toLp ∞ volume * (σ i).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)),
    s.eventually_all.2 fun i _ ↦ Lp.coeFn_mul ((σ i).toLp ∞ (volume : Measure V))
      ((σ i).toLp ∞ volume),
    s.eventually_all.2 fun i _ ↦ coeFn_toLp_symbol hP i] with ξ h₁ h₂ h₃
  rw [h₁, Finset.sum_congr rfl fun i hi ↦ by rw [h₂ i hi, Pi.mul_apply, h₃ i hi]]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)]
  simpa [sq] using hL s ξ

/-- **The `L²` bound for the blocks**, uniformly in the set of indices:
`∑_{i ∈ s} ‖Δᵢ f‖² = Re ⟪f, ∑_{i ∈ s} Δᵢ² f⟫ ≤ L ‖f‖²`, since `∑_{i ∈ s} Δᵢ²` is the multiplier
with symbol `∑_{i ∈ s} ψᵢ²`. -/
private theorem exists_sum_norm_block_sq_le (hP : IsDyadic ψ σ e) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (s : Finset ι) (f : Lp F 2 (volume : Measure V)),
      ∑ i ∈ s, ‖block σ i f‖ ^ 2 ≤ L * ‖f‖ ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_sum_toLp_symbol_smul_le hP
  refine ⟨L, hL0, fun s f ↦ ?_⟩
  have h : ∑ i ∈ s, ‖block σ i f‖ ^ 2 = RCLike.re ⟪f, Lp.fourierMultiplierCLM F (∑ i ∈ s,
      ((σ i).toLp ∞ volume • (σ i).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V))) f⟫_ℂ := by
    simp only [Lp.fourierMultiplierCLM_sum, sum_apply, inner_sum, map_sum,
      ← Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [block_apply, norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg RCLike.re ((isSelfAdjoint_fourierMultiplierCLM_toLp_symbol hP i).isSymmetric _ _)
  rw [h]
  calc RCLike.re ⟪f, Lp.fourierMultiplierCLM F _ f⟫_ℂ ≤ ‖f‖ * ‖Lp.fourierMultiplierCLM F _ f‖ :=
        re_inner_le_norm _ _
    _ ≤ ‖f‖ * (L * ‖f‖) := by
        gcongr
        exact (Lp.norm_fourierMultiplierCLM_apply_le _ f).trans (by gcongr; exact hL _)
    _ = L * ‖f‖ ^ 2 := by ring

/-- **The `L²` bound**, uniformly in the truncation: `‖(Δᵢ f)_{i ∈ s}‖ ≤ √L ‖f‖`. -/
private theorem exists_norm_sqFun_apply_le [DecidableEq ι] (hP : IsDyadic ψ σ e) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (s : Finset ι) (f : Lp F 2 (volume : Measure V)),
      ‖Lp.lpPi 2 s (block σ) f‖ ≤ √L * ‖f‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_sum_norm_block_sq_le (F := F) hP
  refine ⟨L, hL0, fun s f ↦ ?_⟩
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hL0, ← real_inner_self_eq_norm_sq, ← adjoint_inner_right,
    adjoint_lpPi_block hP, sqFunAdj_lpPi_block, inner_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ ↦ ?_) (hL _ f)
  rw [← real_inner_self_eq_norm_sq, ← adjoint_inner_right, adjoint_block hP]

/-- **The Calderón–Zygmund bound for the truncated square functions**, uniformly in the
truncation. -/
private theorem exists_eLpNorm_sqFun_le [DecidableEq ι]
    (hP : IsDyadic ψ σ e) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ (s : Finset ι) (f : Lp F 2 (volume : Measure V)),
      eLpNorm (Lp.lpPi 2 s (block σ) f) p volume ≤ C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, -, hB⟩ := exists_setIntegral_norm_kernel_sub_sub_le hP
  obtain ⟨L, -, hL⟩ := exists_norm_sqFun_apply_le (F := F) hP
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_hormander (V := V) (H := F)
    (K := lp (fun _ : ι ↦ F) 2) (M := ENNReal.ofReal √L) (B := ENNReal.ofReal B)
    (B' := ENNReal.ofReal B) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hp hp_top
  refine ⟨C, fun s f ↦ hC (Lp.lpPi 2 s (block σ)) (sqKernel σ s) (sqKernelAdj σ s) ?_
    (stronglyMeasurable_sqKernel s) (stronglyMeasurable_sqKernelAdj s)
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel σ s).integrable (norm_sqKernel_sub_le s)
      (hB s))
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel σ s).integrable
      (norm_sqKernelAdj_sub_le s) (hB s))
    (fun g _ _ _ ↦ (ae_sqFun_eq_integral s g).mono fun _ hx _ ↦ hx)
    (fun g _ _ _ ↦ (adjoint_lpPi_block (F := F) hP s) ▸
      (ae_sqFunAdj_eq_integral s g).mono fun _ hx _ ↦ hx)
    f⟩
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (opNorm_le_bound _ (Real.sqrt_nonneg _) (hL s))

/-- **The square function inequality for a dyadic family**:
`‖(∑ᵢ ‖Δᵢ f‖²)^{1/2}‖_p ≤ C ‖f‖_p`. The full square sum is the increasing limit of the square sums
over the indices with `|e i| ≤ n`. -/
private theorem exists_eLpNorm_tsum_le
    (hP : IsDyadic ψ σ e) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ι → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ i, m i =ᵐ[volume] fun ξ ↦ (ψ i ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (fun x ↦ (∑' i, ‖Lp.fourierMultiplierCLM F (m i) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
          volume ≤ C * eLpNorm f p volume := by
  classical
  obtain ⟨C, hC⟩ := exists_eLpNorm_sqFun_le (F := F) hP hp hp_top
  refine ⟨C, fun m hm f ↦ ?_⟩
  have hb : ∀ i, Lp.fourierMultiplierCLM F (m i) f = block σ i f := fun i ↦ by
    rw [eq_toLp_symbol hP (hm i), block_apply]
  simp_rw [hb]
  -- The full square sum is the increasing limit of the partial sums over `t n`.
  set t : ℕ → Finset ι := fun n ↦
    (Finset.Icc (-(n : ℤ)) n).preimage e hP.injective.injOn
  have hmem : ∀ n i, i ∈ t n ↔ (e i).natAbs ≤ n := fun n i ↦ by
    simp only [t, Finset.mem_preimage, Finset.mem_Icc]
    omega
  have hcover : ∀ s : Finset ι, ∃ n, s ⊆ t n := fun s ↦
    ⟨s.sup fun i ↦ (e i).natAbs, fun i hi ↦ (hmem _ i).2 (Finset.le_sup (f := fun i ↦ (e i).natAbs)
      hi)⟩
  set G : ℕ → V → ℝ≥0∞ := fun n x ↦ (∑ i ∈ t n, ‖block σ i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hG : ∀ x, (∑' i, ‖block σ i f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) = ⨆ n, G n x := fun x ↦ by
    rw [← ENNReal.iSup_rpow_of_pos (by norm_num), tsum_eq_iSup_sum' t hcover]
  have hmeas : ∀ n, AEMeasurable (G n) := fun n ↦
    (Finset.aemeasurable_fun_sum _ fun i _ ↦
      (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  have hmono : ∀ x, Monotone fun n ↦ G n x := fun x a b hab ↦ ENNReal.rpow_le_rpow
    (Finset.sum_le_sum_of_subset fun i hi ↦ (hmem b i).2 (((hmem a i).1 hi).trans hab))
    (by norm_num)
  simp_rw [hG]
  rw [eLpNorm_iSup_eq_iSup_eLpNorm hmeas (.of_forall hmono)]
  refine iSup_le fun n ↦
    (eLpNorm_mono_eNorm_ae (hmeas n).aestronglyMeasurable ?_).trans (hC (t n) f)
  -- Pointwise, `G n` is the `ℓ²` norm of `(Δᵢ f)_{i ∈ t n}`.
  filter_upwards [Lp.coeFn_lpPi 2 (t n) (block σ) f] with x hx
  rw [hx, eNorm_eq_self, lp.enorm_sum_single]

/-! ### The reverse inequality -/

/-- If the neighbours `W i` of each index satisfy `(∑_{k ∈ W i} ψₖ) ψᵢ = ψᵢ`, then
`∑_{k ∈ W i} ψₖ ψᵢ = ψᵢ`, as an identity of symbols in `L^∞`. -/
private theorem sum_toLp_symbol_smul_toLp_symbol (hP : IsDyadic ψ σ e)
    (W : ι → Finset ι) (hW : ∀ i ξ, (∑ k ∈ W i, ψ k ξ) * ψ i ξ = ψ i ξ) (i : ι) :
    ∑ k ∈ W i, ((σ k).toLp ∞ volume • (σ i).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)) =
      (σ i).toLp ∞ volume := by
  simp only [Lp.smul_eq_mul]
  refine Lp.sum_mul_eq_of_ae_eq (fun k ↦ ((σ k).coeFn_toLp ∞ volume).trans
    (.of_forall (hP.apply_eq k))) (.of_forall fun ξ ↦ ?_)
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_mul, hW]

/-- The block `Δᵢ f` only sees the blocks of `g` with indices in `W i`:
`⟪Δᵢ f, g⟫ = ∑_{k ∈ W i} ⟪Δᵢ f, Δₖ g⟫`. -/
private theorem inner_fourierMultiplierCLM_eq_sum (hP : IsDyadic ψ σ e)
    (W : ι → Finset ι) (hW : ∀ i ξ, (∑ k ∈ W i, ψ k ξ) * ψ i ξ = ψ i ξ) (i : ι)
    (f g : Lp F 2 (volume : Measure V)) :
    ⟪Lp.fourierMultiplierCLM F ((σ i).toLp ∞ volume) f, g⟫_ℂ =
      ∑ k ∈ W i, ⟪Lp.fourierMultiplierCLM F ((σ i).toLp ∞ volume) f,
        Lp.fourierMultiplierCLM F ((σ k).toLp ∞ volume) g⟫_ℂ := by
  have h : Lp.fourierMultiplierCLM F ((σ i).toLp ∞ volume) f = ∑ k ∈ W i,
      Lp.fourierMultiplierCLM F ((σ k).toLp ∞ volume)
        (Lp.fourierMultiplierCLM F ((σ i).toLp ∞ volume) f) := by
    simp only [Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, ← sum_apply,
      ← Lp.fourierMultiplierCLM_sum, sum_toLp_symbol_smul_toLp_symbol hP W hW]
  conv_lhs => rw [h]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact (isSelfAdjoint_fourierMultiplierCLM_toLp_symbol hP k).isSymmetric _ _

/-- **The reverse square function inequality for a dyadic family**:
`‖f‖_p ≤ C ‖(∑ᵢ ‖Δᵢ f‖²)^{1/2}‖_p`, given neighbourhoods `W i` of bounded overlap (each has at
most `L` elements and each index lies in at most `L` of them), on which the symbols sum to `1` on
the support of `ψᵢ`, and partial sums of the blocks converging to the identity in `L²`. -/
private theorem exists_eLpNorm_le_mul_eLpNorm_tsum [DecidableEq ι]
    (hP : IsDyadic ψ σ e) (W : ι → Finset ι) {L : ℕ} (hWL : ∀ i, (W i).card ≤ L)
    (hWL' : ∀ (s : Finset ι) (k : ι), (s.filter (k ∈ W ·)).card ≤ L)
    (hW : ∀ i ξ, (∑ k ∈ W i, ψ k ξ) * ψ i ξ = ψ i ξ) (t : ℕ → Finset ι)
    (ht : ∀ f : Lp F 2 (volume : Measure V),
      Tendsto (fun N ↦ ∑ i ∈ t N, Lp.fourierMultiplierCLM F ((σ i).toLp ∞ volume) f) atTop (𝓝 f))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ι → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ i, m i =ᵐ[volume] fun ξ ↦ (ψ i ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f p volume ≤ C * eLpNorm
          (fun x ↦ (∑' i, ‖Lp.fourierMultiplierCLM F (m i) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  -- The conjugate exponent `q = (1 - p⁻¹)⁻¹` also lies in `(1, ∞)`.
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have : p.HolderConjugate q := ENNReal.HolderConjugate.inv_one_sub_inv' hp.le
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 hp_top.lt_top
  have hq_top : q ≠ (∞ : ℝ≥0∞) := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  obtain ⟨C, hC⟩ := exists_eLpNorm_tsum_le (F := F) hP hq hq_top
  refine ⟨L * C, fun m hm f ↦ ?_⟩
  have hm' : ∀ i, m i = (σ i).toLp ∞ volume := fun i ↦ eq_toLp_symbol hP (hm i)
  simp_rw [hm']
  -- The labels `e` are injective, so the indices are countable and the square sums measurable.
  have : Countable ι := hP.injective.countable
  push_cast
  exact eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow
    (fun i ↦ Lp.fourierMultiplierCLM F ((σ i).toLp ∞ volume)) W hWL hWL'
    (inner_fourierMultiplierCLM_eq_sum hP W hW) (hC _ (coeFn_toLp_symbol hP)) t (ht f)

end LittlewoodPaleySquare

/-! ### The inhomogeneous partition -/

namespace LittlewoodPaleySquare

/-- The inhomogeneous Littlewood–Paley partition is a dyadic family. -/
private theorem isDyadic_inhomogeneousLittlewoodPaley (φ : ContDiffBump (0 : V)) :
    ∃ e : ℕ → ℤ, IsDyadic φ.inhomogeneousLittlewoodPaley φ.inhomogeneousLittlewoodPaleySchwartz e
      := by
  refine IsDyadic.of_scale Nat.cast_injective φ.inhomogeneousLittlewoodPaleySchwartz_apply
    (fun j ↦ φ.contDiff_inhomogeneousLittlewoodPaley j) (R := φ.rOut) (fun j ξ hξ ↦ ?_)
    (fun k ↦ ?_) φ.exists_sum_sq_inhomogeneousLittlewoodPaley_le
  · rw [zpow_natCast]
    exact lt_of_not_ge fun hle ↦ hξ (φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hle)
  · simpa only [zpow_natCast] using φ.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_le k

end LittlewoodPaleySquare

open LittlewoodPaleySquare in
/-- **The Littlewood–Paley square function inequality.** Let `V` be a finite-dimensional real
inner product space, let `φ` be a smooth bump function on `V`, and let `1 < p < ∞`. Let
`Δⱼ` be the `L²` Fourier multipliers with the pieces `ψ₀ = φ`, `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`
of the inhomogeneous Littlewood–Paley partition as symbols. For every complex Hilbert space `F`
there is a constant `C` such that for every `f ∈ L²(V, F)`,

`‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p ≤ C ‖f‖_p`.

Each symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℕ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
          volume ≤ C * eLpNorm f p volume := by
  obtain ⟨e, hP⟩ := isDyadic_inhomogeneousLittlewoodPaley φ
  exact exists_eLpNorm_tsum_le hP hp hp_top

open LittlewoodPaleySquare in
/-- **The `L²` Littlewood–Paley inequality.** Let `V` be a finite-dimensional real inner product
space, let `φ` be a smooth bump function on `V`, and let `Δⱼ` be the `L²` Fourier multipliers with
the pieces `ψⱼ` of the inhomogeneous Littlewood–Paley partition as symbols. For every complex
Hilbert space `F` there is a constant `L` such that for every `f ∈ L²(V, F)` and every finite set
`s` of indices,

`∑_{j ∈ s} ‖Δⱼ f‖₂² ≤ L ‖f‖₂²`.

Each symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_sum_norm_fourierMultiplierCLM_sq_le [MeasurableSpace V] [BorelSpace V]
    [CompleteSpace F] (φ : ContDiffBump (0 : V)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ m : ℕ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp F 2 (volume : Measure V)) (s : Finset ℕ),
        ∑ j ∈ s, ‖Lp.fourierMultiplierCLM F (m j) f‖ ^ 2 ≤ L * ‖f‖ ^ 2 := by
  obtain ⟨e, hP⟩ := isDyadic_inhomogeneousLittlewoodPaley φ
  obtain ⟨L, hL0, hL⟩ := exists_sum_norm_block_sq_le (F := F) hP
  refine ⟨L, hL0, fun m hm f s ↦ le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) (hL s f)⟩
  rw [eq_toLp_symbol hP (hm j), block_apply]

end TauCeti

/-! ### Littlewood–Paley reconstruction in `L²` -/

namespace MeasureTheory.Lp

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- **Littlewood–Paley reconstruction in `L²`.** The partial sums `∑_{j < N} Δⱼ f` of the
Littlewood–Paley blocks of `f ∈ L²(V, F)` converge to `f` in `L²`. Each symbol enters as any
element of `L^∞` almost everywhere equal to the piece `ψⱼ` of the inhomogeneous partition. -/
theorem tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley
    (φ : ContDiffBump (0 : V)) {m : ℕ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
    (f : Lp F 2 (volume : Measure V)) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, fourierMultiplierCLM F (m j) f) atTop (𝓝 f) := by
  -- The partial sums of the symbols are `∑_{j < N} ψⱼ = φ (2^{1-N} ·)`, with values in `[0, 1]`,
  -- and tend to `1` at every frequency.
  refine tendsto_sum_fourierMultiplierCLM_of_tendsto hm _ (C := 1) (fun N ξ ↦ ?_)
    (.of_forall fun ξ ↦ ?_) f
  · rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    rcases N with _ | N
    · simp
    · rw [φ.sum_inhomogeneousLittlewoodPaley_range, abs_of_nonneg φ.nonneg]
      exact φ.le_one
  · simpa only [Function.comp_def, Complex.ofReal_sum, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto _).comp
        (φ.hasSum_inhomogeneousLittlewoodPaley ξ).tendsto_sum_nat

end MeasureTheory.Lp

namespace ContDiffBump

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- On the zero space every homogeneous Littlewood–Paley cutoff `ψⱼ` vanishes, and so does the
block `Pⱼ`: the `L²` Fourier multiplier with any symbol in `L^∞` almost everywhere equal to
`ψⱼ` is `0`. -/
theorem fourierMultiplierCLM_littlewoodPaley_eq_zero [Subsingleton V] {φ : ContDiffBump (0 : V)}
    {j : ℤ} {m : Lp ℂ ∞ (volume : Measure V)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    Lp.fourierMultiplierCLM F m = 0 := by
  rw [Lp.fourierMultiplierCLM_of_ae_eq_const (F := F) (c := 0)]
  · exact zero_smul ℂ (ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure V)))
  filter_upwards [hm] with ξ h
  rw [h, Subsingleton.elim ξ 0, φ.littlewoodPaley_apply_zero, Complex.ofReal_zero]

/-- **Homogeneous Littlewood–Paley reconstruction in `L²`.** On a nontrivial space, the partial
sums `∑_{-N < j ≤ N} Pⱼ f` of the homogeneous Littlewood–Paley blocks of `f ∈ L²(V, F)` converge
to `f` in `L²`. Each symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. The
cutoffs sum to `1` only away from the origin, a null set on a nontrivial space; on the zero space
every block vanishes. -/
theorem tendsto_sum_fourierMultiplierCLM_littlewoodPaley [Nontrivial V]
    (φ : ContDiffBump (0 : V)) {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (f : Lp F 2 (volume : Measure V)) :
    Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.Ioc (-(N : ℤ)) N, Lp.fourierMultiplierCLM F (m j) f)
      atTop (𝓝 f) := by
  -- The partial sums of the symbols telescope to `φ (2^{-N} ·) - φ (2^N ·)`, with values in
  -- `[-1, 1]`, and tend to `1` away from the origin, which is a null set.
  refine Lp.tendsto_sum_fourierMultiplierCLM_of_tendsto hm _ (C := 1) (fun N ξ ↦ ?_) ?_ f
  · rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      φ.sum_littlewoodPaley_Ioc (by omega)]
    exact abs_sub_le_of_nonneg_of_le φ.nonneg φ.le_one φ.nonneg φ.le_one
  · filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    simpa only [Function.comp_def, Complex.ofReal_sum, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto _).comp
        ((φ.hasSum_littlewoodPaley hξ).comp (Finset.tendsto_Ioc_neg (R := ℤ)))

/-- **The `Lʳ` norm is at most the sum of the `Lʳ` norms of the blocks.** On a nontrivial space,
for a bounded operator `A` on `L²(V, F)`, every `f ∈ L²` and every `1 ≤ r ≤ ∞`,
`‖A f‖_r ≤ ∑ⱼ ‖A Pⱼ f‖_r`, where `Pⱼ` is the `L²` Fourier multiplier with symbol `ψⱼ`: the partial
sums of the blocks converge to `f` in `L²`, and the `Lʳ` seminorm is lower semicontinuous on `L²`.
Neither side is assumed finite. -/
theorem eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM [Nontrivial V]
    (φ : ContDiffBump (0 : V)) {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (A : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (f : Lp F 2 (volume : Measure V)) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (A f) r volume ≤ ∑' j, eLpNorm (A (Lp.fourierMultiplierCLM F (m j) f)) r volume := by
  by_contra! h
  have hlim := (A.continuous.tendsto f).comp
    (φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm f)
  obtain ⟨N, hN⟩ := (hlim.eventually (TauCeti.lowerSemicontinuous_eLpNorm_Lp
    (Measure.AbsolutelyContinuous.refl volume) r (A f) _ h)).exists
  rw [Function.comp_apply, map_sum] at hN
  dsimp only at hN
  rw [eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)] at hN
  exact (hN.trans_le ((eLpNorm_sum_le hr).trans (sum_le_tsum _))).false


end ContDiffBump

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ### The reverse inequality -/

open LittlewoodPaleySquare in
/-- **The reverse Littlewood–Paley square function inequality.** Let `V` be a finite-dimensional
real inner product space, let `φ` be a smooth bump function on `V`, and let `1 < p < ∞`.
Let `Δⱼ` be the `L²` Fourier multipliers with the pieces `ψ₀ = φ`,
`ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` of the inhomogeneous Littlewood–Paley partition as symbols.
For every complex Hilbert space `F` there is a constant `C` such that for every `f ∈ L²(V, F)`,

`‖f‖_p ≤ C ‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p`.

Neither side is assumed finite: in particular `f ∈ Lᵖ` as soon as its square function is. Each
symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℕ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f p volume ≤ C * eLpNorm
          (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  obtain ⟨e, hP⟩ := isDyadic_inhomogeneousLittlewoodPaley φ
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  have hWL : ∀ j k, k ∈ Finset.Ico (j + 1 - L) (j + L) → |(k : ℤ) - j| < L :=
    fun j k hk ↦ abs_sub_lt_iff.2 (by rw [Finset.mem_Ico] at hk; omega)
  refine exists_eLpNorm_le_mul_eLpNorm_tsum hP (fun j ↦ Finset.Ico (j + 1 - L) (j + L))
    (fun j ↦ card_le_two_mul_of_abs_sub_lt Nat.cast_injective (hWL j))
    (card_filter_mem_le_two_mul_of_abs_sub_lt Nat.cast_injective hWL)
    (fun j ξ ↦ by
      rw [← φ.enlargedLittlewoodPaley_apply]
      exact φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL j ξ)
    (fun N ↦ Finset.range N)
    (fun f ↦ Lp.tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley φ
      (coeFn_toLp_symbol hP) f) hp hp_top

/-! ### The homogeneous Littlewood–Paley cutoffs -/

namespace LittlewoodPaleySquare

/-- The homogeneous Littlewood–Paley cutoffs form a dyadic family. -/
private theorem isDyadic_littlewoodPaley (φ : ContDiffBump (0 : V)) :
    ∃ e : ℤ → ℤ, IsDyadic φ.littlewoodPaley φ.littlewoodPaleySchwartz e :=
  IsDyadic.of_scale Function.injective_id φ.littlewoodPaleySchwartz_apply
    (fun j ↦ φ.contDiff_littlewoodPaley j) (R := φ.rOut)
    (fun _ _ hξ ↦ lt_of_not_ge fun hle ↦ hξ (φ.littlewoodPaley_eq_zero_of_le_norm hle))
    φ.exists_norm_iteratedFDeriv_littlewoodPaley_le φ.exists_sum_sq_littlewoodPaley_le

end LittlewoodPaleySquare

open LittlewoodPaleySquare in
/-- **The homogeneous Littlewood–Paley square function inequality.** Let `V` be a
finite-dimensional real inner product space, let `φ` be a smooth bump function on `V`, and let
`1 < p < ∞`. Let `Pⱼ`, `j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous
Littlewood–Paley cutoffs `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` as symbols. For every complex Hilbert
space `F` there is a constant `C` such that for every `f ∈ L²(V, F)`,

`‖(∑_{j ∈ ℤ} ‖Pⱼ f‖²)^{1/2}‖_p ≤ C ‖f‖_p`.

Each symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. In dimension `0`
every cutoff vanishes, and so does the square function. -/
theorem exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow_le
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
          volume ≤ C * eLpNorm f p volume := by
  obtain ⟨e, hP⟩ := isDyadic_littlewoodPaley φ
  exact exists_eLpNorm_tsum_le hP hp hp_top

open LittlewoodPaleySquare in
/-- **The reverse homogeneous Littlewood–Paley square function inequality.** Let `V` be a real
inner product space of finite dimension `n ≥ 1`, let `φ` be a smooth bump function on `V`, and
let `1 < p < ∞`. Let `Pⱼ`, `j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous
Littlewood–Paley cutoffs `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` as symbols. For every complex Hilbert
space `F` there is a constant `C` such that for every `f ∈ L²(V, F)`,

`‖f‖_p ≤ C ‖(∑_{j ∈ ℤ} ‖Pⱼ f‖²)^{1/2}‖_p`.

Neither side is assumed finite: in particular `f ∈ Lᵖ` as soon as its square function is. Each
symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow
    [Nontrivial V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace F]
    (φ : ContDiffBump (0 : V)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f p volume ≤ C * eLpNorm
          (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  obtain ⟨e, hP⟩ := isDyadic_littlewoodPaley φ
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  have hWL : ∀ j k : ℤ, k ∈ Finset.Ioo (j - L) (j + L) → |id k - id j| < L :=
    fun j k hk ↦ abs_sub_lt_iff.2 (by simp only [Finset.mem_Ioo, id_eq] at hk ⊢; omega)
  refine exists_eLpNorm_le_mul_eLpNorm_tsum hP (fun j ↦ Finset.Ioo (j - L) (j + L))
    (fun j ↦ card_le_two_mul_of_abs_sub_lt Function.injective_id (hWL j))
    (card_filter_mem_le_two_mul_of_abs_sub_lt Function.injective_id hWL)
    (fun j ξ ↦ by rw [Finset.sum_mul]; exact φ.sum_littlewoodPaley_mul_littlewoodPaley hL j ξ)
    (fun N ↦ Finset.Ioc (-(N : ℤ)) N)
    (fun f ↦ φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley (coeFn_toLp_symbol hP) f)
    hp hp_top

end TauCeti

/-! ### Homogeneous Littlewood–Paley blocks on `Lᵖ` -/

namespace ContDiffBump

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (φ : ContDiffBump (0 : V))

variable [MeasurableSpace V] [BorelSpace V]

/-- Every symbol in `L^∞` almost everywhere equal to `ψⱼ` is the class of the Schwartz
cutoff. -/
private theorem eq_toLp_littlewoodPaleySchwartz {j : ℤ} {m : Lp ℂ ∞ (volume : Measure V)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    m = (littlewoodPaleySchwartz φ j).toLp ∞ :=
  Lp.ext <| hm.trans <| by
    filter_upwards [(littlewoodPaleySchwartz φ j).coeFn_toLp ∞ volume] with ξ h
    rw [h, coe_littlewoodPaleySchwartz]

variable {φ} in
/-- Every symbol in `L^∞` almost everywhere equal to `ψⱼ` is almost everywhere equal to the dilate
`ψ₀ (2^{-j} ·)`. -/
theorem ae_eq_littlewoodPaley_zero_comp_smul {j : ℤ} {m : Lp ℂ ∞ (volume : Measure V)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley 0 (((2 : ℝ) ^ j)⁻¹ • ξ) : ℂ) := by
  filter_upwards [hm] with ξ hξ
  rw [hξ, φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply j]

/-- The kernel `𝓕⁻ ψⱼ` of a homogeneous Littlewood–Paley block is a Schwartz function, so it lies
in every `Lᵖ`. -/
theorem memLp_fourierInv_littlewoodPaley (j : ℤ) (p : ℝ≥0∞) :
    MemLp (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) p volume := by
  rw [← coe_littlewoodPaleySchwartz, ← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ (littlewoodPaleySchwartz φ j)).memLp p volume

/-- The cutoff `ψⱼ` of a homogeneous Littlewood–Paley block, as a complex-valued function, is a
Schwartz function, so it lies in every `Lᵖ`; for `p = ∞` it is an admissible `L²` multiplier
symbol. -/
theorem memLp_ofReal_littlewoodPaley (j : ℤ) (p : ℝ≥0∞) :
    MemLp (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) p volume := by
  rw [← coe_littlewoodPaleySchwartz]
  exact (littlewoodPaleySchwartz φ j).memLp p volume

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The homogeneous Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in the scale.** For
every symbol `m ∈ L^∞` almost everywhere equal to `ψⱼ`, `j ∈ ℤ`, every `f ∈ L²(V, F)` and every
`1 ≤ p ≤ ∞`, `‖Pⱼ f‖_p ≤ ‖𝓕⁻ ψ₀‖₁ ‖f‖_p`, where `Pⱼ` is the `L²` Fourier multiplier with symbol
`m`: `Pⱼ` is convolution with `𝓕⁻ ψⱼ`, a dilate of `𝓕⁻ ψ₀` with the same `L¹` norm. -/
theorem eLpNorm_fourierMultiplierCLM_littlewoodPaley_le {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure V)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (f : Lp F 2 (volume : Measure V)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (Lp.fourierMultiplierCLM F m f) p volume ≤
      eLpNorm (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))) 1 volume * eLpNorm f p volume := by
  rw [eq_toLp_littlewoodPaleySchwartz φ hm]
  refine ((littlewoodPaleySchwartz φ j).eLpNorm_fourierMultiplierCLM_toLp_le f hp).trans_eq ?_
  have h : (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) =
      fun ξ ↦ (fun η ↦ (φ.littlewoodPaley 0 η : ℂ)) (((2 : ℝ) ^ j)⁻¹ • ξ) :=
    funext fun ξ ↦ by rw [littlewoodPaley_apply_eq_littlewoodPaley_zero_apply]
  rw [coe_littlewoodPaleySchwartz, h, TauCeti.eLpNorm_fourierInv_comp_inv_smul
    (fun η ↦ (φ.littlewoodPaley 0 η : ℂ)) (zpow_pos two_pos j)]
  simp

/-- The homogeneous Littlewood–Paley block `Pⱼ` has norm at most `1` on `L²`. -/
theorem norm_fourierMultiplierCLM_littlewoodPaley_le {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure V)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    ‖Lp.fourierMultiplierCLM (E := V) F m‖ ≤ 1 := by
  refine (Lp.norm_fourierMultiplierCLM_le m).trans ?_
  exact Lp.norm_le_of_ae_bound_top zero_le_one (hm.mono fun ξ h ↦ by
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    exact φ.abs_littlewoodPaley_le_one j ξ)

/-- **The neighbouring blocks reproduce `Pⱼ`.** If the cutoffs whose indices differ by at least
`L` have disjoint supports, as for the `L` of `ContDiffBump.exists_littlewoodPaley_mul_eq_zero φ`,
then `∑_{j - L < k < j + L} Pₖ Pⱼ f = Pⱼ f` for every `f ∈ L²(V, F)`, where `Pₖ` is the `L²`
Fourier multiplier with any symbol in `L^∞` almost everywhere equal to `ψₖ`. -/
theorem sum_fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : V, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (j : ℤ)
    (f : Lp F 2 (volume : Measure V)) :
    ∑ k ∈ Finset.Ioo (j - L) (j + L),
        Lp.fourierMultiplierCLM F (m k) (Lp.fourierMultiplierCLM F (m j) f) =
      Lp.fourierMultiplierCLM F (m j) f := by
  -- As symbols in `L^∞`, `∑_{j - L < k < j + L} ψₖ ψⱼ = ψⱼ`.
  have hsym : ∑ k ∈ Finset.Ioo (j - L) (j + L), (m k • m j : Lp ℂ ∞ (volume : Measure V)) =
      m j := by
    simpa only [Lp.smul_eq_mul] using Lp.sum_mul_eq_of_ae_eq hm (.of_forall fun ξ ↦ by
      exact_mod_cast φ.sum_littlewoodPaley_mul_littlewoodPaley hL j ξ)
  simp only [Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  conv_rhs => rw [← hsym]
  rw [Lp.fourierMultiplierCLM_sum, FunLike.coe_sum, Finset.sum_apply]

/-- **Far blocks compose to zero.** If the cutoffs whose indices differ by at least `L` have
disjoint supports, as for the `L` of `ContDiffBump.exists_littlewoodPaley_mul_eq_zero φ`, then
`Pⱼ Pₖ f = 0` for every `f ∈ L²(V, F)` once `|j - k| ≥ L`, where `Pⱼ` is the `L²` Fourier
multiplier with any symbol in `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley_eq_zero {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : V, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) {j k : ℤ} (hjk : L ≤ |j - k|)
    (f : Lp F 2 (volume : Measure V)) :
    Lp.fourierMultiplierCLM F (m j) (Lp.fourierMultiplierCLM F (m k) f) = 0 := by
  -- The symbol `ψⱼ ψₖ` of `Pⱼ Pₖ` vanishes.
  rw [Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply,
    Lp.fourierMultiplierCLM_of_ae_eq_const (c := 0), _root_.smul_apply, zero_smul]
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) (m j) (m k), hm j, hm k] with ξ h₁ h₂ h₃
  rw [h₁, Pi.smul_apply', h₂, h₃, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_eq_zero]
  rcases le_abs'.1 hjk with hjk | hjk
  · exact hL j k (by omega) ξ
  · exact mul_comm (φ.littlewoodPaley j ξ) _ ▸ hL k j (by omega) ξ

/-- **A nonzero datum with finitely many nonzero blocks.** On a nontrivial space, some nonzero
`f₀ ∈ L²(V, F)` has only finitely many nonzero homogeneous Littlewood–Paley blocks: a nonzero block
`f₀ = P_{j₀} g`, whose blocks `Pⱼ P_{j₀} g` vanish for `|j - j₀|` large. Each symbol enters as any
element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_ne_zero_forall_notMem_fourierMultiplierCLM_eq_zero [Nontrivial V] [Nontrivial F]
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    ∃ f₀ : Lp F 2 (volume : Measure V), f₀ ≠ 0 ∧
      ∃ S : Finset ℤ, ∀ j ∉ S, Lp.fourierMultiplierCLM F (m j) f₀ = 0 := by
  -- A nonzero vector on the unit ball is a nonzero element of `L²`.
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  obtain ⟨g, hg⟩ : ∃ g : Lp F 2 (volume : Measure V), g ≠ 0 :=
    ⟨indicatorConstLp 2 (Metric.isOpen_ball (x := (0 : V)) (ε := 1)).measurableSet
      measure_ball_lt_top.ne v, fun h ↦ (TauCeti.indicatorConstLp_eq_zero_iff.1 h).elim
        (Metric.measure_ball_pos volume (0 : V) one_pos).ne' hv⟩
  -- Some block of `g` is nonzero, since the blocks reconstruct `g`.
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, Lp.fourierMultiplierCLM F (m j₀) g ≠ 0 := by
    by_contra! hall
    have hlim := φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm g
    simp only [hall, Finset.sum_const_zero] at hlim
    exact hg (tendsto_nhds_unique hlim tendsto_const_nhds)
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  refine ⟨_, hj₀, Finset.Ioo (j₀ - L) (j₀ + L), fun j hj ↦
    φ.fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley_eq_zero hL hm ?_ g⟩
  rw [Finset.mem_Ioo] at hj
  rw [le_abs']
  omega

/-- **Duality of the dyadic `ℓ¹` and `ℓ^∞` norms on `L²`.** On a nontrivial space, for every
`γ ∈ ℝ` there is `K` such that for all `f, g ∈ L²(V, F)`, if the homogeneous Littlewood–Paley
blocks of `g` satisfy `‖Pₖ g‖₂ ≤ A 2^{kγ}` for every `k ∈ ℤ`, then

`|⟪f, g⟫| ≤ K A ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂`.

In the language of homogeneous Besov spaces, this is the pairing of `\dot B^γ_{2,1}` with
`\dot B^{-γ}_{2,∞}`. The constant depends only on `φ` and `γ`. Each symbol enters as any element of
`L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_enorm_inner_le_mul_tsum [Nontrivial V] (γ : ℝ) :
    ∃ K : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f g : Lp F 2 (volume : Measure V)) (A : ℝ≥0∞),
        (∀ k : ℤ, ‖Lp.fourierMultiplierCLM F (m k) g‖ₑ ≤
          A * ENNReal.ofReal (((2 : ℝ) ^ k) ^ γ)) →
        ‖⟪f, g⟫_ℂ‖ₑ ≤ K * A * ∑' j : ℤ,
          ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) * ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ := by
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  set S := Finset.Ioo (-(L : ℤ)) L
  refine ⟨∑ d ∈ S, (((2 : ℝ) ^ d) ^ (-γ)).toNNReal, fun m hm f g A hg ↦ ?_⟩
  set w : ℤ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ)
  set u : ℤ → ℝ≥0∞ := fun j ↦ ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ
  -- Each pairing `⟪f, Pₖ g⟫ = ∑_{|j - k| < L} ⟪Pⱼ f, Pₖ g⟫` only sees the blocks of `f` near `k`.
  have hk : ∀ k, ‖⟪f, Lp.fourierMultiplierCLM F (m k) g⟫_ℂ‖ₑ ≤
      A * ∑ d ∈ S, w k * u (d + k) := by
    intro k
    have hS : Finset.Ioo (k - L) (k + L) = S.map (addRightEmbedding k) := by
      rw [Finset.map_add_right_Ioo, neg_add_eq_sub, add_comm (L : ℤ)]
    rw [← φ.sum_fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley hL hm k g, inner_sum,
      Finset.mul_sum]
    refine (eNorm_sum_le _ _).trans ?_
    rw [hS, Finset.sum_map]
    refine Finset.sum_le_sum fun d _ ↦ ?_
    have hsa := (Lp.isSelfAdjoint_fourierMultiplierCLM
      (Lp.star_eq_self_of_ae_eq_ofReal (hm (d + k)))).isSymmetric f
        (Lp.fourierMultiplierCLM F (m k) g)
    rw [ContinuousLinearMap.coe_coe] at hsa
    rw [addRightEmbedding_apply, ← hsa]
    refine (eNorm_inner_le_eNorm _ _).trans ((mul_le_mul_right (hg k) _).trans_eq ?_)
    simp only [u, w]
    ring
  -- The partial sums of the blocks of `g` converge to `g`, so `⟪f, g⟫` is bounded by the sum of
  -- the pairings `⟪f, Pₖ g⟫`; shifting the index by `d` costs the factor `2^{-dγ}`.
  have hshift : ∀ d j : ℤ, w (j - d) = ENNReal.ofReal (((2 : ℝ) ^ d) ^ (-γ)) * w j := fun d j ↦ by
    simp only [w]
    rw [← ENNReal.ofReal_mul (by positivity), zpow_sub₀ two_ne_zero,
      Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv,
      mul_comm]
  have hsum : ∑' k, ∑ d ∈ S, w k * u (d + k) =
      ((∑ d ∈ S, (((2 : ℝ) ^ d) ^ (-γ)).toNNReal : ℝ≥0) : ℝ≥0∞) * ∑' j, w j * u j := by
    rw [Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable, ENNReal.ofNNReal_finsetSum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← (Equiv.subRight d).tsum_eq, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j ↦ ?_
    simp only [Equiv.subRight_apply, add_sub_cancel, hshift, mul_assoc,
      ENNReal.ofNNReal_toNNReal]
  refine le_of_tendsto' ((continuous_eNorm.tendsto _).comp
    (tendsto_const_nhds.inner (φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm g)))
    fun N ↦ ?_
  rw [Function.comp_apply, inner_sum, mul_comm _ A, mul_assoc, ← hsum, ← ENNReal.tsum_mul_left]
  exact (eNorm_sum_le _ _).trans ((sum_le_tsum _).trans (tsum_le_tsum hk))

end ContDiffBump

/-! ### Dyadic multipliers and squared blocks -/

namespace ContDiffBump

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (φ : ContDiffBump (0 : V))

/-- The **dyadic dilate** `σ ((2^j φ.rIn / 2)⁻¹ ·)` of a Schwartz function `σ`. It carries the
annulus `1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn` onto the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, which
contains the support of `ψⱼ`. -/
def dyadicDilate (σ : 𝓢(V, ℂ)) (j : ℤ) : 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.smulLeft
    (Units.mk0 ((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ (inv_ne_zero
      (mul_pos (zpow_pos two_pos j) (half_pos φ.rIn_pos)).ne'))) σ

/-- The values of the dyadic dilate `σ ((2^j φ.rIn / 2)⁻¹ ·)`. -/
@[simp]
theorem dyadicDilate_apply (σ : 𝓢(V, ℂ)) (j : ℤ) (ξ : V) :
    φ.dyadicDilate σ j ξ = σ (((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ • ξ) := by
  rw [dyadicDilate, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_mk0]

/-- Each dyadic dilate of `σ` is the rescaling of the one at scale `0`:
`σⱼ ξ = σ₀ (2^{-j} ξ)`. -/
theorem dyadicDilate_apply_eq_dyadicDilate_zero_apply (σ : 𝓢(V, ℂ)) (j : ℤ) (ξ : V) :
    φ.dyadicDilate σ j ξ = φ.dyadicDilate σ 0 (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  rw [dyadicDilate_apply, dyadicDilate_apply, smul_smul, zpow_zero, one_mul, ← mul_inv,
    mul_comm (φ.rIn / 2)]

/-- **Dyadic dilates invert a symbol on the supports of the cutoffs.** If `σ` equals
`1 / a ((φ.rIn / 2) • η)` on the annulus `1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`, then wherever `ψⱼ ξ ≠ 0`
the `j`-th dyadic dilate of `σ` is `1 / a (2^{-j} ξ)`. -/
theorem dyadicDilate_apply_of_littlewoodPaley_ne_zero {a : V → ℝ} {σ : 𝓢(V, ℂ)}
    (hσ : Set.EqOn σ (fun η ↦ (((a ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
      {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn})
    {j : ℤ} {ξ : V} (hξ : φ.littlewoodPaley j ξ ≠ 0) :
    φ.dyadicDilate σ j ξ = (((a (((2 : ℝ) ^ j)⁻¹ • ξ))⁻¹ : ℝ) : ℂ) := by
  have hb : (0 : ℝ) < 2 ^ j * (φ.rIn / 2) := mul_pos (zpow_pos two_pos j) (half_pos φ.rIn_pos)
  have h1 : 2 ^ (j - 1) * φ.rIn < ‖ξ‖ := by
    by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_norm_le (not_lt.1 h))
  have h2 : ‖ξ‖ < 2 ^ j * φ.rOut := by
    by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_le_norm (not_lt.1 h))
  rw [zpow_sub_one₀ two_ne_zero] at h1
  set η := ((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ • ξ
  have hη : ‖η‖ = ‖ξ‖ / (2 ^ j * (φ.rIn / 2)) := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hb.le), inv_mul_eq_div]
  have hmem : 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn := by
    rw [hη, le_div_iff₀ hb, div_le_div_iff₀ hb φ.rIn_pos]
    constructor <;> nlinarith [φ.rIn_pos]
  have haη : (φ.rIn / 2) • η = ((2 : ℝ) ^ j)⁻¹ • ξ := by
    rw [smul_smul, mul_inv, ← mul_assoc, mul_comm (φ.rIn / 2), mul_assoc,
      mul_inv_cancel₀ (half_pos φ.rIn_pos).ne', mul_one]
  rw [dyadicDilate_apply, hσ hmem]
  beta_reduce
  rw [haη]

variable [FiniteDimensional ℝ V]

/-- A real symbol `a` smooth and nonvanishing away from the origin is inverted on an annulus by a
Schwartz function: some `σ` equals `1 / a ((φ.rIn / 2) • η)` for `1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`, so
its dyadic dilates invert `a (2^{-j} ·)` on the support of `ψⱼ`
(`ContDiffBump.dyadicDilate_apply_of_littlewoodPaley_ne_zero`). -/
theorem exists_eqOn_inv_of_contDiffOn {a : V → ℝ} (ha : ContDiffOn ℝ ∞ a {0}ᶜ)
    (ha0 : ∀ ξ ≠ 0, a ξ ≠ 0) :
    ∃ σ : 𝓢(V, ℂ), Set.EqOn σ (fun η ↦ (((a ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
      {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn} := by
  have hr : φ.rIn / 2 ≠ 0 := (half_pos φ.rIn_pos).ne'
  refine SchwartzMap.exists_eqOn_annulus_of_contDiffOn
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiffOn.inv (fun η hη ↦ ?_) fun η hη ↦ ?_)) _
  · exact (ha.comp (contDiff_const_smul _).contDiffOn fun ξ hξ ↦ smul_ne_zero hr hξ) η hη
  · exact ha0 _ (smul_ne_zero hr hη)

/-- A Schwartz function `θ` equal to `1 / Ψ ((φ.rIn / 2) • η)` on the annulus
`1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`, where `Ψ = ∑ⱼ ψⱼ²`: `1 / Ψ` is smooth away from the origin. -/
private theorem exists_invSumSq : ∃ σ : 𝓢(V, ℂ), Set.EqOn σ
    (fun η ↦ (((φ.sumSqLittlewoodPaley ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
    {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn} :=
  φ.exists_eqOn_inv_of_contDiffOn
    (fun _ hξ ↦ (φ.contDiffAt_sumSqLittlewoodPaley hξ).contDiffWithinAt)
    fun _ hξ ↦ (φ.sumSqLittlewoodPaley_pos hξ).ne'

/-- A Schwartz function equal to `1 / Ψ ((φ.rIn / 2) • η)` on the annulus
`1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`, where `Ψ = ∑ⱼ ψⱼ²` is `ContDiffBump.sumSqLittlewoodPaley`. Its
`j`-th dyadic dilate inverts `Ψ` on the support of `ψⱼ`
(`ContDiffBump.dyadicDilate_invSumSq_mul_sumSqLittlewoodPaley`). -/
def invSumSq : 𝓢(V, ℂ) :=
  φ.exists_invSumSq.choose

/-- `ContDiffBump.invSumSq` equals `1 / Ψ ((φ.rIn / 2) • η)` on the annulus
`1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`, where `Ψ = ∑ⱼ ψⱼ²`. -/
theorem eqOn_invSumSq : Set.EqOn φ.invSumSq
    (fun η ↦ (((φ.sumSqLittlewoodPaley ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
    {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn} :=
  φ.exists_invSumSq.choose_spec

/-- On the support of `ψⱼ`, the `j`-th dyadic dilate of `ContDiffBump.invSumSq` inverts
`Ψ = ∑ⱼ ψⱼ²`. -/
theorem dyadicDilate_invSumSq_mul_sumSqLittlewoodPaley {j : ℤ} {ξ : V}
    (hξ : φ.littlewoodPaley j ξ ≠ 0) :
    φ.dyadicDilate φ.invSumSq j ξ * (φ.sumSqLittlewoodPaley ξ : ℂ) = 1 := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    exact hξ (φ.littlewoodPaley_apply_zero j)
  rw [φ.dyadicDilate_apply_of_littlewoodPaley_ne_zero φ.eqOn_invSumSq hξ,
    sumSqLittlewoodPaley_two_zpow_inv_smul, Complex.ofReal_inv]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (φ.sumSqLittlewoodPaley_pos hξ0).ne')

/-- **Reassembling a cutoff from squared cutoffs.** If the cutoffs whose indices differ by at least
`L` have disjoint supports, as for the `L` of `ContDiffBump.exists_littlewoodPaley_mul_eq_zero φ`,
then `∑_{|d| < L} ψ_{d + l}² θₗ ψₗ = ψₗ`, where `θₗ` is the `l`-th dyadic dilate of
`ContDiffBump.invSumSq`. -/
theorem sum_littlewoodPaley_mul_littlewoodPaley_mul_dyadicDilate_invSumSq {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : V, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    (l : ℤ) (ξ : V) :
    ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (φ.littlewoodPaley (d + l) ξ : ℂ) *
        ((φ.littlewoodPaley (d + l) ξ : ℂ) *
          (φ.dyadicDilate φ.invSumSq l ξ * (φ.littlewoodPaley l ξ : ℂ))) =
      φ.littlewoodPaley l ξ := by
  by_cases h : φ.littlewoodPaley l ξ = 0
  · simp only [h, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  -- Only the cutoffs `ψⱼ` with `|j - l| < L` are nonzero at `ξ`, so they sum their squares to `Ψ`.
  have hs : ∀ j ∉ (Finset.Ioo (-(L : ℤ)) L).map (addRightEmbedding l),
      φ.littlewoodPaley j ξ = 0 := by
    intro j hj
    rw [Finset.map_add_right_Ioo, Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hj
    rcases hj with hj | hj
    · exact (mul_eq_zero.1 (hL j l (by omega) ξ)).resolve_right h
    · exact (mul_eq_zero.1 (hL l j (by omega) ξ)).resolve_left h
  have hsum := φ.sumSqLittlewoodPaley_eq_sum hs
  rw [Finset.sum_map] at hsum
  simp only [addRightEmbedding_apply] at hsum
  have key := φ.dyadicDilate_invSumSq_mul_sumSqLittlewoodPaley h
  rw [hsum] at key
  push_cast at key
  simp only [← mul_assoc, ← sq, ← Finset.sum_mul]
  linear_combination (φ.littlewoodPaley l ξ : ℂ) * key

variable [MeasurableSpace V] [BorelSpace V]

/-- The kernel `𝓕⁻ σⱼ` of a dyadic dilate of a Schwartz function is a Schwartz function, so it lies
in every `Lᵖ`. -/
theorem memLp_fourierInv_dyadicDilate (σ : 𝓢(V, ℂ)) (j : ℤ) (p : ℝ≥0∞) :
    MemLp (𝓕⁻ ⇑(φ.dyadicDilate σ j)) p volume := by
  rw [← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ (φ.dyadicDilate σ j)).memLp p volume

/-- The kernels of the dyadic dilates of `σ` all have the same `L¹` norm. -/
theorem eLpNorm_fourierInv_dyadicDilate (σ : 𝓢(V, ℂ)) (j : ℤ) :
    eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ j)) 1 volume =
      eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) 1 volume := by
  have h : ⇑(φ.dyadicDilate σ j) = fun ξ ↦ (⇑(φ.dyadicDilate σ 0)) (((2 : ℝ) ^ j)⁻¹ • ξ) :=
    funext (φ.dyadicDilate_apply_eq_dyadicDilate_zero_apply σ j)
  rw [h, TauCeti.eLpNorm_fourierInv_comp_inv_smul _ (zpow_pos two_pos j)]
  simp

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **dyadic multiplier**: the `L²` Fourier multiplier whose symbol is the `j`-th dyadic dilate
of the Schwartz function `σ`. -/
def dyadicMultiplier (σ : 𝓢(V, ℂ)) (j : ℤ) :
    Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V) :=
  Lp.fourierMultiplierCLM F ((φ.dyadicDilate σ j).toLp ∞)

/-- Unfolding `ContDiffBump.dyadicMultiplier`. -/
theorem dyadicMultiplier_def (σ : 𝓢(V, ℂ)) (j : ℤ) :
    φ.dyadicMultiplier F σ j = Lp.fourierMultiplierCLM F ((φ.dyadicDilate σ j).toLp ∞) :=
  (rfl)

variable {F}

/-- **Dyadic multipliers are bounded on `Lᵖ` uniformly in the scale.** For every `f ∈ L²(V, F)`
and `1 ≤ p ≤ ∞`, `‖Mⱼ f‖_p ≤ ‖𝓕⁻ σ₀‖₁ ‖f‖_p`, where `Mⱼ` is the multiplier with symbol the `j`-th
dyadic dilate `σⱼ` of `σ`: its kernel `𝓕⁻ σⱼ` has the same `L¹` norm as `𝓕⁻ σ₀`. -/
theorem eLpNorm_dyadicMultiplier_le (σ : 𝓢(V, ℂ)) (j : ℤ) (f : Lp F 2 (volume : Measure V))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (φ.dyadicMultiplier F σ j f) p volume ≤
      eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) 1 volume * eLpNorm f p volume := by
  rw [← φ.eLpNorm_fourierInv_dyadicDilate σ j]
  exact (φ.dyadicDilate σ j).eLpNorm_fourierMultiplierCLM_toLp_le f hp

/-- **Dyadic multipliers in mixed norms.** For an almost everywhere strongly measurable
`G : β → L²(V, F)`, the multiplier `Mⱼ` with symbol the `j`-th dyadic dilate of `σ` costs at most
the factor `‖𝓕⁻ σ₀‖₁` in every mixed norm `L^p_b L^r_x` with `r ≥ 1`, uniformly in `j`; this is
`MeasureTheory.eLpNorm_eLpNorm_apply_le` for `T = Mⱼ`. -/
theorem eLpNorm_eLpNorm_dyadicMultiplier_le (σ : 𝓢(V, ℂ)) (j : ℤ) {β : Type*}
    [MeasurableSpace β] {ρ : Measure β} {G : β → Lp F 2 (volume : Measure V)}
    (hG : AEStronglyMeasurable G ρ) {p r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (fun b ↦ eLpNorm (φ.dyadicMultiplier F σ j (G b)) r volume) p ρ ≤
      eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) 1 volume *
        eLpNorm (fun b ↦ eLpNorm (G b) r volume) p ρ :=
  eLpNorm_eLpNorm_apply_le (φ.dyadicMultiplier F σ j).continuous
    (fun f ↦ φ.eLpNorm_dyadicMultiplier_le σ j f hr) hG

/-- **Reassembling a block from squared blocks.** If the cutoffs whose indices differ by at least
`L` have disjoint supports, as for the `L` of `ContDiffBump.exists_littlewoodPaley_mul_eq_zero φ`,
then `Pₗ f = ∑_{|d| < L} P_{d + l} P_{d + l} Qₗ Pₗ f` for every `f ∈ L²(V, F)`. Here `Pⱼ` is the
`L²` Fourier multiplier with any symbol in `L^∞` almost everywhere equal to `ψⱼ`, and `Qₗ` is the
dyadic multiplier of `ContDiffBump.invSumSq`, which inverts `∑ⱼ ψⱼ²` on the support of `ψₗ`. -/
theorem sum_fourierMultiplierCLM_fourierMultiplierCLM_dyadicMultiplier_invSumSq {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : V, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (l : ℤ)
    (f : Lp F 2 (volume : Measure V)) :
    ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, Lp.fourierMultiplierCLM F (m (d + l))
        (Lp.fourierMultiplierCLM F (m (d + l))
          (φ.dyadicMultiplier F φ.invSumSq l (Lp.fourierMultiplierCLM F (m l) f))) =
      Lp.fourierMultiplierCLM F (m l) f := by
  set θ : Lp ℂ ∞ (volume : Measure V) := (φ.dyadicDilate φ.invSumSq l).toLp ∞ volume
  -- As symbols in `L^∞`, `∑_{|d| < L} ψ_{d + l} ψ_{d + l} θ ψₗ = ψₗ`.
  have hsym : ∑ d ∈ Finset.Ioo (-(L : ℤ)) L,
      (m (d + l) • m (d + l) • θ • m l : Lp ℂ ∞ (volume : Measure V)) = m l := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum (Finset.Ioo (-(L : ℤ)) L)
        (fun d ↦ (m (d + l) • m (d + l) • θ • m l : Lp ℂ ∞ (volume : Measure V))),
      (Filter.eventually_all_finset _).2 fun d _ ↦
        Lp.coeFn_lpSMul (r := ∞) (m (d + l)) (m (d + l) • θ • m l),
      (Filter.eventually_all_finset _).2 fun d _ ↦ Lp.coeFn_lpSMul (r := ∞) (m (d + l)) (θ • m l),
      (Filter.eventually_all_finset _).2 fun d _ ↦ hm (d + l),
      Lp.coeFn_lpSMul (r := ∞) θ (m l), (φ.dyadicDilate φ.invSumSq l).coeFn_toLp ∞ volume, hm l]
      with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁, Finset.sum_apply, h₇,
      ← φ.sum_littlewoodPaley_mul_littlewoodPaley_mul_dyadicDilate_invSumSq hL l ξ]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [h₂ d hd, Pi.smul_apply', h₃ d hd, Pi.smul_apply', h₅, Pi.smul_apply', h₄ d hd, h₆, h₇,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
  simp only [dyadicMultiplier_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  conv_rhs => rw [← hsym]
  rw [Lp.fourierMultiplierCLM_sum, FunLike.coe_sum, Finset.sum_apply]

end ContDiffBump
