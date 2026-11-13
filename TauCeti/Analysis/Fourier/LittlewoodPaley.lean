/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Function.Lp.One
import TauCeti.MeasureTheory.Function.Lp.SequenceValued
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace

/-!
# The Littlewood–Paley square function theorem

Let `V` be a real inner product space of finite dimension `n ≥ 1`, let `φ` be a smooth bump
function on `V`, and let `ψ₀ = φ, ψ₁, ψ₂, …` be the inhomogeneous Littlewood–Paley partition built
from it (`ContDiffBump.inhomogeneousLittlewoodPaley`). The Littlewood–Paley blocks `Δⱼ` are the
`L²` Fourier multipliers with symbols `ψⱼ`, and the **Littlewood–Paley square function** of `f` is

`S f = (∑ⱼ ‖Δⱼ f‖²)^{1/2}`.

This file proves the Littlewood–Paley theorem `‖S f‖_p ≈ ‖f‖_p`: for a complex Hilbert space `F`
and `1 < p < ∞` there is a constant `C`, depending on `φ`, `p` and `F`, with

`‖S f‖_p ≤ C ‖f‖_p` and `‖f‖_p ≤ C ‖S f‖_p`

for every `f ∈ L²(V, F)` (`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le` and
`TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow`). Neither side is
assumed finite, so in particular `f ∈ Lᵖ` exactly when `S f ∈ Lᵖ`.

At `p = 2` the first inequality is stated for finite sums of blocks as
`TauCeti.exists_sum_norm_fourierMultiplierCLM_sq_le`: `∑_{j ∈ s} ‖Δⱼ f‖₂² ≤ L ‖f‖₂²`.

## The argument for `‖S f‖_p ≤ C ‖f‖_p`

The truncation `f ↦ (Δ₀ f, …, Δₙ f)` (`MeasureTheory.Lp.lpPi`) is a bounded operator
`L²(V, F) → L²(V, ℓ²(F))` and the inequality is the Calderón–Zygmund theorem for it, applied
uniformly in `n` (`TauCeti.exists_eLpNorm_le_of_hormander`), followed by monotone convergence as
`n → ∞` (`MeasureTheory.eLpNorm_iSup_eq_iSup_eLpNorm`).

* **`L²` bound.** Write `T` for the truncation; its adjoint is `T† (gⱼ) = ∑ⱼ Δⱼ gⱼ`. The
  operator `T† T = ∑_{j ≤ n} Δⱼ²` on `L²(V, F)` is the multiplier with symbol `∑_{j ≤ n} ψⱼ²`,
  which is bounded by a constant `L` independent of `n`, since at each frequency at most `L`
  consecutive pieces are nonzero and each lies in `[-1, 1]`
  (`ContDiffBump.exists_sum_sq_inhomogeneousLittlewoodPaley_le`).
* **Kernel.** Both the truncation and its adjoint are given by kernels dominated by differences
  of the `ℓ²`-valued Schwartz function `K_n z = ∑_{j ≤ n} (𝓕⁻ ψⱼ) z eⱼ`, the inverse Fourier
  transform of `ξ ↦ ∑_{j ≤ n} ψⱼ ξ eⱼ`.
* **Hörmander's condition.** The pieces `ξ ↦ ψⱼ ξ eⱼ` are band-limited at the scales `2 ^ j` with
  derivatives `O(2^{-jk})`, so `K_n` satisfies Hörmander's condition
  `∫_{‖x‖ > 2 ‖h‖} ‖K_n (x - h) - K_n x‖ dx ≤ B` uniformly in `n`
  (`SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le`).

The Calderón–Zygmund constant must not depend on `n`, so the vectors `(Δ₀ f, …, Δₙ f)` are placed
in the single Hilbert space `ℓ²(ℕ, F)` rather than in `Fⁿ⁺¹`.

## The argument for `‖f‖_p ≤ C ‖S f‖_p`

The reverse inequality follows from the first one at the conjugate exponent `q` by duality
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`). The pieces
`ψⱼ` and `ψₖ` have disjoint supports once `|j - k| ≥ L`
(`ContDiffBump.exists_inhomogeneousLittlewoodPaley_mul_eq_zero`), so `∑_{|k - j| < L} ψₖ ψⱼ = ψⱼ`
(`ContDiffBump.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley`), and the blocks are
self-adjoint. Hence, for `f, g ∈ L²(V, F)`,

`⟪∑_{j ≤ N} Δⱼ f, g⟫ = ∑_{j ≤ N} ∑_{|k - j| < L} ⟪Δⱼ f, Δₖ g⟫`,

which Cauchy–Schwarz for the banded double sum (`ENNReal.tsum_sum_Ico_mul_le`) bounds by
`2 L ∫ S f · S g`. The partial sums `∑_{j ≤ N} Δⱼ f` converge to `f` in `L²`
(`MeasureTheory.Lp.tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley`), and Hölder's
inequality and the first inequality at the exponent `q` give
`|⟪f, g⟫| ≤ 2 L C_q ‖S f‖_p ‖g‖_q`.

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

variable (φ : ContDiffBump (0 : V))

variable (V) in
/-- Schwartz functions with values in `ℓ²(ℕ, ℂ)`, with the real structure induced by the complex
one, which is the structure the Fourier transform on Schwartz space is stated for. -/
private abbrev L2Schwartz : Type _ :=
  @SchwartzMap V (lp (fun _ : ℕ ↦ ℂ) 2) _ _ _ NormedSpace.complexToReal

/-- The `ℓ²`-valued Schwartz function `ξ ↦ ψⱼ ξ eⱼ`. -/
private def vecSymbol (j : ℕ) : L2Schwartz V :=
  SchwartzMap.postcompCLM (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 2 j)
    (φ.inhomogeneousLittlewoodPaleySchwartz j)

private theorem vecSymbol_apply (j : ℕ) (ξ : V) :
    vecSymbol φ j ξ = lp.single 2 j (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
  rw [← φ.inhomogeneousLittlewoodPaleySchwartz_apply]
  -- This is `SchwartzMap.postcompCLM_apply`, which holds by `rfl`. It does not rewrite here: the
  -- real structure of `L2Schwartz V` is not reducibly the one `postcompCLM` produces.
  rfl

/-- The `k`-th derivative of `ξ ↦ ψⱼ ξ eⱼ` is bounded by that of `ψⱼ`. -/
private theorem norm_iteratedFDeriv_vecSymbol_le (j k : ℕ) (ξ : V) :
    ‖iteratedFDeriv ℝ k (vecSymbol φ j : V → lp (fun _ : ℕ ↦ ℂ) 2) ξ‖ ≤
      ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ := by
  set L : ℝ →L[ℝ] lp (fun _ : ℕ ↦ ℂ) 2 :=
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ ℂ) 2 j).comp Complex.ofRealCLM
  have hL : ‖L‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun r ↦ by simp [L]
  have hfun : (vecSymbol φ j : V → lp (fun _ : ℕ ↦ ℂ) 2) =
      L ∘ φ.inhomogeneousLittlewoodPaley j := funext fun ξ ↦ by
    simp [vecSymbol_apply, L]
  rw [hfun]
  refine (L.norm_iteratedFDeriv_comp_left
    (φ.contDiff_inhomogeneousLittlewoodPaley j (n := ⊤)).contDiffAt (mod_cast le_top)).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) hL

/-- If `φ.rOut ≤ 2 ^ m`, then `ξ ↦ ψⱼ ξ eⱼ` is supported in the ball of radius `2 ^ (j + m)`. -/
private theorem support_vecSymbol_subset {m : ℕ} (hm : φ.rOut ≤ 2 ^ m) (j : ℕ) :
    Function.support (vecSymbol φ j) ⊆ closedBall 0 (2 ^ ((j : ℤ) + m)) := by
  intro ξ hξ
  rw [Function.mem_support, vecSymbol_apply] at hξ
  have hψ : φ.inhomogeneousLittlewoodPaley j ξ ≠ 0 := fun h0 ↦ hξ (by simp [h0])
  have hlt : ‖ξ‖ < 2 ^ j * φ.rOut :=
    lt_of_not_ge fun hle ↦ hψ (φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hle)
  rw [mem_closedBall_zero_iff, zpow_add₀ two_ne_zero, zpow_natCast, zpow_natCast]
  exact hlt.le.trans (mul_le_mul_of_nonneg_left hm (by positivity))

/-- A derivative bound `‖D^k ψⱼ‖ ≤ B 2^{-jk}` gives, for the iterated directional derivatives of
`ξ ↦ ψⱼ ξ eⱼ` along an orthonormal basis, the bound `B 2^{mk} 2^{-(j + m)k}` at the scale
`2 ^ (j + m)`. -/
private theorem norm_iterate_lineDerivOp_vecSymbol_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {k : ℕ} {B : ℝ}
    (hB : ∀ (j : ℕ) (ξ : V),
      ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ ≤ B / (2 ^ j) ^ k)
    (m j : ℕ) (i : ι) (ξ : V) :
    ‖(∂_{b i})^[k] (vecSymbol φ j) ξ‖ ≤ B * (2 ^ m) ^ k / (2 ^ ((j : ℤ) + m)) ^ k := by
  rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  refine ((iteratedFDeriv ℝ k (vecSymbol φ j : V → lp (fun _ : ℕ ↦ ℂ) 2) ξ).le_opNorm
    _).trans ?_
  simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one]
  refine (norm_iteratedFDeriv_vecSymbol_le φ j k ξ).trans ((hB j ξ).trans_eq ?_)
  rw [zpow_add₀ two_ne_zero, zpow_natCast, zpow_natCast, mul_pow]
  field_simp

variable [MeasurableSpace V] [BorelSpace V]

/-- The `ℓ²`-valued kernel `z ↦ ∑_{j ≤ n} (𝓕⁻ ψⱼ) z eⱼ` of the truncated square function. -/
private def kernel (n : ℕ) : L2Schwartz V :=
  𝓕⁻ (∑ j ∈ Finset.range (n + 1), vecSymbol φ j)

private theorem kernel_apply (n : ℕ) (z : V) :
    kernel φ n z =
      ∑ j ∈ Finset.range (n + 1),
        lp.single 2 j (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) z) := by
  rw [kernel, FourierTransform.fourierInv_sum, sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact SchwartzMap.fourierInv_postcompCLM_apply _ (φ.inhomogeneousLittlewoodPaleySchwartz j) z

/-- **Hörmander's condition for the `ℓ²`-valued kernels**, uniformly in the truncation:
`∫_{‖x‖ > 2 ‖h‖} ‖K_n (x - h) - K_n x‖ dx ≤ B`. -/
private theorem exists_setIntegral_norm_kernel_sub_sub_le [Nontrivial V] :
    ∃ B, 0 ≤ B ∧ ∀ (n : ℕ) (h : V),
      ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖kernel φ n (x - h) - kernel φ n x‖ ≤ B := by
  set N := finrank ℝ V
  have hN : finrank ℝ V < 2 * N := by have := finrank_pos (R := ℝ) (M := V); omega
  obtain ⟨C, hC, hK⟩ := SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le
    (H := lp (fun _ : ℕ ↦ ℂ) 2) (stdOrthonormalBasis ℝ V) hN
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt φ.rOut (one_lt_two (α := ℝ))
  choose B hB0 hB using fun k ↦ φ.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_le k
  set A := ∑ k ∈ Finset.range (N + 1), B k * (2 ^ m) ^ k
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ ↦ mul_nonneg (hB0 k) (by positivity)
  refine ⟨C * A, mul_nonneg hC hA, fun n h ↦ ?_⟩
  -- Index the pieces by `ℤ`, shifted by `m` so that `ψⱼ` is supported in the ball of radius
  -- `2 ^ (j + m)`.
  set σ : ℤ → L2Schwartz V := fun i ↦ vecSymbol φ (i - m).toNat
  set s : Finset ℤ := (Finset.range (n + 1)).map
    ⟨fun j : ℕ ↦ (j : ℤ) + m, fun a b hab ↦ by simpa using hab⟩
  have hσ : ∀ j : ℕ, σ (j + m) = vecSymbol φ j := fun j ↦ by
    simp only [σ, add_sub_cancel_right, Int.toNat_natCast]
  have hsum : ∑ i ∈ s, σ i = ∑ j ∈ Finset.range (n + 1), vecSymbol φ j := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ ↦ hσ j
  have hmem : ∀ i ∈ s, ∃ j : ℕ, i = j + m ∧ σ i = vecSymbol φ j := fun i hi ↦ by
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    exact ⟨j, rfl, hσ j⟩
  have hsupp : ∀ i ∈ s, Function.support (σ i) ⊆ closedBall 0 (2 ^ i) := fun i hi ↦ by
    obtain ⟨j, rfl, hσj⟩ := hmem i hi
    rw [hσj]
    exact support_vecSymbol_subset φ hm.le j
  have hderiv : ∀ i ∈ s, ∀ k ≤ N, ∀ i' ξ,
      ‖(∂_{stdOrthonormalBasis ℝ V i'})^[k] (σ i) ξ‖ ≤ A / (2 ^ i) ^ k := by
    intro i hi k hk i' ξ
    obtain ⟨j, rfl, hσj⟩ := hmem i hi
    rw [hσj]
    refine (norm_iterate_lineDerivOp_vecSymbol_le φ _ (hB k) m j i' ξ).trans ?_
    exact div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun k ↦ B k * (2 ^ m) ^ k)
      (fun k _ ↦ mul_nonneg (hB0 k) (by positivity)) (Finset.mem_range.2 (by omega)))
      (by positivity)
  have := hK σ s hA hsupp hderiv h
  rwa [hsum] at this

/-! ### The truncated square function as a vector-valued operator -/

/-- The kernel `v ↦ ((𝓕⁻ ψⱼ) (x - y) v)ⱼ` of `Lp.lpPi 2 (Finset.range (n + 1)) (block φ)`. -/
private def sqKernel (n : ℕ) (x y : V) : F →L[ℝ] lp (fun _ : ℕ ↦ F) 2 :=
  ∑ j ∈ Finset.range (n + 1),
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).comp
      (lsmul ℝ ℂ (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (x - y)))

/-- The kernel `(wⱼ) ↦ ∑ⱼ (𝓕⁻ ψⱼ) (x - y) wⱼ` of `sqFunAdj φ n`. -/
private def sqKernelAdj (n : ℕ) (x y : V) : lp (fun _ : ℕ ↦ F) 2 →L[ℝ] F :=
  ∑ j ∈ Finset.range (n + 1),
    (lsmul ℝ ℂ (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (x - y))).comp
      (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j)

private theorem kernel_sub_kernel (n : ℕ) (z z' : V) :
    kernel φ n z - kernel φ n z' = ∑ j ∈ Finset.range (n + 1),
      lp.single 2 j
        (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) z -
          𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) z') := by
  simp only [kernel_apply, ← Finset.sum_sub_distrib, lp.single_sub]

private theorem norm_sqKernel_sub_le (n : ℕ) (x y y' : V) :
    ‖sqKernel (F := F) φ n x y - sqKernel φ n x y'‖ ≤
      ‖kernel φ n (x - y) - kernel φ n (x - y')‖ := by
  rw [kernel_sub_kernel, sqKernel, sqKernel, ← Finset.sum_sub_distrib]
  simp_rw [← comp_sub, ← map_sub]
  exact lp.norm_sum_single_comp_lsmul_le _ _

private theorem norm_sqKernelAdj_sub_le (n : ℕ) (x y y' : V) :
    ‖sqKernelAdj (F := F) φ n x y - sqKernelAdj φ n x y'‖ ≤
      ‖kernel φ n (x - y) - kernel φ n (x - y')‖ := by
  rw [kernel_sub_kernel, sqKernelAdj, sqKernelAdj, ← Finset.sum_sub_distrib]
  simp_rw [← sub_comp, ← map_sub]
  exact lp.norm_sum_lsmul_comp_evalCLM_le _ _

private theorem stronglyMeasurable_sqKernel (n : ℕ) :
    StronglyMeasurable (Function.uncurry (sqKernel (F := F) φ n)) :=
  Finset.stronglyMeasurable_fun_sum (Finset.range (n + 1))
    (f := fun j (p : V × V) ↦ (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).comp
      (lsmul ℝ ℂ (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (p.1 - p.2)))) fun j _ ↦
    (continuous_const.clm_comp (lsmul ℝ ℂ).continuous).comp_stronglyMeasurable
      ((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).continuous.comp
        continuous_sub).stronglyMeasurable

private theorem stronglyMeasurable_sqKernelAdj (n : ℕ) :
    StronglyMeasurable (Function.uncurry (sqKernelAdj (F := F) φ n)) :=
  Finset.stronglyMeasurable_fun_sum (Finset.range (n + 1))
    (f := fun j (p : V × V) ↦
      (lsmul ℝ ℂ (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (p.1 - p.2))).comp
      (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j)) fun j _ ↦
    ((lsmul ℝ ℂ).continuous.clm_comp continuous_const).comp_stronglyMeasurable
      ((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).continuous.comp
        continuous_sub).stronglyMeasurable

variable [CompleteSpace F]

/-- The Littlewood–Paley block `Δⱼ` on `L²(V, F)`, as a real-linear operator. -/
private def block (j : ℕ) : Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  (Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞)).restrictScalars ℝ

private theorem block_apply (j : ℕ) (f : Lp F 2 (volume : Measure V)) :
    block φ j f = Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞) f :=
  (rfl)

private theorem coeFn_toLp_symbol (j : ℕ) :
    (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ (volume : Measure V) =ᵐ[volume]
      fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
  (φ.inhomogeneousLittlewoodPaleySchwartz j).coeFn_toLp ∞ volume |>.mono fun ξ h ↦ by
    rw [h, φ.inhomogeneousLittlewoodPaleySchwartz_apply]

/-- Any symbol in `L^∞` almost everywhere equal to `ψⱼ` is
`(φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞`. -/
private theorem eq_toLp_symbol {j : ℕ} {m : Lp ℂ ∞ (volume : Measure V)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) :
    m = (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume :=
  Lp.ext (hm.trans (coeFn_toLp_symbol φ j).symm)

/-- The operator `(gⱼ) ↦ ∑_{j ≤ n} Δⱼ gⱼ`, the adjoint of
`Lp.lpPi 2 (Finset.range (n + 1)) (block φ)`. -/
private def sqFunAdj (n : ℕ) :
    Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  ∑ j ∈ Finset.range (n + 1),
    block φ j ∘L (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume

/-- The block `Δⱼ` is convolution with `𝓕⁻ ψⱼ`. -/
private theorem coeFn_block (j : ℕ) (f : Lp F 2 (volume : Measure V)) :
    block φ j f =ᵐ[volume]
      fun x ↦ ∫ z, 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (x - z) • f z :=
  (φ.inhomogeneousLittlewoodPaleySchwartz j).coeFn_fourierMultiplierCLM_toLp f

private theorem ae_sqFun_eq_integral (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, Lp.lpPi 2 (Finset.range (n + 1)) (block φ) f x = ∫ z, sqKernel φ n x z (f z) := by
  filter_upwards [Lp.coeFn_lpPi 2 (Finset.range (n + 1)) (block φ) f,
    ae_all_iff.2 fun j ↦ coeFn_block φ j f] with x hx hjx
  rw [hx]
  simp only [sqKernel, sum_apply, coe_comp, Function.comp_apply, lsmul_apply,
    lp.singleContinuousLinearMap_apply]
  rw [integral_finsetSum _ fun j _ ↦ ?_]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hjx j]
    exact ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).integral_comp_comm
      ((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).integrable_sub_smul one_le_two
        (Lp.memLp f) x)).symm
  · exact (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).integrable_comp
      ((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).integrable_sub_smul one_le_two
        (Lp.memLp f) x)

private theorem ae_sqFunAdj_eq_integral (n : ℕ)
    (g : Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V)) :
    ∀ᵐ x, sqFunAdj φ n g x = ∫ z, sqKernelAdj φ n x z (g z) := by
  set u : ℕ → Lp F 2 (volume : Measure V) := fun j ↦
    (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume g
  have hu : ∀ j, (u j : V → F) =ᵐ[volume] fun z ↦ g z j := fun j ↦
    (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).coeFn_compLpL g
  have hint : ∀ j x,
      Integrable (fun z ↦ 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (x - z) • g z j) :=
    fun j x ↦
    ((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).integrable_sub_smul one_le_two (Lp.memLp (u j))
      x).congr
      ((hu j).mono fun z hz ↦ by simp [hz])
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n + 1)) fun j ↦ block φ j (u j),
    ae_all_iff.2 fun j ↦ coeFn_block φ j (u j)] with x hx hjx
  rw [sqFunAdj, sum_apply]
  simp only [comp_apply]
  rw [hx]
  simp only [sqKernelAdj, sum_apply, coe_comp, Function.comp_apply, lsmul_apply, lp.evalCLM_apply]
  rw [integral_finsetSum _ fun j _ ↦ hint j x]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hjx j]
  exact integral_congr_ae ((hu j).mono fun z hz ↦ by simp [hz])

/-- The symbols `ψⱼ` are real, so the blocks are self-adjoint. -/
private theorem isSelfAdjoint_fourierMultiplierCLM_toLp_symbol (j : ℕ) :
    IsSelfAdjoint (Lp.fourierMultiplierCLM F
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ (volume : Measure V))) :=
  Lp.isSelfAdjoint_fourierMultiplierCLM
    (Lp.star_eq_self_of_ae_eq_ofReal (coeFn_toLp_symbol φ j))

private theorem inner_block_left (j : ℕ) (f g : Lp F 2 (volume : Measure V)) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    inner ℝ (block φ j f) g = inner ℝ f (block φ j g) := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [L2.real_inner_eq_re_inner, L2.real_inner_eq_re_inner]
  exact congrArg RCLike.re ((isSelfAdjoint_fourierMultiplierCLM_toLp_symbol φ j).isSymmetric f g)

private theorem adjoint_lpPi_block (n : ℕ) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    adjoint (Lp.lpPi 2 (Finset.range (n + 1)) (block (F := F) φ)) = sqFunAdj φ n := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine ((eq_adjoint_iff _ _).2 fun g f ↦ ?_).symm
  simp only [sqFunAdj, Lp.lpPi_apply, sum_apply, comp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_block_left, L2.inner_evalCLM_compLpL]

private theorem sqFunAdj_lpPi_block (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    sqFunAdj φ n (Lp.lpPi 2 (Finset.range (n + 1)) (block φ) f) =
      ∑ j ∈ Finset.range (n + 1), block φ j (block φ j f) := by
  simp only [sqFunAdj, sum_apply, comp_apply]
  exact Finset.sum_congr rfl fun j hj ↦ congrArg _ (Lp.evalCLM_compLpL_lpPi 2 (block φ) hj f)

/-- The symbol `∑ⱼ ψⱼ²` of `∑ⱼ Δⱼ²` is bounded uniformly in the set of indices. -/
private theorem exists_norm_sum_toLp_symbol_smul_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s : Finset ℕ, ‖∑ j ∈ s,
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume •
          (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V))‖ ≤
        L := by
  obtain ⟨L, hL⟩ := φ.exists_sum_sq_inhomogeneousLittlewoodPaley_le
  refine ⟨L, Nat.cast_nonneg L, fun s ↦ ?_⟩
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg L) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j ↦
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume •
          (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)),
    ae_all_iff.2 fun j ↦ Lp.coeFn_lpSMul (r := ∞)
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ (volume : Measure V))
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume),
    ae_all_iff.2 fun j ↦
      (φ.inhomogeneousLittlewoodPaleySchwartz j).coeFn_toLp ∞ (volume : Measure V)]
    with ξ h₁ h₂ h₃
  rw [h₁]
  simp only [h₂, Pi.smul_apply', h₃, φ.inhomogeneousLittlewoodPaleySchwartz_apply, smul_eq_mul,
    ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ mul_self_nonneg _)]
  simpa [sq] using hL s ξ

/-- **The `L²` bound for the blocks**, uniformly in the set of indices:
`∑_{j ∈ s} ‖Δⱼ f‖² = Re ⟪f, ∑_{j ∈ s} Δⱼ² f⟫ ≤ L ‖f‖²`, since `∑_{j ∈ s} Δⱼ²` is the multiplier
with symbol `∑_{j ∈ s} ψⱼ²`. -/
private theorem exists_sum_norm_block_sq_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (s : Finset ℕ) (f : Lp F 2 (volume : Measure V)),
      ∑ j ∈ s, ‖block φ j f‖ ^ 2 ≤ L * ‖f‖ ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_sum_toLp_symbol_smul_le φ
  refine ⟨L, hL0, fun s f ↦ ?_⟩
  have h : ∑ j ∈ s, ‖block φ j f‖ ^ 2 = RCLike.re ⟪f, Lp.fourierMultiplierCLM F (∑ j ∈ s,
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume •
        (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume :
          Lp ℂ ∞ (volume : Measure V))) f⟫_ℂ := by
    simp only [Lp.fourierMultiplierCLM_sum, sum_apply, inner_sum, map_sum,
      ← Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [block_apply, norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg RCLike.re ((isSelfAdjoint_fourierMultiplierCLM_toLp_symbol φ j).isSymmetric _ _)
  rw [h]
  calc RCLike.re ⟪f, Lp.fourierMultiplierCLM F _ f⟫_ℂ ≤ ‖f‖ * ‖Lp.fourierMultiplierCLM F _ f‖ :=
        re_inner_le_norm _ _
    _ ≤ ‖f‖ * (L * ‖f‖) := by
        gcongr
        exact (Lp.norm_fourierMultiplierCLM_apply_le _ f).trans (by gcongr; exact hL _)
    _ = L * ‖f‖ ^ 2 := by ring

/-- **The `L²` bound**, uniformly in the truncation: `‖(Δ₀ f, …, Δₙ f)‖ ≤ √L ‖f‖`. -/
private theorem exists_norm_sqFun_apply_le :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (n : ℕ) (f : Lp F 2 (volume : Measure V)),
        ‖Lp.lpPi 2 (Finset.range (n + 1)) (block φ) f‖ ≤ √L * ‖f‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_sum_norm_block_sq_le (F := F) φ
  refine ⟨L, hL0, fun n f ↦ ?_⟩
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hL0, ← real_inner_self_eq_norm_sq, ← adjoint_inner_right,
    adjoint_lpPi_block, sqFunAdj_lpPi_block, inner_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) (hL _ f)
  rw [← inner_block_left, real_inner_self_eq_norm_sq]

/-- **The Calderón–Zygmund bound for the truncated square functions**, uniformly in the
truncation. -/
private theorem exists_eLpNorm_sqFun_le [Nontrivial V] {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ (n : ℕ) (f : Lp F 2 (volume : Measure V)),
      eLpNorm (Lp.lpPi 2 (Finset.range (n + 1)) (block φ) f) p volume ≤ C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, -, hB⟩ := exists_setIntegral_norm_kernel_sub_sub_le φ
  obtain ⟨L, -, hL⟩ := exists_norm_sqFun_apply_le (F := F) φ
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_hormander (V := V) (H := F)
    (K := lp (fun _ : ℕ ↦ F) 2) (M := ENNReal.ofReal √L) (B := ENNReal.ofReal B)
    (B' := ENNReal.ofReal B) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hp hp_top
  refine ⟨C, fun n f ↦ hC (Lp.lpPi 2 (Finset.range (n + 1)) (block φ)) (sqKernel φ n)
    (sqKernelAdj φ n) ?_
    (stronglyMeasurable_sqKernel φ n) (stronglyMeasurable_sqKernelAdj φ n)
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel φ n).integrable (norm_sqKernel_sub_le φ n)
      (hB n))
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel φ n).integrable
      (norm_sqKernelAdj_sub_le φ n) (hB n))
    (fun g _ _ _ ↦ (ae_sqFun_eq_integral φ n g).mono fun _ hx _ ↦ hx)
    (fun g _ _ _ ↦ (adjoint_lpPi_block (F := F) φ n) ▸
      (ae_sqFunAdj_eq_integral φ n g).mono fun _ hx _ ↦ hx)
    f⟩
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (opNorm_le_bound _ (Real.sqrt_nonneg _) (hL n))

end LittlewoodPaleySquare

open LittlewoodPaleySquare in
/-- **The Littlewood–Paley square function inequality.** Let `V` be a real inner product space
of finite dimension `n ≥ 1`, let `φ` be a smooth bump function on `V`, and let `1 < p < ∞`. Let
`Δⱼ` be the `L²` Fourier multipliers with the pieces `ψ₀ = φ`, `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`
of the inhomogeneous Littlewood–Paley partition as symbols. For every complex Hilbert space `F`
there is a constant `C` such that for every `f ∈ L²(V, F)`,

`‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p ≤ C ‖f‖_p`.

Each symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le [Nontrivial V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℕ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
          volume ≤ C * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_sqFun_le (F := F) φ hp hp_top
  refine ⟨C, fun m hm f ↦ ?_⟩
  have hb : ∀ j, Lp.fourierMultiplierCLM F (m j) f = block φ j f := fun j ↦ by
    rw [eq_toLp_symbol φ (hm j), block_apply]
  simp_rw [hb]
  -- The full square sum is the increasing limit of the partial sums `∑_{j ≤ n}`.
  set G : ℕ → V → ℝ≥0∞ := fun n x ↦
    (∑ j ∈ Finset.range (n + 1), ‖block φ j f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hG : ∀ x, (∑' j, ‖block φ j f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) = ⨆ n, G n x := fun x ↦ by
    rw [← ENNReal.iSup_rpow_of_pos (by norm_num),
      ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)]
  have hmeas : ∀ n, AEMeasurable (G n) := fun n ↦
    (Finset.aemeasurable_fun_sum _ fun j _ ↦
      (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  have hmono : ∀ x, Monotone fun n ↦ G n x := fun x a b hab ↦ ENNReal.rpow_le_rpow
    (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))) (by norm_num)
  simp_rw [hG]
  rw [eLpNorm_iSup_eq_iSup_eLpNorm hmeas (.of_forall hmono)]
  refine iSup_le fun n ↦ (eLpNorm_mono_eNorm_ae (hmeas n).aestronglyMeasurable ?_).trans (hC n f)
  -- Pointwise, `G n` is the `ℓ²` norm of `(Δ₀ f, …, Δₙ f)`.
  filter_upwards [Lp.coeFn_lpPi 2 (Finset.range (n + 1)) (block φ) f] with x hx
  rw [hx, eNorm_eq_self, lp.enorm_sum_single]

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
  obtain ⟨L, hL0, hL⟩ := exists_sum_norm_block_sq_le (F := F) φ
  refine ⟨L, hL0, fun m hm f s ↦ le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) (hL s f)⟩
  rw [eq_toLp_symbol φ (hm j), block_apply]

end TauCeti

/-! ### Littlewood–Paley reconstruction in `L²` -/

namespace MeasureTheory.Lp

open scoped Topology

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
  -- The partial sums are the multipliers with the symbols `∑_{j < N} ψⱼ`, which take values in
  -- `[0, 1]` and tend to `1` at every frequency.
  have hae : ∀ᵐ ξ ∂(volume : Measure V), ∀ N,
      (∑ j ∈ Finset.range N, m j) ξ =
        ∑ j ∈ Finset.range N, (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
    refine ae_all_iff.2 fun N ↦ ?_
    filter_upwards [coeFn_fun_finsetSum (Finset.range N) m, ae_all_iff.2 hm] with ξ h₁ h₂
    rw [h₁]
    exact Finset.sum_congr rfl fun j _ ↦ h₂ j
  have h1 : MemLp (fun _ : V ↦ (1 : ℂ)) ∞ volume := memLp_top_const 1
  have h := tendsto_fourierMultiplierCLM_apply (F := F) (l := atTop)
    (m := fun N ↦ ∑ j ∈ Finset.range N, m j) (m₀ := h1.toLp _) (C := 1) ?_ ?_ f
  · rw [fourierMultiplierCLM_of_ae_eq_const h1.coeFn_toLp] at h
    simpa only [one_smul, id_apply, fourierMultiplierCLM_sum, FunLike.coe_sum,
      Finset.sum_apply] using h
  · refine Eventually.of_forall fun N ↦ ?_
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one (eLpNormEssSup_le_of_ae_bound ?_)
    filter_upwards [hae] with ξ hξ
    rw [hξ N]
    rcases N with _ | N
    · simp
    · rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range, Complex.norm_real,
        Real.norm_of_nonneg φ.nonneg]
      exact φ.le_one
  · filter_upwards [hae, h1.coeFn_toLp] with ξ h₁ h₂
    simp only [h₁, h₂]
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp
      (φ.hasSum_inhomogeneousLittlewoodPaley ξ).tendsto_sum_nat

end MeasureTheory.Lp

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ### The reverse inequality -/

namespace LittlewoodPaleySquare

variable (φ : ContDiffBump (0 : V)) [MeasurableSpace V] [BorelSpace V] [CompleteSpace F]

/-- If the pieces whose indices differ by at least `L` have disjoint supports, then
`∑_{|k - j| < L} ψₖ ψⱼ = ψⱼ`, as an identity of symbols in `L^∞`. -/
private theorem sum_toLp_symbol_smul_toLp_symbol {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0) (j : ℕ) :
    ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
      ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ volume •
          (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)) =
      (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.Ico (j + 1 - L) (j + L)) fun k ↦
      ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ volume •
          (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)),
    ae_all_iff.2 fun k ↦ Lp.coeFn_lpSMul (r := ∞)
      ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ (volume : Measure V))
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume),
    ae_all_iff.2 fun k ↦
      (φ.inhomogeneousLittlewoodPaleySchwartz k).coeFn_toLp ∞ (volume : Measure V)]
    with ξ h₁ h₂ h₃
  rw [h₁]
  simp only [h₂, Pi.smul_apply', h₃, φ.inhomogeneousLittlewoodPaleySchwartz_apply, smul_eq_mul,
    ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, ← Finset.sum_mul, ← φ.enlargedLittlewoodPaley_apply,
    φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]

/-- The block `Δⱼ f` only sees the blocks of `g` whose indices are within `L` of `j`:
`⟪Δⱼ f, g⟫ = ∑_{|k - j| < L} ⟪Δⱼ f, Δₖ g⟫`. -/
private theorem inner_fourierMultiplierCLM_eq_sum {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0) (j : ℕ)
    (f g : Lp F 2 (volume : Measure V)) :
    ⟪Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f, g⟫_ℂ =
      ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
        ⟪Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f,
          Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ volume)
            g⟫_ℂ := by
  have h : Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f =
      ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
        Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ volume)
          (Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume)
            f) := by
    simp only [Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, ← sum_apply,
      ← Lp.fourierMultiplierCLM_sum, sum_toLp_symbol_smul_toLp_symbol φ hL]
  conv_lhs => rw [h]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact (isSelfAdjoint_fourierMultiplierCLM_toLp_symbol φ k).isSymmetric _ _

/-- The pairing bound `|⟪∑_{j ≤ N} Δⱼ f, g⟫| ≤ 2 L ∫ S f · S g` for the partial sums of `f`. -/
private theorem enorm_inner_sum_fourierMultiplierCLM_le {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0) (N : ℕ)
    (f g : Lp F 2 (volume : Measure V)) :
    ‖⟪∑ j ∈ Finset.range (N + 1),
        Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f,
      g⟫_ℂ‖ₑ ≤
      2 * L * ∫⁻ x,
        (∑' j, ‖Lp.fourierMultiplierCLM F
            ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖Lp.fourierMultiplierCLM F
            ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ volume) g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
  set M : ℕ → Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V) :=
    fun j ↦ Lp.fourierMultiplierCLM F ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume)
  have hmeas : ∀ j k, AEMeasurable (fun x ↦ ‖M j f x‖ₑ * ‖M k g x‖ₑ) :=
    fun j k ↦ (Lp.aestronglyMeasurable _).eNorm.mul (Lp.aestronglyMeasurable _).eNorm
  calc ‖⟪∑ j ∈ Finset.range (N + 1), M j f, g⟫_ℂ‖ₑ
      = ‖∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          ∫ x, ⟪M j f x, M k g x⟫_ℂ‖ₑ := by
        rw [sum_inner]
        refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
        rw [inner_fourierMultiplierCLM_eq_sum φ hL]
        simp only [M, L2.inner_def]
    _ ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          ∫⁻ x, ‖M j f x‖ₑ * ‖M k g x‖ₑ :=
        (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ (eNorm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ (eNorm_integral_le_lintegral_eNorm _).trans
            (lintegral_mono fun x ↦ eNorm_inner_le_eNorm _ _)))
    _ = ∫⁻ x, ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          ‖M j f x‖ₑ * ‖M k g x‖ₑ := by
        rw [lintegral_finsetSum' _ fun j _ ↦ Finset.aemeasurable_fun_sum _ fun k _ ↦ hmeas j k]
        exact Finset.sum_congr rfl fun j _ ↦
          (lintegral_finsetSum' _ fun k _ ↦ hmeas j k).symm
    _ ≤ ∫⁻ x, 2 * L * ((∑' j, ‖M j f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖M k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) :=
        lintegral_mono fun x ↦ (sum_le_tsum _).trans (ENNReal.tsum_sum_Ico_mul_le L _ _)
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

/-- **The pairing bound** behind the reverse inequality: `|⟪f, g⟫| ≤ 2 L ∫ S f · S g`, where `S`
is the square function and the pieces whose indices differ by at least `L` have disjoint
supports. -/
private theorem enorm_inner_le_mul_lintegral {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (f g : Lp F 2 (volume : Measure V)) :
    ‖⟪f, g⟫_ℂ‖ₑ ≤
      2 * L * ∫⁻ x,
        (∑' j, ‖Lp.fourierMultiplierCLM F
            ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖Lp.fourierMultiplierCLM F
            ((φ.inhomogeneousLittlewoodPaleySchwartz k).toLp ∞ volume) g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) :=
  le_of_tendsto' ((continuous_eNorm.tendsto _).comp
    (((Lp.tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley φ
      (coeFn_toLp_symbol φ) f).comp (tendsto_add_atTop_nat 1)).inner tendsto_const_nhds))
    (enorm_inner_sum_fourierMultiplierCLM_le φ hL · f g)

end LittlewoodPaleySquare

open LittlewoodPaleySquare in
/-- **The reverse Littlewood–Paley square function inequality.** Let `V` be a real inner product
space of finite dimension `n ≥ 1`, let `φ` be a smooth bump function on `V`, and let `1 < p < ∞`.
Let `Δⱼ` be the `L²` Fourier multipliers with the pieces `ψ₀ = φ`,
`ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` of the inhomogeneous Littlewood–Paley partition as symbols.
For every complex Hilbert space `F` there is a constant `C` such that for every `f ∈ L²(V, F)`,

`‖f‖_p ≤ C ‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p`.

Neither side is assumed finite: in particular `f ∈ Lᵖ` as soon as its square function is. Each
symbol enters as any element of `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow [Nontrivial V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℕ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f p volume ≤ C * eLpNorm
          (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  -- The conjugate exponent `q = p / (p - 1)` also lies in `(1, ∞)`.
  set P := p.toReal
  have hP : 1 < P := by simpa using (ENNReal.toReal_lt_toReal (by norm_num) hp_top).2 hp
  set q := ENNReal.ofReal (P / (P - 1))
  have hq : 1 < q := ENNReal.one_lt_ofReal.2 (by rw [lt_div_iff₀ (by linarith)]; linarith)
  have : p.HolderConjugate q := by
    refine ENNReal.HolderConjugate.of_toReal ?_
    rw [ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]
    exact Real.HolderConjugate.conjExponent hP
  obtain ⟨C, hC⟩ := exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le (F := F) φ hq
    ENNReal.ofReal_ne_top
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  refine ⟨2 * L * C, fun m hm f ↦ ?_⟩
  have hm' : ∀ j, m j = (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume := fun j ↦
    eq_toLp_symbol φ (hm j)
  simp_rw [hm']
  set S : Lp F 2 (volume : Measure V) → V → ℝ≥0∞ := fun f x ↦
    (∑' j, ‖Lp.fourierMultiplierCLM F
      ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hS : ∀ f, AEMeasurable (S f) := fun f ↦
    (AEMeasurable.tsum fun j ↦ (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  -- By duality, it suffices to bound the pairing of `f` with a bounded `g` of finite-measure
  -- support, which is an element `G` of `L²`.
  refine (Lp.aestronglyMeasurable f).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ)
    (q' := q) hp_top fun g s hs hgs hg ↦ ?_
  have hg2 : MemLp g 2 volume := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  set G := hg2.toLp g
  have hGg : (G : V → F) =ᵐ[volume] g := hg2.coeFn_toLp
  have hpair : ∫ x, ⟪f x, g x⟫_ℂ = ⟪f, G⟫_ℂ := by
    rw [L2.inner_def]
    exact integral_congr_ae (hGg.mono fun x hx ↦ by simp only [hx])
  -- Hölder's inequality and the square function inequality at the exponent `q` for `G`.
  have hHolder : ∫⁻ x, S f x * S G x ≤ eLpNorm (S f) p volume * eLpNorm (S G) q volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (μ := volume) (p := p) (q := q)
      (r := 1) (fun a b : ℝ≥0∞ ↦ a * b) 1 (f := S f) (g := S G)
      (fun _ _ ↦ ((hS f).mul (hS G)).aestronglyMeasurable)
      (ae_of_all _ fun x ↦ by simp) zero_lt_one
    rw [eLpNorm_one_eq_lintegral_eNorm (f := fun x ↦ S f x * S G x)
      ((hS f).mul (hS G)).aestronglyMeasurable] at h
    simpa only [eNorm_eq_self, one_mul] using h
  have hSG : eLpNorm (S G) q volume ≤ C * eLpNorm g q volume := by
    rw [← eLpNorm_congr_ae hGg]
    exact hC _ (coeFn_toLp_symbol φ) G
  rw [hpair]
  calc ‖⟪f, G⟫_ℂ‖ₑ ≤ 2 * L * ∫⁻ x, S f x * S G x := enorm_inner_le_mul_lintegral φ hL f G
    _ ≤ 2 * L * (eLpNorm (S f) p volume * (C * eLpNorm g q volume)) := by
        gcongr
        exact hHolder.trans (by gcongr)
    _ = ↑(2 * L * C) * eLpNorm (S f) p volume * eLpNorm g q volume := by
        push_cast
        ring

end TauCeti
