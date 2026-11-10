/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace

/-!
# The Littlewood–Paley square function inequalities

Let `V` be a real inner product space of finite dimension `n ≥ 1`, let `φ` be a smooth bump
function on `V`, and let `ψ₀ = φ, ψ₁, ψ₂, …` be the inhomogeneous Littlewood–Paley partition built
from it (`ContDiffBump.inhomogeneousLittlewoodPaley`). The Littlewood–Paley blocks `Δⱼ` are the
`L²` Fourier multipliers with symbols `ψⱼ`, and the **Littlewood–Paley square function** of `f` is

`S f = (∑ⱼ ‖Δⱼ f‖²)^{1/2}`.

This file proves the Littlewood–Paley theorem `‖S f‖_p ≈ ‖f‖_p`: for a complex Hilbert space `F`
and `1 < p < ∞` there are constants `C` and `C'`, depending on `φ`, `p` and `F`, with

`‖S f‖_p ≤ C ‖f‖_p` and `‖f‖_p ≤ C' ‖S f‖_p`

for every `f ∈ L²(V, F)` (`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le` and
`TauCeti.exists_eLpNorm_le_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow`). Along the way, the
partial sums `∑_{j < N} Δⱼ f` converge to `f` in `L²`
(`MeasureTheory.Lp.tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley`).

## The upper inequality

The truncation `f ↦ (Δ₀ f, …, Δₙ f)` is a bounded operator `L²(V, F) → L²(V, ℓ²(F))` and the
inequality is the Calderón–Zygmund theorem for it, applied uniformly in `n`
(`TauCeti.exists_eLpNorm_le_of_hormander`), followed by monotone convergence as `n → ∞`
(`MeasureTheory.eLpNorm_iSup_eq_iSup_eLpNorm`).

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

## The reverse inequality

The reverse inequality follows from the upper one in the dual exponent `p'` by duality. The
`Lᵖ` norm of `f` is the supremum of `‖∫ ⟪f, g⟫‖` over bounded `g` of finite-measure support with
`‖g‖_{p'} ≤ 1` (`AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`), and such `g`
lie in `L²`.

* **Reconstruction.** The partial sums `∑_{j ≤ N} Δⱼ f` are the multipliers with symbols
  `φ (2^{-N} ·)`, which take values in `[0, 1]` and tend to `1`, so they converge to `f` in `L²`
  and `⟪f, g⟫ = lim_N ∑_{j ≤ N} ⟪Δⱼ f, g⟫`.
* **Almost orthogonality.** The pieces `ψⱼ` and `ψₖ` have disjoint supports once `|j - k| ≥ L`
  (`ContDiffBump.exists_inhomogeneousLittlewoodPaley_mul_eq_zero`), and the blocks are
  self-adjoint, so `⟪Δⱼ f, g⟫ = ∑_{|k - j| < L} ⟪Δⱼ f, Δₖ g⟫`.
* **Cauchy–Schwarz.** Pointwise, `∑ⱼ ‖Δⱼ f‖ ∑_{|k - j| < L} ‖Δₖ g‖ ≤ 2 L S f · S g`, and Hölder's
  inequality with the upper inequality in `L^{p'}` gives
  `‖⟪f, g⟫‖ ≤ 2 L ‖S f‖_p ‖S g‖_{p'} ≤ 2 L C ‖S f‖_p ‖g‖_{p'}`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Theorem 6.1.2 (both inequalities, the reverse
  one by duality) and Section 5.6 (vector-valued inequalities).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  Section 1.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap ContDiff LineDeriv
open FourierTransform MeasureTheory Metric Filter ContinuousLinearMap Module

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace LittlewoodPaleySquare

variable (φ : ContDiffBump (0 : V))

/-- The piece `ψⱼ` of the inhomogeneous Littlewood–Paley partition, as a complex Schwartz
function. -/
private def symbol (j : ℕ) : 𝓢(V, ℂ) :=
  ((φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff_inhomogeneousLittlewoodPaley j))

private theorem symbol_apply (j : ℕ) (ξ : V) :
    symbol φ j ξ = (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) :=
  HasCompactSupport.toSchwartzMap_toFun _ _ ξ

variable (V) in
/-- Schwartz functions with values in `ℓ²(ℕ, ℂ)`, with the real structure induced by the complex
one, which is the structure the Fourier transform on Schwartz space is stated for. -/
private abbrev L2Schwartz : Type _ :=
  @SchwartzMap V (lp (fun _ : ℕ ↦ ℂ) 2) _ _ _ NormedSpace.complexToReal

/-- The `ℓ²`-valued Schwartz function `ξ ↦ ψⱼ ξ eⱼ`. -/
private def vecSymbol (j : ℕ) : L2Schwartz V :=
  SchwartzMap.postcompCLM (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 2 j) (symbol φ j)

private theorem vecSymbol_apply (j : ℕ) (ξ : V) :
    vecSymbol φ j ξ = lp.single 2 j (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
  rw [← symbol_apply]
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
    kernel φ n z = ∑ j ∈ Finset.range (n + 1), lp.single 2 j (𝓕⁻ (symbol φ j) z) := by
  rw [kernel, FourierTransform.fourierInv_sum, sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact SchwartzMap.fourierInv_postcompCLM_apply _ (symbol φ j) z

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

/-- The kernel `v ↦ ((𝓕⁻ ψⱼ) (x - y) v)ⱼ` of `sqFun φ n`. -/
private def sqKernel (n : ℕ) (x y : V) : F →L[ℝ] lp (fun _ : ℕ ↦ F) 2 :=
  ∑ j ∈ Finset.range (n + 1),
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).comp (lsmul ℝ ℂ (𝓕⁻ (symbol φ j) (x - y)))

/-- The kernel `(wⱼ) ↦ ∑ⱼ (𝓕⁻ ψⱼ) (x - y) wⱼ` of `sqFunAdj φ n`. -/
private def sqKernelAdj (n : ℕ) (x y : V) : lp (fun _ : ℕ ↦ F) 2 →L[ℝ] F :=
  ∑ j ∈ Finset.range (n + 1),
    (lsmul ℝ ℂ (𝓕⁻ (symbol φ j) (x - y))).comp (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j)

private theorem kernel_sub_kernel (n : ℕ) (z z' : V) :
    kernel φ n z - kernel φ n z' = ∑ j ∈ Finset.range (n + 1),
      lp.single 2 j (𝓕⁻ (symbol φ j) z - 𝓕⁻ (symbol φ j) z') := by
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
      (lsmul ℝ ℂ (𝓕⁻ (symbol φ j) (p.1 - p.2)))) fun j _ ↦
    (continuous_const.clm_comp (lsmul ℝ ℂ).continuous).comp_stronglyMeasurable
      ((𝓕⁻ (symbol φ j)).continuous.comp continuous_sub).stronglyMeasurable

private theorem stronglyMeasurable_sqKernelAdj (n : ℕ) :
    StronglyMeasurable (Function.uncurry (sqKernelAdj (F := F) φ n)) :=
  Finset.stronglyMeasurable_fun_sum (Finset.range (n + 1))
    (f := fun j (p : V × V) ↦ (lsmul ℝ ℂ (𝓕⁻ (symbol φ j) (p.1 - p.2))).comp
      (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j)) fun j _ ↦
    ((lsmul ℝ ℂ).continuous.clm_comp continuous_const).comp_stronglyMeasurable
      ((𝓕⁻ (symbol φ j)).continuous.comp continuous_sub).stronglyMeasurable

variable [CompleteSpace F]

/-- The Littlewood–Paley block `Δⱼ` on `L²(V, F)`, as a real-linear operator. -/
private def block (j : ℕ) : Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  (Lp.fourierMultiplierCLM F ((symbol φ j).toLp ∞)).restrictScalars ℝ

private theorem block_apply (j : ℕ) (f : Lp F 2 (volume : Measure V)) :
    block φ j f = Lp.fourierMultiplierCLM F ((symbol φ j).toLp ∞) f :=
  (rfl)

/-- The truncated square function operator `f ↦ (Δ₀ f, …, Δₙ f)` from `L²(V, F)` to
`L²(V, ℓ²(F))`. -/
private def sqFun (n : ℕ) :
    Lp F 2 (volume : Measure V) →L[ℝ] Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V) :=
  ∑ j ∈ Finset.range (n + 1),
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume ∘L block φ j

/-- The operator `(gⱼ) ↦ ∑_{j ≤ n} Δⱼ gⱼ`, the adjoint of `sqFun φ n`. -/
private def sqFunAdj (n : ℕ) :
    Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  ∑ j ∈ Finset.range (n + 1),
    block φ j ∘L (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume

/-- The block `Δⱼ` is convolution with `𝓕⁻ ψⱼ`. -/
private theorem coeFn_block (j : ℕ) (f : Lp F 2 (volume : Measure V)) :
    block φ j f =ᵐ[volume] fun x ↦ ∫ z, 𝓕⁻ (symbol φ j) (x - z) • f z :=
  (symbol φ j).coeFn_fourierMultiplierCLM_toLp f

private theorem coeFn_sqFun (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    sqFun φ n f =ᵐ[volume] fun x ↦ ∑ j ∈ Finset.range (n + 1), lp.single 2 j (block φ j f x) := by
  have hj := ae_all_iff.2 fun j : ℕ ↦
    ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).coeFn_compLpL (block φ j f))
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n + 1)) fun j ↦
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume (block φ j f), hj]
    with x hx hjx
  rw [sqFun, sum_apply]
  simp only [comp_apply]
  rw [hx]
  exact Finset.sum_congr rfl fun j _ ↦ hjx j

private theorem ae_sqFun_eq_integral (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, sqFun φ n f x = ∫ z, sqKernel φ n x z (f z) := by
  filter_upwards [coeFn_sqFun φ n f, ae_all_iff.2 fun j ↦ coeFn_block φ j f] with x hx hjx
  rw [hx]
  simp only [sqKernel, sum_apply, coe_comp, Function.comp_apply, lsmul_apply,
    lp.singleContinuousLinearMap_apply]
  rw [integral_finsetSum _ fun j _ ↦ ?_]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hjx j]
    exact ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).integral_comp_comm
      ((symbol φ j).integrable_fourierInv_sub_smul f x)).symm
  · exact (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).integrable_comp
      ((symbol φ j).integrable_fourierInv_sub_smul f x)

private theorem ae_sqFunAdj_eq_integral (n : ℕ)
    (g : Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V)) :
    ∀ᵐ x, sqFunAdj φ n g x = ∫ z, sqKernelAdj φ n x z (g z) := by
  set u : ℕ → Lp F 2 (volume : Measure V) := fun j ↦
    (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume g
  have hu : ∀ j, (u j : V → F) =ᵐ[volume] fun z ↦ g z j := fun j ↦
    (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).coeFn_compLpL g
  have hint : ∀ j x, Integrable (fun z ↦ 𝓕⁻ (symbol φ j) (x - z) • g z j) := fun j x ↦
    ((symbol φ j).integrable_fourierInv_sub_smul (u j) x).congr
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
private theorem star_toLp_symbol (j : ℕ) :
    star ((symbol φ j).toLp ∞ (volume : Measure V)) = (symbol φ j).toLp ∞ volume := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star ((symbol φ j).toLp ∞ (volume : Measure V)),
    (symbol φ j).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂
  rw [h₁, Pi.star_apply, h₂, symbol_apply, Complex.star_def, Complex.conj_ofReal]

private theorem inner_block_left (j : ℕ) (f g : Lp F 2 (volume : Measure V)) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    inner ℝ (block φ j f) g = inner ℝ f (block φ j g) := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hM : adjoint (Lp.fourierMultiplierCLM F ((symbol φ j).toLp ∞ (volume : Measure V))) =
      Lp.fourierMultiplierCLM F ((symbol φ j).toLp ∞ volume) := by
    rw [Lp.adjoint_fourierMultiplierCLM, star_toLp_symbol]
  simp only [block, coe_restrictScalars']
  rw [L2.real_inner_eq_re_inner, L2.real_inner_eq_re_inner]
  conv_lhs => rw [← hM]
  rw [adjoint_inner_left]

private theorem adjoint_sqFun (n : ℕ) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    adjoint (sqFun (F := F) φ n) = sqFunAdj φ n := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine ((eq_adjoint_iff _ _).2 fun g f ↦ ?_).symm
  simp only [sqFunAdj, sqFun, sum_apply, comp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_block_left, L2.inner_evalCLM_compLpL]

/-- Coordinate `j ≤ n` of `sqFun φ n f` is `Δⱼ f`. -/
private theorem evalCLM_compLpL_sqFun {n j : ℕ} (hj : j ∈ Finset.range (n + 1))
    (f : Lp F 2 (volume : Measure V)) :
    (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume (sqFun φ n f) = block φ j f := by
  apply Lp.ext
  filter_upwards [(lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).coeFn_compLpL (sqFun φ n f),
    coeFn_sqFun φ n f] with x h₁ h₂
  rw [h₁, h₂, lp.evalCLM_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [hj]

private theorem sqFunAdj_sqFun (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    sqFunAdj φ n (sqFun φ n f) = ∑ j ∈ Finset.range (n + 1), block φ j (block φ j f) := by
  simp only [sqFunAdj, sum_apply, comp_apply]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [evalCLM_compLpL_sqFun φ hj]

/-- The symbol `∑ⱼ ψⱼ²` of `∑ⱼ Δⱼ²` is bounded uniformly in the set of indices. -/
private theorem exists_norm_sum_toLp_symbol_smul_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s : Finset ℕ, ‖∑ j ∈ s,
      ((symbol φ j).toLp ∞ volume • (symbol φ j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V))‖ ≤
        L := by
  obtain ⟨L, hL⟩ := φ.exists_sum_sq_inhomogeneousLittlewoodPaley_le
  refine ⟨L, Nat.cast_nonneg L, fun s ↦ ?_⟩
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg L) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j ↦
      ((symbol φ j).toLp ∞ volume • (symbol φ j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)),
    ae_all_iff.2 fun j ↦ Lp.coeFn_lpSMul (r := ∞) ((symbol φ j).toLp ∞ (volume : Measure V))
      ((symbol φ j).toLp ∞ volume),
    ae_all_iff.2 fun j ↦ (symbol φ j).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂ h₃
  rw [h₁]
  simp only [h₂, Pi.smul_apply', h₃, symbol_apply, smul_eq_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ mul_self_nonneg _)]
  simpa [sq] using hL s ξ

/-- `∑_{j ≤ n} Δⱼ² f` is the multiplier with symbol `∑_{j ≤ n} ψⱼ²` applied to `f`. -/
private theorem sum_block_block (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    ∑ j ∈ Finset.range (n + 1), block φ j (block φ j f) =
      Lp.fourierMultiplierCLM F (∑ j ∈ Finset.range (n + 1),
        ((symbol φ j).toLp ∞ volume • (symbol φ j).toLp ∞ volume :
          Lp ℂ ∞ (volume : Measure V))) f := by
  simp only [Lp.fourierMultiplierCLM_sum, sum_apply, block, coe_restrictScalars',
    Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]

/-- **The `L²` bound**, uniformly in the truncation: `‖(Δ₀ f, …, Δₙ f)‖ ≤ √L ‖f‖`. -/
private theorem exists_norm_sqFun_apply_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (n : ℕ) (f : Lp F 2 (volume : Measure V)), ‖sqFun φ n f‖ ≤ √L * ‖f‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_sum_toLp_symbol_smul_le φ
  refine ⟨L, hL0, fun n f ↦ ?_⟩
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hL0, ← real_inner_self_eq_norm_sq, ← adjoint_inner_right,
    adjoint_sqFun, sqFunAdj_sqFun, sum_block_block]
  calc inner ℝ f (Lp.fourierMultiplierCLM F _ f) ≤ ‖f‖ * ‖Lp.fourierMultiplierCLM F _ f‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖f‖ * (L * ‖f‖) := by
        gcongr
        exact (Lp.norm_fourierMultiplierCLM_apply_le _ f).trans (by gcongr; exact hL _)
    _ = L * ‖f‖ ^ 2 := by ring

/-- **The Calderón–Zygmund bound for the truncated square functions**, uniformly in the
truncation. -/
private theorem exists_eLpNorm_sqFun_le [Nontrivial V] {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ (n : ℕ) (f : Lp F 2 (volume : Measure V)),
      eLpNorm (sqFun φ n f) p volume ≤ C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, -, hB⟩ := exists_setIntegral_norm_kernel_sub_sub_le φ
  obtain ⟨L, -, hL⟩ := exists_norm_sqFun_apply_le (F := F) φ
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_hormander (V := V) (H := F)
    (K := lp (fun _ : ℕ ↦ F) 2) (M := ENNReal.ofReal √L) (B := ENNReal.ofReal B)
    (B' := ENNReal.ofReal B) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hp hp_top
  refine ⟨C, fun n f ↦ hC (sqFun φ n) (sqKernel φ n) (sqKernelAdj φ n) ?_
    (stronglyMeasurable_sqKernel φ n) (stronglyMeasurable_sqKernelAdj φ n)
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel φ n).integrable (norm_sqKernel_sub_le φ n)
      (hB n))
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel φ n).integrable
      (norm_sqKernelAdj_sub_le φ n) (hB n))
    (fun g _ _ _ ↦ (ae_sqFun_eq_integral φ n g).mono fun _ hx _ ↦ hx)
    (fun g _ _ _ ↦ (adjoint_sqFun (F := F) φ n) ▸
      (ae_sqFunAdj_eq_integral φ n g).mono fun _ hx _ ↦ hx)
    f⟩
  rw [← ofReal_norm (sqFun φ n)]
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
    have : m j = (symbol φ j).toLp ∞ volume := Lp.ext <| by
      filter_upwards [hm j, (symbol φ j).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂
      rw [h₁, h₂, symbol_apply]
    rw [this, block_apply]
  simp_rw [hb]
  -- The full square sum is the increasing limit of the partial sums `∑_{j ≤ n}`.
  set G : ℕ → V → ℝ≥0∞ := fun n x ↦
    (∑ j ∈ Finset.range (n + 1), ‖block φ j f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hG : ∀ x, (∑' j, ‖block φ j f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) = ⨆ n, G n x := fun x ↦ by
    rw [← ENNReal.iSup_rpow_of_pos (by norm_num),
      ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)]
  have hmeas : ∀ n, AEMeasurable (G n) := fun n ↦
    (Finset.aemeasurable_fun_sum _ fun j _ ↦
      (Lp.aestronglyMeasurable _).enorm.pow_const 2).pow_const _
  have hmono : ∀ x, Monotone fun n ↦ G n x := fun x a b hab ↦ ENNReal.rpow_le_rpow
    (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))) (by norm_num)
  simp_rw [hG]
  rw [eLpNorm_iSup_eq_iSup_eLpNorm hmeas (.of_forall hmono)]
  refine iSup_le fun n ↦ (eLpNorm_mono_enorm_ae (hmeas n).aestronglyMeasurable ?_).trans (hC n f)
  -- Pointwise, `G n` is the `ℓ²` norm of `(Δ₀ f, …, Δₙ f)`.
  filter_upwards [coeFn_sqFun φ n f] with x hx
  rw [hx, enorm_eq_self, lp.enorm_sum_single]

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

/-! ### The reverse square function inequality -/

namespace TauCeti

open scoped InnerProductSpace Topology

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace LittlewoodPaleySquare

/-- **Cauchy–Schwarz near the diagonal.** Pairing `b` with the sums of `a` over the windows
`j + 1 - L ≤ k < j + L` costs at most the factor `2 L` over the `ℓ²` norms, since each window has
at most `2 L` elements and each index lies in at most `2 L` windows. -/
private theorem sum_mul_sum_Ico_le (L N : ℕ) (a b : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range N, b j * ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), a k ≤
      2 * L * ((∑' j, b j ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, a k ^ 2) ^ (2⁻¹ : ℝ)) := by
  set P := (Finset.range N).sigma fun j ↦ Finset.Ico (j + 1 - L) (j + L)
  have hcard : ∀ j, ((Finset.Ico (j + 1 - L) (j + L)).card : ℝ≥0∞) ≤ 2 * L := fun j ↦ by
    rw [Nat.card_Ico]
    exact_mod_cast (by omega : j + L - (j + 1 - L) ≤ 2 * L)
  have hb : ∑ x ∈ P, b x.1 ^ 2 ≤ 2 * L * ∑' j, b j ^ 2 := by
    rw [Finset.sum_sigma]
    simp_rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ j ∈ Finset.range N, ((Finset.Ico (j + 1 - L) (j + L)).card : ℝ≥0∞) * b j ^ 2
        ≤ ∑ j ∈ Finset.range N, 2 * L * b j ^ 2 := by gcongr with j; exact hcard j
      _ ≤ 2 * L * ∑' j, b j ^ 2 := by rw [← Finset.mul_sum]; gcongr; exact sum_le_tsum _
  -- Exchange the order of summation: the indices `j` whose window contains `k` form a window
  -- around `k`.
  have ha : ∑ x ∈ P, a x.2 ^ 2 ≤ 2 * L * ∑' k, a k ^ 2 := by
    rw [Finset.sum_sigma, Finset.sum_comm' (t' := Finset.range (N + L))
      (s' := fun k ↦ (Finset.range N).filter fun j ↦ k ∈ Finset.Ico (j + 1 - L) (j + L))
      (fun j k ↦ by simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]; omega)]
    simp_rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ k ∈ Finset.range (N + L),
          (((Finset.range N).filter fun j ↦ k ∈ Finset.Ico (j + 1 - L) (j + L)).card : ℝ≥0∞) *
            a k ^ 2
        ≤ ∑ k ∈ Finset.range (N + L), 2 * L * a k ^ 2 := by
          gcongr with k
          refine le_trans ?_ (hcard k)
          exact_mod_cast Finset.card_le_card fun j ↦ by
            simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]; omega
      _ ≤ 2 * L * ∑' k, a k ^ 2 := by rw [← Finset.mul_sum]; gcongr; exact sum_le_tsum _
  have hhalf : ((2 : ℝ≥0∞) * L) ^ (2⁻¹ : ℝ) * ((2 : ℝ≥0∞) * L) ^ (2⁻¹ : ℝ) = 2 * L := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc ∑ j ∈ Finset.range N, b j * ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), a k
      = ∑ x ∈ P, b x.1 * a x.2 := by rw [Finset.sum_sigma]; simp_rw [Finset.mul_sum]
    _ ≤ (∑ x ∈ P, b x.1 ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑ x ∈ P, a x.2 ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.inner_le_Lp_mul_Lq P (fun x ↦ b x.1) (fun x ↦ a x.2) Real.HolderConjugate.two_two
    _ ≤ (2 * L * ∑' j, b j ^ 2) ^ (2⁻¹ : ℝ) * (2 * L * ∑' k, a k ^ 2) ^ (2⁻¹ : ℝ) := by
        simp_rw [ENNReal.rpow_two, one_div]
        gcongr
    _ = 2 * L * ((∑' j, b j ^ 2) ^ (2⁻¹ : ℝ) * (∑' k, a k ^ 2) ^ (2⁻¹ : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg (2 * (L : ℝ≥0∞)) (∑' j, b j ^ 2) (by norm_num),
          ENNReal.mul_rpow_of_nonneg (2 * (L : ℝ≥0∞)) (∑' k, a k ^ 2) (by norm_num),
          mul_mul_mul_comm, hhalf]

variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace F]

/-- **Almost orthogonality of the blocks.** If the pieces `ψⱼ` and `ψₖ` have disjoint supports
whenever `j + L ≤ k`, then pairing `Δⱼ u` with `v` only sees the blocks `Δₖ v` with
`j + 1 - L ≤ k < j + L`. -/
private theorem inner_fourierMultiplierCLM_eq_sum (φ : ContDiffBump (0 : V)) {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    {m : ℕ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
    (j : ℕ) (u v : Lp F 2 (volume : Measure V)) :
    ⟪Lp.fourierMultiplierCLM F (m j) u, v⟫_ℂ = ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
      ⟪Lp.fourierMultiplierCLM F (m j) u, Lp.fourierMultiplierCLM F (m k) v⟫_ℂ := by
  -- The enlarged cutoff `∑_{|k - j| < L} ψₖ` is `1` on the support of `ψⱼ`.
  have hsym : ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), (m k • m j : Lp ℂ ∞ (volume : Measure V)) =
      m j := Lp.ext <| by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.Ico (j + 1 - L) (j + L))
        fun k ↦ (m k • m j : Lp ℂ ∞ (volume : Measure V)),
      ae_all_iff.2 fun k ↦ Lp.coeFn_lpSMul (r := ∞) (m k) (m j), ae_all_iff.2 hm]
      with ξ h₁ h₂ h₃
    have h := φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL j ξ
    rw [φ.enlargedLittlewoodPaley_apply] at h
    simp only [h₁, h₂, h₃, Pi.smul_apply', smul_eq_mul, ← Finset.sum_mul]
    exact_mod_cast h
  -- The blocks are self-adjoint, since their symbols are real.
  have hstar : ∀ k, star (m k) = m k := fun k ↦ Lp.ext <| by
    filter_upwards [Lp.coeFn_star (m k), hm k] with ξ h₁ h₂
    rw [h₁, Pi.star_apply, h₂, Complex.star_def, Complex.conj_ofReal]
  conv_lhs => rw [← hsym, Lp.fourierMultiplierCLM_sum, FunLike.coe_sum, Finset.sum_apply]
  refine (sum_inner _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [← Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, ← adjoint_inner_right,
    Lp.adjoint_fourierMultiplierCLM, hstar]

/-- **The truncated pairing.** Pairing the partial sum `∑_{j < N} Δⱼ u` with `v` is bounded by the
integral of the product of the square functions of `u` and `v`, up to the factor `2 L`. -/
private theorem enorm_sum_inner_fourierMultiplierCLM_le (φ : ContDiffBump (0 : V)) {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    {m : ℕ → Lp ℂ ∞ (volume : Measure V)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
    (N : ℕ) (u v : Lp F 2 (volume : Measure V)) :
    ‖∑ j ∈ Finset.range N, ⟪Lp.fourierMultiplierCLM F (m j) u, v⟫_ℂ‖ₑ ≤
      2 * L * ∫⁻ x, (∑' j, ‖Lp.fourierMultiplierCLM F (m j) u x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
        (∑' k, ‖Lp.fourierMultiplierCLM F (m k) v x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
  set Δ := fun j ↦ Lp.fourierMultiplierCLM (E := V) F (m j)
  have hmeas : ∀ j k, AEMeasurable (fun x ↦ ‖Δ j u x‖ₑ * ‖Δ k v x‖ₑ) volume := fun j k ↦
    (Lp.aestronglyMeasurable _).enorm.mul (Lp.aestronglyMeasurable _).enorm
  calc ‖∑ j ∈ Finset.range N, ⟪Δ j u, v⟫_ℂ‖ₑ
      = ‖∑ j ∈ Finset.range N, ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          ∫ x, ⟪Δ j u x, Δ k v x⟫_ℂ‖ₑ := by
        simp_rw [Δ, inner_fourierMultiplierCLM_eq_sum φ hL hm _ u v, L2.inner_def]
    _ ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          ∫⁻ x, ‖Δ j u x‖ₑ * ‖Δ k v x‖ₑ := by
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
          (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_))
        exact (enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono fun x ↦ enorm_inner_le_enorm _ _)
    _ = ∫⁻ x, ∑ j ∈ Finset.range N,
          ‖Δ j u x‖ₑ * ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), ‖Δ k v x‖ₑ := by
        simp_rw [Finset.mul_sum]
        rw [lintegral_finsetSum' _ fun j _ ↦ Finset.aemeasurable_fun_sum _ fun k _ ↦ hmeas j k]
        exact Finset.sum_congr rfl fun j _ ↦ (lintegral_finsetSum' _ fun k _ ↦ hmeas j k).symm
    _ ≤ 2 * L * ∫⁻ x, (∑' j, ‖Δ j u x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖Δ k v x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
        rw [← lintegral_const_mul' _ _ (by finiteness)]
        exact lintegral_mono fun x ↦
          sum_mul_sum_Ico_le L N (fun k ↦ ‖Δ k v x‖ₑ) (fun j ↦ ‖Δ j u x‖ₑ)

end LittlewoodPaleySquare

open LittlewoodPaleySquare in
/-- **The reverse Littlewood–Paley square function inequality.** Let `V` be a real inner product
space of finite dimension `n ≥ 1`, let `φ` be a smooth bump function on `V`, and let
`1 < p < ∞`. Let `Δⱼ` be the `L²` Fourier multipliers with the pieces `ψⱼ` of the inhomogeneous
Littlewood–Paley partition as symbols. For every complex Hilbert space `F` there is a constant `C`
such that for every `f ∈ L²(V, F)`,

`‖f‖_p ≤ C ‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p`.

Neither side is assumed finite. Together with
`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le` this is the Littlewood–Paley
theorem `‖f‖_p ≈ ‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p`. Each symbol enters as any element of `L^∞` almost
everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_le_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow [Nontrivial V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℕ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f p volume ≤ C *
          eLpNorm (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
            volume := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero
  have : p.HolderConjugate p.conjExponent := .conjExponent hp.le
  obtain ⟨C, hC⟩ := exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le (F := F) φ
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).1 hp_top.lt_top)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt _ p).2 hp).ne
  refine ⟨2 * L * C, fun m hm f ↦ ?_⟩
  set S : Lp F 2 (volume : Measure V) → V → ℝ≥0∞ :=
    fun u x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) u x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hSm : ∀ u, AEMeasurable (S u) volume := fun u ↦
    (AEMeasurable.tsum fun j ↦ (Lp.aestronglyMeasurable _).enorm.pow_const 2).pow_const _
  -- Test `f` against bounded functions `g` vanishing off a set of finite measure; these lie in
  -- `L²`, where the pairing is the `L²` inner product.
  refine (Lp.aestronglyMeasurable f).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ)
    (q' := p.conjExponent) hp_top fun g s hs hgs hg ↦ ?_
  have hg2 : MemLp g 2 volume := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  set G := hg2.toLp g
  have hint : ∫ x, ⟪f x, g x⟫_ℂ = ⟪f, G⟫_ℂ := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hg2.coeFn_toLp] with x hx; rw [hx])
  rw [hint, ← eLpNorm_congr_ae hg2.coeFn_toLp]
  -- By the reconstruction `f = ∑ⱼ Δⱼ f`, the pairing is the limit of `∑_{j < N} ⟪Δⱼ f, G⟫`.
  have hlim : Tendsto (fun N ↦ ‖∑ j ∈ Finset.range N, ⟪Lp.fourierMultiplierCLM F (m j) f, G⟫_ℂ‖ₑ)
      atTop (𝓝 ‖⟪f, G⟫_ℂ‖ₑ) := by
    have h := ((continuous_enorm.comp (continuous_id.inner (𝕜 := ℂ)
      (continuous_const (y := G)))).tendsto f).comp
        (Lp.tendsto_sum_fourierMultiplierCLM_inhomogeneousLittlewoodPaley φ hm f)
    simpa only [Function.comp_def, sum_inner, id] using h
  -- Hölder's inequality for the two square functions, then the square function inequality in
  -- `L^{p'}` for `G`.
  have hH : ∫⁻ x, S f x * S G x ≤ eLpNorm (S f) p volume * eLpNorm (S G) p.conjExponent volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (μ := volume) (p := p)
      (q := p.conjExponent) (r := 1) (fun a b : ℝ≥0∞ ↦ a * b) 1
      (fun ha hb ↦ (ha.aemeasurable.mul hb.aemeasurable).aestronglyMeasurable)
      (hSm f).aestronglyMeasurable (hSm G).aestronglyMeasurable (ae_of_all _ fun x ↦ by simp)
    rw [one_mul, eLpNorm_one_eq_lintegral_enorm (f := fun x ↦ S f x * S G x)
      ((hSm f).mul (hSm G)).aestronglyMeasurable] at h
    simpa only [enorm_eq_self] using h
  refine le_of_tendsto' hlim fun N ↦ ?_
  calc _ ≤ 2 * L * ∫⁻ x, S f x * S G x := enorm_sum_inner_fourierMultiplierCLM_le φ hL hm N f G
    _ ≤ 2 * L * (eLpNorm (S f) p volume * (C * eLpNorm G p.conjExponent volume)) := by
        grw [hH, hC m hm G]
    _ = ↑(2 * L * C : ℝ≥0) * eLpNorm (S f) p volume * eLpNorm G p.conjExponent volume := by
        push_cast
        ring

end TauCeti
