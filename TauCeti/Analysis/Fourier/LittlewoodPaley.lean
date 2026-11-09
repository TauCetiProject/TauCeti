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
and `1 < p < ∞` there is a constant `C`, depending on `φ`, `p` and `F`, with

`‖S f‖_p ≤ C ‖f‖_p` and `‖f‖_p ≤ C ‖S f‖_p`

for every `f ∈ L²(V, F)` (`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le` and
`TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow`).

## The upper bound

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

## The lower bound

The lower bound follows from the upper one at the conjugate exponent `p'` by duality. Pieces whose
indices differ by at least some `L` have disjoint supports, so the enlarged cutoff
`Ψⱼ = ∑_{j + 1 - L ≤ k < j + L} ψₖ` equals `1` on the support of `ψⱼ`
(`ContDiffBump.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley`), and its multiplier
`Δ'ⱼ = ∑_{j + 1 - L ≤ k < j + L} Δₖ` satisfies `Δ'ⱼ Δⱼ = Δⱼ`. For a test function `g`,

`⟪∑_{j ≤ n} Δⱼ f, g⟫ = ∑_{j ≤ n} ⟪Δⱼ f, Δ'ⱼ g⟫ = ∫ ⟪(Δⱼ f (x))ⱼ, (Δ'ⱼ g (x))ⱼ⟫_{ℓ²} dx`,

which Hölder's inequality bounds by `‖S f‖_p ‖(∑ⱼ ‖Δ'ⱼ g‖²)^{1/2}‖_{p'}`. Each `Δ'ⱼ g` is a sum of
at most `2 L` blocks of `g`, and each block enters at most `2 L` of them, so
`(∑ⱼ ‖Δ'ⱼ g‖²)^{1/2} ≤ 2 L S g` pointwise, and `‖S g‖_{p'} ≤ C ‖g‖_{p'}`. Letting `n → ∞`, the
partial sums `∑_{j ≤ n} Δⱼ f`, the multipliers with symbols `φ (2^{-n} ·)`, converge to `f` in
`L²`, and testing against all `g` gives `‖f‖_p ≤ 2 L C ‖S f‖_p`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Theorem 6.1.2 and Section 5.6
  (vector-valued inequalities).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  Section 1.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap ContDiff LineDeriv Topology
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

/-- The kernel `v ↦ ((𝓕⁻ ψⱼ) (x - y) v)ⱼ` of `vecOp (block φ) n`. -/
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

/-- A multiplier whose symbol agrees almost everywhere with `ψⱼ` is the block `Δⱼ`. -/
private theorem fourierMultiplierCLM_eq_block {m : Lp ℂ ∞ (volume : Measure V)} {j : ℕ}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
    (f : Lp F 2 (volume : Measure V)) :
    Lp.fourierMultiplierCLM F m f = block φ j f := by
  have : m = (symbol φ j).toLp ∞ volume := Lp.ext <| by
    filter_upwards [hm, (symbol φ j).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂
    rw [h₁, h₂, symbol_apply]
  rw [this, block_apply]

/-- The operator `f ↦ (T₀ f, …, Tₙ f)` from `L²(V, F)` to `L²(V, ℓ²(F))` built from operators
`Tⱼ` on `L²(V, F)`. For the blocks `Tⱼ = Δⱼ` it is the truncated square function operator. -/
private def vecOp (T : ℕ → Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    (n : ℕ) :
    Lp F 2 (volume : Measure V) →L[ℝ] Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V) :=
  ∑ j ∈ Finset.range (n + 1),
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume ∘L T j

/-- The operator `(gⱼ) ↦ ∑_{j ≤ n} Δⱼ gⱼ`, the adjoint of `vecOp (block φ) n`. -/
private def sqFunAdj (n : ℕ) :
    Lp (lp (fun _ : ℕ ↦ F) 2) 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  ∑ j ∈ Finset.range (n + 1),
    block φ j ∘L (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume

/-- The block `Δⱼ` is convolution with `𝓕⁻ ψⱼ`. -/
private theorem coeFn_block (j : ℕ) (f : Lp F 2 (volume : Measure V)) :
    block φ j f =ᵐ[volume] fun x ↦ ∫ z, 𝓕⁻ (symbol φ j) (x - z) • f z :=
  (symbol φ j).coeFn_fourierMultiplierCLM_toLp f

omit [CompleteSpace F] in
private theorem coeFn_vecOp
    (T : ℕ → Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) (n : ℕ)
    (f : Lp F 2 (volume : Measure V)) :
    vecOp T n f =ᵐ[volume] fun x ↦ ∑ j ∈ Finset.range (n + 1), lp.single 2 j (T j f x) := by
  have hj := ae_all_iff.2 fun j : ℕ ↦
    ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).coeFn_compLpL (T j f))
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n + 1)) fun j ↦
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume (T j f), hj]
    with x hx hjx
  rw [vecOp, sum_apply]
  simp only [comp_apply]
  rw [hx]
  exact Finset.sum_congr rfl fun j _ ↦ hjx j

private theorem ae_sqFun_eq_integral (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, vecOp (block φ) n f x = ∫ z, sqKernel φ n x z (f z) := by
  filter_upwards [coeFn_vecOp (block φ) n f, ae_all_iff.2 fun j ↦ coeFn_block φ j f] with x hx hjx
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

private theorem adjoint_vecOp_block (n : ℕ) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    adjoint (vecOp (block (F := F) φ) n) = sqFunAdj φ n := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine ((eq_adjoint_iff _ _).2 fun g f ↦ ?_).symm
  simp only [sqFunAdj, vecOp, sum_apply, comp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_block_left, L2.inner_evalCLM_compLpL]

omit [CompleteSpace F] in
/-- Coordinate `j ≤ n` of `vecOp T n f` is `Tⱼ f`. -/
private theorem evalCLM_compLpL_vecOp
    (T : ℕ → Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) {n j : ℕ}
    (hj : j ∈ Finset.range (n + 1)) (f : Lp F 2 (volume : Measure V)) :
    (lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume (vecOp T n f) = T j f := by
  apply Lp.ext
  filter_upwards [(lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).coeFn_compLpL (vecOp T n f),
    coeFn_vecOp T n f] with x h₁ h₂
  rw [h₁, h₂, lp.evalCLM_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [hj]

private theorem sqFunAdj_vecOp_block (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    sqFunAdj φ n (vecOp (block φ) n f) = ∑ j ∈ Finset.range (n + 1), block φ j (block φ j f) := by
  simp only [sqFunAdj, sum_apply, comp_apply]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [evalCLM_compLpL_vecOp (block φ) hj]

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
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (n : ℕ) (f : Lp F 2 (volume : Measure V)), ‖vecOp (block φ) n f‖ ≤ √L * ‖f‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_sum_toLp_symbol_smul_le φ
  refine ⟨L, hL0, fun n f ↦ ?_⟩
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hL0, ← real_inner_self_eq_norm_sq, ← adjoint_inner_right,
    adjoint_vecOp_block, sqFunAdj_vecOp_block, sum_block_block]
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
      eLpNorm (vecOp (block φ) n f) p volume ≤ C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, -, hB⟩ := exists_setIntegral_norm_kernel_sub_sub_le φ
  obtain ⟨L, -, hL⟩ := exists_norm_sqFun_apply_le (F := F) φ
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_hormander (V := V) (H := F)
    (K := lp (fun _ : ℕ ↦ F) 2) (M := ENNReal.ofReal √L) (B := ENNReal.ofReal B)
    (B' := ENNReal.ofReal B) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hp hp_top
  refine ⟨C, fun n f ↦ hC (vecOp (block φ) n) (sqKernel φ n) (sqKernelAdj φ n) ?_
    (stronglyMeasurable_sqKernel φ n) (stronglyMeasurable_sqKernelAdj φ n)
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel φ n).integrable (norm_sqKernel_sub_le φ n)
      (hB n))
    (setLIntegral_enorm_sub_le_of_norm_sub_le (kernel φ n).integrable
      (norm_sqKernelAdj_sub_le φ n) (hB n))
    (fun g _ _ _ ↦ (ae_sqFun_eq_integral φ n g).mono fun _ hx _ ↦ hx)
    (fun g _ _ _ ↦ (adjoint_vecOp_block (F := F) φ n) ▸
      (ae_sqFunAdj_eq_integral φ n g).mono fun _ hx _ ↦ hx)
    f⟩
  rw [← ofReal_norm (vecOp (block φ) n)]
  exact ENNReal.ofReal_le_ofReal (opNorm_le_bound _ (Real.sqrt_nonneg _) (hL n))

/-! ### The reverse inequality -/

/-- The partial sums `∑_{j ≤ n} Δⱼ f` converge to `f` in `L²`. -/
private theorem tendsto_sum_block (f : Lp F 2 (volume : Measure V)) :
    Tendsto (fun n ↦ ∑ j ∈ Finset.range (n + 1), block φ j f) atTop (𝓝 f) := by
  -- The partial sum is the multiplier with symbol `∑_{j ≤ n} ψⱼ = φ (2^{-n} ·)`, which lies in
  -- `[0, 1]` and tends to `1` pointwise.
  set one : Lp ℂ ∞ (volume : Measure V) := (memLp_top_const (1 : ℂ)).toLp _
  have hone : Lp.fourierMultiplierCLM F one f = f := by
    rw [Lp.fourierMultiplierCLM_of_ae_eq_const (memLp_top_const (1 : ℂ)).coeFn_toLp, one_smul,
      id_apply]
  have hsym : ∀ n, ∀ᵐ ξ ∂(volume : Measure V),
      (∑ j ∈ Finset.range (n + 1), (symbol φ j).toLp ∞ (volume : Measure V)) ξ =
        (φ (((2 : ℝ) ^ n)⁻¹ • ξ) : ℂ) := fun n ↦ by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n + 1)) fun j ↦
        (symbol φ j).toLp ∞ (volume : Measure V),
      ae_all_iff.2 fun j ↦ (symbol φ j).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂
    simp only [h₁, h₂, symbol_apply, ← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range]
  have h := Lp.tendsto_fourierMultiplierCLM_apply (F := F) (m₀ := one) (l := atTop) (C := 1)
    (m := fun n ↦ ∑ j ∈ Finset.range (n + 1), (symbol φ j).toLp ∞ (volume : Measure V))
    (Eventually.of_forall fun n ↦ ?_) ?_ f
  · simpa only [hone, Lp.fourierMultiplierCLM_sum, sum_apply, ← block_apply] using h
  · rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one (eLpNormEssSup_le_of_ae_bound ?_)
    filter_upwards [hsym n] with ξ hξ
    rw [hξ, Complex.norm_real, Real.norm_of_nonneg φ.nonneg]
    exact φ.le_one
  · filter_upwards [ae_all_iff.2 hsym, (memLp_top_const (1 : ℂ)).coeFn_toLp] with ξ hξ h₁
    simp only [hξ, one, h₁, ← φ.sum_inhomogeneousLittlewoodPaley_range]
    exact (Complex.continuous_ofReal.tendsto 1).comp
      (((φ.hasSum_inhomogeneousLittlewoodPaley ξ).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))

/-- The enlarged block `Δ'ⱼ = ∑_{j + 1 - L ≤ k < j + L} Δₖ`, the multiplier whose symbol is the
enlarged cutoff `Ψⱼ` (`ContDiffBump.enlargedLittlewoodPaley`). -/
private def enlargedBlock (L j : ℕ) :
    Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), block φ k

/-- If the pieces whose indices differ by at least `L` have disjoint supports, then
`Δ'ⱼ Δⱼ = Δⱼ`. -/
private theorem enlargedBlock_block {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (j : ℕ) (f : Lp F 2 (volume : Measure V)) :
    enlargedBlock φ L j (block φ j f) = block φ j f := by
  have hsym : ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
      ((symbol φ k).toLp ∞ volume • (symbol φ j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)) =
      (symbol φ j).toLp ∞ volume := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.Ico (j + 1 - L) (j + L)) fun k ↦
        ((symbol φ k).toLp ∞ volume • (symbol φ j).toLp ∞ volume : Lp ℂ ∞ (volume : Measure V)),
      ae_all_iff.2 fun k ↦ Lp.coeFn_lpSMul (r := ∞) ((symbol φ k).toLp ∞ (volume : Measure V))
        ((symbol φ j).toLp ∞ volume),
      ae_all_iff.2 fun k ↦ (symbol φ k).coeFn_toLp ∞ (volume : Measure V)] with ξ h₁ h₂ h₃
    simp only [h₁, h₂, Pi.smul_apply', h₃, symbol_apply, smul_eq_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, ← Finset.sum_mul, ← φ.enlargedLittlewoodPaley_apply,
      φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]
  simp only [enlargedBlock, sum_apply, block, coe_restrictScalars',
    Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  rw [← sum_apply, ← Lp.fourierMultiplierCLM_sum, hsym]

/-- The enlarged blocks are self-adjoint. -/
private theorem inner_enlargedBlock_left (L j : ℕ) (f g : Lp F 2 (volume : Measure V)) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    inner ℝ (enlargedBlock φ L j f) g = inner ℝ f (enlargedBlock φ L j g) := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  simp only [enlargedBlock, sum_apply, sum_inner, inner_sum, inner_block_left]

/-- **The pairing identity.** Pairing the partial sum `∑_{j ≤ n} Δⱼ f` with `g` is pairing the
vectors `(Δ₀ f, …, Δₙ f)` and `(Δ'₀ g, …, Δ'ₙ g)`, since `Δⱼ = Δ'ⱼ Δⱼ` and `Δ'ⱼ` is
self-adjoint. -/
private theorem inner_sum_block_eq {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : V,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (n : ℕ) (f g : Lp F 2 (volume : Measure V)) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    inner ℝ (∑ j ∈ Finset.range (n + 1), block φ j f) g =
      inner ℝ (vecOp (block φ) n f) (vecOp (enlargedBlock φ L) n g) := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [sum_inner]
  conv_rhs => rw [vecOp, sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [comp_apply]
  calc inner ℝ (block φ j f) g = inner ℝ (block φ j f) (enlargedBlock φ L j g) := by
        rw [← inner_enlargedBlock_left, enlargedBlock_block φ hL]
    _ = inner ℝ ((lp.evalCLM ℝ (fun _ : ℕ ↦ F) 2 j).compLpL 2 volume
          (vecOp (enlargedBlock φ L) n g)) (block φ j f) := by
        rw [evalCLM_compLpL_vecOp _ hj, real_inner_comm]
    _ = _ := by rw [L2.inner_evalCLM_compLpL, real_inner_comm]

/-- Pointwise, `‖(Δ₀ f, …, Δₙ f)‖` is at most the square function `(∑ⱼ ‖Δⱼ f‖²)^{1/2}`. -/
private theorem ae_enorm_vecOp_block_le (n : ℕ) (f : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, ‖vecOp (block φ) n f x‖ₑ ≤ (∑' j, ‖block φ j f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
  filter_upwards [coeFn_vecOp (block φ) n f] with x hx
  rw [hx, lp.enorm_sum_single]
  gcongr
  exact sum_le_tsum _

omit [CompleteSpace F] in
/-- **Bounded overlap of the windows.** Each window `[j + 1 - L, j + L)` has at most `2 L`
indices, and each index lies in at most `2 L` windows, so
`∑_{j ≤ n} (∑_{j + 1 - L ≤ k < j + L} cₖ)² ≤ (2 L)² ∑ₖ cₖ²`. -/
private theorem sum_sq_sum_Ico_le (L n : ℕ) (c : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range (n + 1), (∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c k) ^ 2 ≤
      (2 * L) ^ 2 * ∑' k, c k ^ 2 := by
  have hcard : ∀ k, ((Finset.Ico (k + 1 - L) (k + L)).card : ℝ≥0∞) ≤ 2 * L := fun k ↦ by
    rw [Nat.card_Ico]
    exact_mod_cast (by omega : k + L - (k + 1 - L) ≤ 2 * L)
  calc ∑ j ∈ Finset.range (n + 1), (∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c k) ^ 2
      ≤ ∑ j ∈ Finset.range (n + 1), 2 * L * ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c k ^ 2 := by
        gcongr with j
        have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.Ico (j + 1 - L) (j + L))
          (f := c) one_le_two
        norm_num only [ENNReal.rpow_two, ENNReal.rpow_one] at h
        exact h.trans (by gcongr; exact hcard j)
    _ = 2 * L * ∑ k ∈ Finset.range (n + L),
          ∑ j ∈ (Finset.range (n + 1)).filter (fun j ↦ k ∈ Finset.Ico (j + 1 - L) (j + L)),
            c k ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        refine Finset.sum_comm' fun j k ↦ ?_
        simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]
        omega
    _ ≤ 2 * L * ∑ k ∈ Finset.range (n + L), 2 * L * c k ^ 2 := by
        gcongr with k
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        refine le_trans ?_ (hcard k)
        gcongr
        intro j
        simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]
        omega
    _ ≤ (2 * L) ^ 2 * ∑' k, c k ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc, ← sq]
        gcongr
        exact sum_le_tsum _

/-- Pointwise, `‖(Δ'₀ g, …, Δ'ₙ g)‖ ≤ 2 L (∑ₖ ‖Δₖ g‖²)^{1/2}`. -/
private theorem ae_enorm_vecOp_enlargedBlock_le (L n : ℕ) (g : Lp F 2 (volume : Measure V)) :
    ∀ᵐ x, ‖vecOp (enlargedBlock φ L) n g x‖ₑ ≤
      ((2 * L : ℝ≥0) : ℝ≥0∞) * ‖(∑' k, ‖block φ k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)‖ₑ := by
  have hj : ∀ j, ∀ᵐ x ∂(volume : Measure V),
      enlargedBlock φ L j g x = ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), block φ k g x := fun j ↦ by
    rw [enlargedBlock, sum_apply]
    exact Lp.coeFn_fun_finsetSum _ _
  filter_upwards [coeFn_vecOp (enlargedBlock φ L) n g, ae_all_iff.2 hj] with x hx hjx
  rw [hx, lp.enorm_sum_single, enorm_eq_self]
  simp_rw [hjx]
  calc (∑ j ∈ Finset.range (n + 1),
        ‖∑ k ∈ Finset.Ico (j + 1 - L) (j + L), block φ k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
      ≤ (∑ j ∈ Finset.range (n + 1),
          (∑ k ∈ Finset.Ico (j + 1 - L) (j + L), ‖block φ k g x‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
        gcongr
        exact enorm_sum_le _ _
    _ ≤ ((2 * L) ^ 2 * ∑' k, ‖block φ k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
        gcongr
        exact sum_sq_sum_Ico_le L n _
    _ = ((2 * L : ℝ≥0) : ℝ≥0∞) * (∑' k, ‖block φ k g x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

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
  simp_rw [fourierMultiplierCLM_eq_block φ (hm _)]
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
  filter_upwards [coeFn_vecOp (block φ) n f] with x hx
  rw [hx, enorm_eq_self, lp.enorm_sum_single]

open LittlewoodPaleySquare in
/-- **The reverse Littlewood–Paley inequality.** Let `V` be a real inner product space of finite
dimension `n ≥ 1`, let `φ` be a smooth bump function on `V`, and let `1 < p < ∞`. Let `Δⱼ` be the
`L²` Fourier multipliers with the pieces `ψ₀ = φ`, `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` of the
inhomogeneous Littlewood–Paley partition as symbols. For every complex Hilbert space `F` there is
a constant `C` such that for every `f ∈ L²(V, F)`,

`‖f‖_p ≤ C ‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p`.

Together with `TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le` this is the
Littlewood–Paley theorem `‖f‖_p ≈ ‖(∑ⱼ ‖Δⱼ f‖²)^{1/2}‖_p`. Each symbol enters as any element of
`L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow [Nontrivial V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] (φ : ContDiffBump (0 : V))
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ m : ℕ → Lp ℂ (∞ : ℝ≥0∞) (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f p volume ≤ C * eLpNorm
          (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM F (m j) f x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  -- The conjugate exponent `p' = P / (P - 1)` lies in `(1, ∞)`.
  set P := p.toReal
  have hP : 1 < P := by simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  set p' := ENNReal.ofReal (P / (P - 1))
  have hp'1 : 1 < p' := ENNReal.one_lt_ofReal.2 (by rw [lt_div_iff₀ (by linarith)]; linarith)
  have : p.HolderConjugate p' := by
    refine ENNReal.HolderConjugate.of_toReal ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact Real.HolderConjugate.conjExponent hP
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero (E := V)
  -- The square function inequality at the conjugate exponent.
  obtain ⟨C, hC⟩ := exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le (F := F) φ hp'1
    ENNReal.ofReal_ne_top
  refine ⟨2 * L * C, fun m hm f ↦ ?_⟩
  simp_rw [fourierMultiplierCLM_eq_block φ (hm _)]
  set S : (Lp F 2 (volume : Measure V)) → V → ℝ≥0∞ :=
    fun u x ↦ (∑' j, ‖block φ j u x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hS : ∀ u, eLpNorm (S u) p' volume ≤ C * eLpNorm u p' volume := fun u ↦ by
    simpa only [S, fourierMultiplierCLM_eq_block φ ((symbol φ _).coeFn_toLp ∞ (volume : Measure V)
      |>.trans (.of_forall fun ξ ↦ symbol_apply φ _ ξ))] using
      hC (fun j ↦ (symbol φ j).toLp ∞ volume)
        (fun j ↦ (symbol φ j).coeFn_toLp ∞ (volume : Measure V)
          |>.trans (.of_forall fun ξ ↦ symbol_apply φ j ξ)) u
  -- By duality, it suffices to bound the pairings of `f` with bounded test functions `g` of
  -- finite-measure support.
  refine AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℝ) (q' := p')
    hp_top (Lp.aestronglyMeasurable f) fun g s hs hgs hg ↦ ?_
  have hg2 : MemLp g 2 volume := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  set G := hg2.toLp g
  have hGg : (G : V → F) =ᵐ[volume] g := hg2.coeFn_toLp
  have hpair : ∫ x, inner ℝ (f x) (g x) = inner ℝ f G := by
    rw [L2.inner_def]
    exact integral_congr_ae (hGg.mono fun x hx ↦ by simp only [hx])
  rw [hpair]
  -- Each partial sum `∑_{j ≤ n} Δⱼ f` satisfies the bound, by the pairing identity, Hölder's
  -- inequality and the square function inequality at the conjugate exponent; then let `n → ∞`.
  have hbound : ∀ n, ‖inner ℝ (∑ j ∈ Finset.range (n + 1), block φ j f) G‖ₑ ≤
      (2 * L * C : ℝ≥0) * eLpNorm (S f) p volume * eLpNorm g p' volume := fun n ↦ by
    rw [inner_sum_block_eq φ hL, L2.inner_def]
    calc _ ≤ eLpNorm (vecOp (block φ) n f) p volume *
          eLpNorm (vecOp (enlargedBlock φ L) n G) p' volume := enorm_integral_inner_le
      _ ≤ eLpNorm (S f) p volume * ((2 * L : ℝ≥0) * eLpNorm (S G) p' volume) := by
          gcongr
          · exact eLpNorm_mono_enorm_ae (Lp.aestronglyMeasurable _)
              ((ae_enorm_vecOp_block_le φ n f).mono fun x hx ↦
              hx.trans_eq (enorm_eq_self _).symm)
          · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (Lp.aestronglyMeasurable _)
              (ae_enorm_vecOp_enlargedBlock_le φ L n G) p'
      _ ≤ eLpNorm (S f) p volume * ((2 * L : ℝ≥0) * (C * eLpNorm G p' volume)) := by
          gcongr
          exact hS G
      _ = (2 * L * C : ℝ≥0) * eLpNorm (S f) p volume * eLpNorm g p' volume := by
          rw [eLpNorm_congr_ae hGg]
          push_cast
          ring
  exact le_of_tendsto' ((tendsto_sum_block φ f).inner tendsto_const_nhds).enorm hbound

end TauCeti
