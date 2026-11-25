/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Kernels of dyadic pieces of symbols

A smooth function `g` with the symbol estimates `‖D^i g ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` of
order `m`, such as the Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (m / 2)`, behaves like the constant `R ^ m` on
frequencies with `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`. This file makes that precise at the level of convolution
kernels.

* `TauCeti.exists_integral_norm_fourierInv_cutoff_smul_le`: let `χ` be a smooth cutoff supported
  where `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`, with `‖D^k χ‖ ≤ B_k R ^ (-k)`, and let `g` satisfy the symbol
  estimates of order `m` with constant `W`. Then the kernel of the dyadic piece `χ g` has `L¹` norm
  at most `C W R ^ m`, with `C` independent of `g`, `W`, `R` and `χ`. By
  `TauCeti.exists_norm_iteratedFDeriv_cutoff_smul_le` the product is a band-limited symbol at
  scale `R` with constant `O(W R ^ m)`, and the scale-invariant `L¹` bound
  `SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset` applies.
* `TauCeti.exists_integral_norm_fourierInv_cutoff_smul_le_of_finiteDimensional`: the same bound,
  with the same uniformity, for `g` valued in a finite-dimensional complex normed space, such as a
  space of operators between finite-dimensional spaces. It follows from the previous bound by
  expanding `g` in a basis.

These kernel bounds are what make a Fourier multiplier by a symbol of order `m` act on the
Littlewood–Paley blocks `Δⱼ` like multiplication by `2^{jm}`, uniformly in `1 ≤ p ≤ ∞`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Lemma 6.2.1.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.2.
-/

public section

open scoped FourierTransform SchwartzMap LineDeriv ContDiff
open FourierTransform MeasureTheory Metric Module

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace TauCeti

/-- **Kernels of dyadic pieces of symbols.** Let `2N > n = dim E`, `m` real, `a > 0`, `b` and
`B : ℕ → ℝ`. There is a constant `C` with the following property. Let `g` be a smooth function,
valued in a complex inner product space, with the symbol estimates
`‖D^i g ξ‖ ≤ W (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` of order `m` for `i ≤ N`. Let `R > 0` and let `χ` be a
smooth real function such that `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ` and
`‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`. Then the kernel of the dyadic piece `χ g` satisfies

`∫ ‖𝓕⁻ (χ g) x‖ dx ≤ C W R ^ m`.

The constant `C` depends neither on `g` nor on `W`. -/
theorem exists_integral_norm_fourierInv_cutoff_smul_le (m : ℝ) {N : ℕ}
    (hN : finrank ℝ E < 2 * N) {a b : ℝ} (ha : 0 < a) (B : ℕ → ℝ) :
    ∃ C, ∀ (g : E → H) (W : ℝ), ContDiff ℝ ∞ g →
      (∀ i ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ W * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)) →
      ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) →
      ∫ x, ‖𝓕⁻ (fun ξ ↦ χ ξ • g ξ) x‖ ≤ C * W * R ^ m := by
  set e := stdOrthonormalBasis ℝ E
  obtain ⟨C₀, -, hC₀⟩ :=
    SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset (H := H) e hN
  obtain ⟨K, hK, hKχ⟩ :=
    exists_norm_iteratedFDeriv_cutoff_smul_le (E := E) (G := H) N m (b := b) ha B
  -- The dyadic piece is a band-limited Schwartz function at the scale `t = (√b + 1) R`, with
  -- constant `A = K W (√b + 1) ^ N R ^ m`.
  refine ⟨C₀ * (K * (√b + 1) ^ N), fun g W hg hgm R χ hR hχ hsupp hB ↦ ?_⟩
  have hKχ := hKχ g W (hg.of_le (mod_cast le_top)) hgm R χ hR (hχ.of_le (mod_cast le_top)) hsupp
    hB
  have hW : 0 ≤ W := nonneg_of_forall_norm_le_mul_one_add_norm_sq_rpow (hgm 0 (Nat.zero_le _))
  -- On the support of `χ`, the frequencies are at most `√b R`.
  set t : ℝ := (√b + 1) * R
  have ht : 0 < t := by positivity
  have hball : tsupport χ ⊆ closedBall 0 t :=
    (subset_closedBall_of_one_add_norm_sq_le hR.le fun ξ hξ ↦ (hsupp ξ hξ).2).trans
      (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (by linarith) hR.le))
  have hcs : HasCompactSupport χ :=
    (isCompact_closedBall (0 : E) t).of_isClosed_subset (isClosed_tsupport χ) hball
  set σ : 𝓢(E, H) := (hcs.smul_right (f' := g)).toSchwartzMap (hχ.smul hg)
  have hσ : ⇑σ = fun ξ ↦ χ ξ • g ξ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hσt : Function.support σ ⊆ closedBall 0 t := fun ξ hξ ↦ by
    refine hball (subset_tsupport _ ?_)
    rw [Function.mem_support] at hξ ⊢
    rintro hχξ
    simp [hσ, hχξ] at hξ
  have hσA (ξ : E) : ‖σ ξ‖ ≤ K * W * (√b + 1) ^ N * R ^ m := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), hσ]
    refine (hKχ 0 (Nat.zero_le _) ξ).trans ?_
    have h1 : (1 : ℝ) ≤ (√b + 1) ^ N := one_le_pow₀ (le_add_of_nonneg_left (Real.sqrt_nonneg b))
    calc K * W * R ^ m / R ^ 0 = K * W * 1 * R ^ m := by ring
      _ ≤ K * W * (√b + 1) ^ N * R ^ m := by gcongr
  have hσN (j : Fin (finrank ℝ E)) (ξ : E) :
      ‖(∂_{e j})^[N] σ ξ‖ ≤ K * W * (√b + 1) ^ N * R ^ m / t ^ N := by
    rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ N σ ξ).le_opNorm _).trans ?_
    simp only [e.orthonormal.1 j, Finset.prod_const_one, mul_one]
    rw [hσ]
    refine (hKχ N le_rfl ξ).trans_eq ?_
    simp only [t, mul_pow]
    field_simp
  have hint := hC₀ σ ht hσt hσA hσN
  rw [SchwartzMap.fourierInv_coe, hσ] at hint
  exact hint.trans_eq (by ring)

/-- **Kernels of dyadic pieces of symbols with finite-dimensional values.** The bound of
`TauCeti.exists_integral_norm_fourierInv_cutoff_smul_le` for a symbol `g` with values in a
finite-dimensional complex normed space `G`, such as a space of operators between
finite-dimensional spaces: there is a constant `C` with `∫ ‖𝓕⁻ (χ g) x‖ dx ≤ C W R ^ m`. The
constant depends on `E`, `G`, `m`, `N`, `a`, `b` and `B`, but not on the symbol `g`, its bound
`W`, the scale `R` or the cutoff `χ`. It follows from the scalar case by expanding `g` in a basis
of `G`. -/
theorem exists_integral_norm_fourierInv_cutoff_smul_le_of_finiteDimensional {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] (m : ℝ) {N : ℕ}
    (hN : finrank ℝ E < 2 * N) {a b : ℝ} (ha : 0 < a) (B : ℕ → ℝ) :
    ∃ C, ∀ (g : E → G) (W : ℝ), ContDiff ℝ ∞ g →
      (∀ i ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ W * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)) →
      ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) →
      ∫ x, ‖𝓕⁻ (fun ξ ↦ χ ξ • g ξ) x‖ ≤ C * W * R ^ m := by
  have : CompleteSpace G := FiniteDimensional.completeSpace ℂ G
  set e := Module.finBasis ℂ G
  set ℓ : Fin (finrank ℂ G) → G →L[ℂ] ℂ := fun i ↦ LinearMap.toContinuousLinearMap (e.coord i)
  obtain ⟨C, hC⟩ := exists_integral_norm_fourierInv_cutoff_smul_le (E := E) (H := ℂ) m hN ha B
  refine ⟨C * ∑ i, ‖e i‖ * ‖ℓ i‖, fun g W hg hgm R χ hR hχ hsupp hB ↦ ?_⟩
  have hcs : HasCompactSupport χ :=
    (isCompact_closedBall (0 : E) _).of_isClosed_subset (isClosed_tsupport χ)
      (subset_closedBall_of_one_add_norm_sq_le hR.le fun ξ hξ ↦ (hsupp ξ hξ).2)
  set σ : 𝓢(E, G) := (hcs.smul_right (f' := g)).toSchwartzMap (hχ.smul hg)
  have hσ : ⇑σ = fun ξ ↦ χ ξ • g ξ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  -- The coordinates of the dyadic piece are the dyadic pieces of the coordinates of `g`.
  have hcoord (i : Fin (finrank ℂ G)) :
      (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) = ⇑(SchwartzMap.postcompCLM (ℓ i) σ) := by
    ext ξ
    simp [hσ]
  have hint (i : Fin (finrank ℂ G)) :
      Integrable fun x ↦ ‖𝓕⁻ (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) x‖ := by
    rw [hcoord, ← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ (SchwartzMap.postcompCLM (ℓ i) σ)).integrable.norm
  have hpt (x : E) : ‖𝓕⁻ (fun ξ ↦ χ ξ • g ξ) x‖ ≤
      ∑ i, ‖e i‖ * ‖𝓕⁻ (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) x‖ := by
    rw [← hσ, ← SchwartzMap.fourierInv_coe]
    calc ‖𝓕⁻ σ x‖ = ‖∑ i, e.repr (𝓕⁻ σ x) i • e i‖ := by rw [e.sum_repr]
      _ ≤ ∑ i, ‖e.repr (𝓕⁻ σ x) i • e i‖ := norm_sum_le _ _
      _ = ∑ i, ‖e i‖ * ‖𝓕⁻ (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) x‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hcoord, ← SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_postcompCLM_apply,
          norm_smul, mul_comm]
        simp [ℓ]
  have hbound (i : Fin (finrank ℂ G)) :
      ∫ x, ‖𝓕⁻ (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) x‖ ≤ C * (‖ℓ i‖ * W) * R ^ m :=
    hC (ℓ i ∘ g) (‖ℓ i‖ * W) (((ℓ i).restrictScalars ℝ).contDiff.comp hg) (fun k hk ξ ↦
      (((ℓ i).restrictScalars ℝ).norm_iteratedFDeriv_comp_left hg.contDiffAt
        (mod_cast le_top)).trans (by
          rw [ContinuousLinearMap.norm_restrictScalars, mul_assoc]
          gcongr
          exact hgm k hk ξ)) R χ hR hχ hsupp hB
  calc ∫ x, ‖𝓕⁻ (fun ξ ↦ χ ξ • g ξ) x‖
      ≤ ∫ x, ∑ i, ‖e i‖ * ‖𝓕⁻ (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) x‖ :=
        integral_mono_of_nonneg (.of_forall fun x ↦ norm_nonneg _)
          (integrable_finsetSum _ fun i _ ↦ (hint i).const_mul _) (.of_forall hpt)
    _ = ∑ i, ‖e i‖ * ∫ x, ‖𝓕⁻ (fun ξ ↦ χ ξ • (ℓ i ∘ g) ξ) x‖ := by
        rw [integral_finsetSum _ fun i _ ↦ (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ ∑ i, ‖e i‖ * (C * (‖ℓ i‖ * W) * R ^ m) := by gcongr with i; exact hbound i
    _ = C * (∑ i, ‖e i‖ * ‖ℓ i‖) * W * R ^ m := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

end TauCeti
