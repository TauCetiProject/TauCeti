/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Kernels of dyadic pieces of symbols

A smooth function `g` with the symbol estimates `‖D^i g ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` of
order `m`, such as the Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (m / 2)`, behaves like the constant `R ^ m` on
frequencies with `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`. This file makes that precise at the level of convolution
kernels.

* `TauCeti.exists_integral_norm_fourierInv_cutoff_smul_le`: let `χ` be a smooth cutoff supported
  where `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`, with `‖D^k χ‖ ≤ B_k R ^ (-k)`. Then the kernel of the dyadic piece
  `χ g` has `L¹` norm at most `C R ^ m`, with `C` independent of `R` and `χ`. By
  `TauCeti.exists_norm_iteratedFDeriv_cutoff_smul_le` the product is a band-limited symbol at
  scale `R` with constant `O(R ^ m)`, and the scale-invariant `L¹` bound
  `SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset` applies.

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

/-- **Kernels of dyadic pieces of symbols.** Let `g` be a smooth function, valued in a complex
inner product space, with the symbol estimates `‖D^i g ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` of
order `m` for `i ≤ N`, and let `2N > n = dim E`,
`a > 0`, `b` and `B : ℕ → ℝ`. There is a constant `C` with the following property. Let `R > 0` and
let `χ` be a smooth real function such that `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ`
and `‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`. Then the kernel of the dyadic piece `χ g` satisfies

`∫ ‖𝓕⁻ (χ g) x‖ dx ≤ C R ^ m`. -/
theorem exists_integral_norm_fourierInv_cutoff_smul_le {g : E → H} (hg : ContDiff ℝ ∞ g) {m : ℝ}
    {N : ℕ} (hN : finrank ℝ E < 2 * N)
    (hgm : ∀ i ≤ N, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {a b : ℝ} (ha : 0 < a) (B : ℕ → ℝ) :
    ∃ C, ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) →
      ∫ x, ‖𝓕⁻ (fun ξ ↦ χ ξ • g ξ) x‖ ≤ C * R ^ m := by
  set e := stdOrthonormalBasis ℝ E
  obtain ⟨C₀, -, hC₀⟩ :=
    SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset (H := H) e hN
  obtain ⟨K, hK, hKχ⟩ :=
    exists_norm_iteratedFDeriv_cutoff_smul_le (hg.of_le (mod_cast le_top)) hgm (b := b) ha B
  -- The dyadic piece is a band-limited Schwartz function at the scale `t = (√b + 1) R`, with
  -- constant `A = K (√b + 1) ^ N R ^ m`.
  refine ⟨C₀ * (K * (√b + 1) ^ N), fun R χ hR hχ hsupp hB ↦ ?_⟩
  have hKχ := hKχ R χ hR (hχ.of_le (mod_cast le_top)) hsupp hB
  -- On the support of `χ`, the frequencies are at most `√b R`.
  set t : ℝ := (√b + 1) * R
  have ht : 0 < t := by positivity
  have hball : tsupport χ ⊆ closedBall 0 t := fun ξ hξ ↦ by
    have h := hsupp ξ hξ
    have hb : 0 ≤ b := nonneg_of_mul_nonneg_left ((by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2).trans
      h.2) (by positivity)
    have hξR : ‖ξ‖ ≤ √b * R := by
      rw [← Real.sqrt_sq (norm_nonneg ξ), ← Real.sqrt_sq hR.le, ← Real.sqrt_mul hb]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [mem_closedBall_zero_iff]
    nlinarith
  have hcs : HasCompactSupport χ :=
    (isCompact_closedBall (0 : E) t).of_isClosed_subset (isClosed_tsupport χ) hball
  set σ : 𝓢(E, H) := (hcs.smul_right (f' := g)).toSchwartzMap (hχ.smul hg)
  have hσ : ⇑σ = fun ξ ↦ χ ξ • g ξ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hσt : Function.support σ ⊆ closedBall 0 t := fun ξ hξ ↦ by
    refine hball (subset_tsupport _ ?_)
    rw [Function.mem_support] at hξ ⊢
    rintro hχξ
    simp [hσ, hχξ] at hξ
  have hσA (ξ : E) : ‖σ ξ‖ ≤ K * (√b + 1) ^ N * R ^ m := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), hσ]
    refine (hKχ 0 (Nat.zero_le _) ξ).trans ?_
    rw [pow_zero, div_one, mul_right_comm]
    exact le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ (le_add_of_nonneg_left (Real.sqrt_nonneg b)))
  have hσN (j : Fin (finrank ℝ E)) (ξ : E) :
      ‖(∂_{e j})^[N] σ ξ‖ ≤ K * (√b + 1) ^ N * R ^ m / t ^ N := by
    rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ N σ ξ).le_opNorm _).trans ?_
    simp only [e.orthonormal.1 j, Finset.prod_const_one, mul_one]
    rw [hσ]
    refine (hKχ N le_rfl ξ).trans_eq ?_
    simp only [t, mul_pow]
    field_simp
  have hint := hC₀ σ ht hσt hσA hσN
  rwa [SchwartzMap.fourierInv_coe, hσ, ← mul_assoc] at hint

end TauCeti
