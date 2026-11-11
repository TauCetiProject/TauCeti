/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Kernels of Bessel-weighted dyadic symbols

The Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (s / 2)` is a symbol of order `s`, so on frequencies with
`1 + ‖ξ‖ ^ 2 ≍ R ^ 2` it behaves like the constant `R ^ s`. This file makes that precise at the
level of convolution kernels.

* `TauCeti.exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le`: let `χ` be a smooth cutoff
  supported where `1 + ‖ξ‖ ^ 2 ≍ R ^ 2`, with `‖D^k χ‖ ≤ B_k R ^ (-k)`. Then the kernel of the
  symbol `(1 + ‖ξ‖ ^ 2) ^ (s / 2) χ ξ` has `L¹` norm at most `C R ^ s`, with `C` independent of `R`
  and `χ`. By `TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_mul_le` the product is a
  band-limited symbol at scale `R` with constant `O(R ^ s)`, and the scale-invariant `L¹` bound
  `SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset` applies.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Lemma 6.2.1.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.2.
-/

public section

open scoped FourierTransform SchwartzMap LineDeriv ContDiff
open FourierTransform MeasureTheory Metric Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti

/-- **Kernels of Bessel-weighted dyadic symbols.** Let `2N > n = dim E`, `a > 0`, `b` and
`B : ℕ → ℝ`. There is a constant `C` with the following property. Let `R > 0` and let `χ` be a
smooth real function such that `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ` and
`‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`. Then the kernel of the symbol `(1 + ‖ξ‖ ^ 2) ^ (s / 2) χ ξ`
satisfies

`∫ ‖𝓕⁻ ((1 + ‖·‖ ^ 2) ^ (s / 2) χ) x‖ dx ≤ C R ^ s`. -/
theorem exists_integral_norm_fourierInv_one_add_norm_sq_rpow_mul_le (s : ℝ) {a b : ℝ}
    (ha : 0 < a) {N : ℕ} (hN : finrank ℝ E < 2 * N) (B : ℕ → ℝ) :
    ∃ C, ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) →
      ∫ x, ‖𝓕⁻ (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ : ℝ) : ℂ)) x‖ ≤ C * R ^ s := by
  set e := stdOrthonormalBasis ℝ E
  obtain ⟨C₀, -, hC₀⟩ :=
    SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset (H := ℂ) e hN
  obtain ⟨K, hK, hKχ⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_mul_le (E := E) s
    (b := b) ha N B
  -- The symbol is a band-limited Schwartz function at the scale `t = (√b + 1) R`, with constant
  -- `A = K (√b + 1) ^ N R ^ s`.
  refine ⟨C₀ * (K * (√b + 1) ^ N), fun R χ hR hχ hsupp hB ↦ ?_⟩
  have hKχ := hKχ R χ hR hχ hsupp hB
  set g : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ ↦ by positivity).mul hχ
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
  set σ : 𝓢(E, ℂ) := (hcs.mul_left.comp_left Complex.ofReal_zero : HasCompactSupport
    fun ξ ↦ (g ξ : ℂ)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have hσ : ⇑σ = fun ξ ↦ (g ξ : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hσD (k : ℕ) (ξ : E) : ‖iteratedFDeriv ℝ k σ ξ‖ = ‖iteratedFDeriv ℝ k g ξ‖ := by
    rw [hσ]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast le_top)
  have hσt : Function.support σ ⊆ closedBall 0 t := fun ξ hξ ↦ by
    refine hball (subset_tsupport _ ?_)
    rw [Function.mem_support] at hξ ⊢
    rintro hχξ
    simp [hσ, g, hχξ] at hξ
  have hσA (ξ : E) : ‖σ ξ‖ ≤ K * (√b + 1) ^ N * R ^ s := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), hσD]
    refine (hKχ 0 (Nat.zero_le _) ξ).trans ?_
    rw [pow_zero, div_one, mul_right_comm]
    exact le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ (le_add_of_nonneg_left (Real.sqrt_nonneg b)))
  have hσN (j : Fin (finrank ℝ E)) (ξ : E) :
      ‖(∂_{e j})^[N] σ ξ‖ ≤ K * (√b + 1) ^ N * R ^ s / t ^ N := by
    rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ N σ ξ).le_opNorm _).trans ?_
    simp only [e.orthonormal.1 j, Finset.prod_const_one, mul_one]
    refine (hσD N ξ).trans_le ((hKχ N le_rfl ξ).trans_eq ?_)
    simp only [t, mul_pow]
    field_simp
  have hint := hC₀ σ ht hσt hσA hσN
  rwa [SchwartzMap.fourierInv_coe, hσ, ← mul_assoc] at hint

end TauCeti
