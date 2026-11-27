/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Poisson.Periodic
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Conductor

/-!
# Poisson summation for Jacobi symbols

`SchwartzMap.tsum_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier` transforms a Schwartz sum
weighted by an odd squarefree Jacobi character. The phase and constant are those of
`ZMod.stdAddChar`. The theorem applies periodic Poisson summation and evaluates the finite
Fourier coefficients using `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`.
`SchwartzMap.tsum_pnat_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier` gives the scaled form for
weights that vanish at nonpositive integer sampling indices.

## References

* D. R. Heath-Brown, *A mean value estimate for real character sums*, Lemma 11.
-/

public section

open scoped SchwartzMap FourierTransform

namespace SchwartzMap

/-- Poisson summation for an odd squarefree Jacobi symbol. In the dual sum the symbol weights
the Fourier transform at `n / N`, with prefactor the quadratic Gauss sum divided by `N`.
This is the bilateral Schwartz form of Heath-Brown's Lemma 11. -/
theorem tsum_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier (f : 𝓢(ℝ, ℂ))
    {N : ℕ} [NeZero N] (hN : Odd N) (hs : Squarefree N) :
    (∑' n : ℤ, (jacobiSym n N : ℂ) * f n) =
      (gaussSum (TauCeti.jacobiChar ℂ N) ZMod.stdAddChar / (N : ℂ)) *
        ∑' n : ℤ, (jacobiSym n N : ℂ) * (𝓕 f) ((n : ℝ) / N) := by
  let χ := TauCeti.jacobiChar ℂ N
  have hp : χ.IsPrimitive := TauCeti.isPrimitive_jacobiChar_of_odd_squarefree (by norm_num) hN hs
  have hχ (n : ℤ) : χ n = jacobiSym n N := TauCeti.jacobiChar_intCast n
  have hd (n : ℤ) : ZMod.dft.symm (χ : ZMod N → ℂ) (n : ZMod N) =
      (gaussSum χ ZMod.stdAddChar / (N : ℂ)) * (jacobiSym n N : ℂ) := by
    rw [ZMod.invDFT_apply', hp.fourierTransform_eq_inv_mul_gaussSum, neg_neg]
    rw [TauCeti.jacobiChar_isQuadratic.inv, hχ, smul_eq_mul]
    ring
  simpa only [hχ, hd, mul_assoc, tsum_mul_left] using
    f.tsum_mul_periodic_eq_tsum_invDFT_fourier (χ : ZMod N → ℂ)

/-- Heath-Brown's Poisson formula for the positive-integer sum with weight `f(n / M)`.
The weight vanishes at `n / M` for nonpositive integers `n`. The dual Fourier transform
is sampled at `M n / N`, with the dilation factor `|M|`. -/
theorem tsum_pnat_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier (f : 𝓢(ℝ, ℂ))
    {N : ℕ} [NeZero N] (hN : Odd N) (hs : Squarefree N) {M : ℝ}
    (hf : ∀ n : ℤ, n ≤ 0 → f ((n : ℝ) / M) = 0) :
    (∑' n : ℕ+, (jacobiSym (n : ℤ) N : ℂ) * f ((n : ℝ) / M)) =
      (((|M| : ℝ) : ℂ) * gaussSum (TauCeti.jacobiChar ℂ N) ZMod.stdAddChar / (N : ℂ)) *
        ∑' n : ℤ, (jacobiSym n N : ℂ) * (𝓕 f) (M * n / N) := by
  rcases eq_or_ne M 0 with rfl | hM
  · have hz : f 0 = 0 := by simpa only [div_zero] using hf 0 le_rfl
    simp [hz]
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 M⁻¹ (inv_ne_zero hM))
  let g := compCLMOfContinuousLinearEquiv ℂ e f
  have hg : (g : ℝ → ℂ) = fun x ↦ f (x / M) := by
    funext x
    simp only [g, e, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, div_eq_mul_inv]
  have hfourier (y : ℝ) : (𝓕 g) y = ((|M| : ℝ) : ℂ) * (𝓕 f) (M * y) := by
    have heq : (g : ℝ → ℂ) = fun x ↦ f (M⁻¹ • x) := by
      simp only [hg, div_eq_inv_mul, smul_eq_mul]
    rw [fourier_coe g, heq, TauCeti.fourier_comp_smul, fourier_coe f]
    simp only [Module.finrank_self, pow_one, abs_inv, inv_inv, smul_eq_mul, Complex.real_smul]
  have hleft :
      (∑' n : ℕ+, (jacobiSym (n : ℤ) N : ℂ) * f ((n : ℝ) / M)) =
        ∑' n : ℤ, (jacobiSym n N : ℂ) * g n := by
    have hinj : Function.Injective (fun n : ℕ+ ↦ (n : ℤ)) :=
      (Nat.cast_injective (R := ℤ)).comp PNat.coe_injective
    convert hinj.tsum_eq (f := fun n : ℤ ↦ (jacobiSym n N : ℂ) * g n) ?_ using 2
    · simp only [hg, Int.cast_natCast]
    · intro n hn
      have hn₀ : 0 < n := by grind
      exact Set.mem_range.mpr ⟨⟨n.toNat, by lia⟩, Int.toNat_of_nonneg hn₀.le⟩
  rw [hleft, g.tsum_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier hN hs]
  simp_rw [hfourier, mul_left_comm (jacobiSym _ _ : ℂ) ((|M| : ℝ) : ℂ),
    ← mul_div_assoc, tsum_mul_left]
  ring

end SchwartzMap
