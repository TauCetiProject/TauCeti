/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Poisson.Periodic
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Conductor

/-!
# Poisson summation for Jacobi symbols

`SchwartzMap.tsum_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier` transforms a Schwartz sum
weighted by an odd squarefree Jacobi character. The phase and constant are those of
`ZMod.stdAddChar`. The theorem applies periodic Poisson summation and evaluates the finite
Fourier coefficients using `SchwartzMap.tsum_mul_dirichletCharacter_eq_gaussSum_mul_tsum_fourier`.
`SchwartzMap.tsum_pnat_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier` gives the scaled form for
weighted summands that vanish at nonpositive integer sampling indices.

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
    {N : ℕ} (hN : Odd N) (hs : Squarefree N) :
    (∑' n : ℤ, (jacobiSym n N : ℂ) * f n) =
      (@gaussSum (ZMod N) _ (@ZMod.fintype N ⟨hs.ne_zero⟩) ℂ _
        (@TauCeti.jacobiChar ℂ _ N ⟨hs.ne_zero⟩) (@ZMod.stdAddChar N ⟨hs.ne_zero⟩) / (N : ℂ)) *
        ∑' n : ℤ, (jacobiSym n N : ℂ) * (𝓕 f) ((n : ℝ) / N) := by
  let : NeZero N := ⟨hs.ne_zero⟩
  have hp := TauCeti.isPrimitive_jacobiChar_of_odd_squarefree (R := ℂ) (by norm_num) hN hs
  simpa only [TauCeti.jacobiChar_isQuadratic.inv, TauCeti.jacobiChar_intCast] using
    f.tsum_mul_dirichletCharacter_eq_gaussSum_mul_tsum_fourier hp

/-- Heath-Brown's Poisson formula for the positive-integer sum with weight `f(n / M)`.
The weighted summand vanishes for nonpositive integers `n`. The dual Fourier transform
is sampled at `M n / N`, with the dilation factor `|M|`. -/
theorem tsum_pnat_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier (f : 𝓢(ℝ, ℂ))
    {N : ℕ} (hN : Odd N) (hs : Squarefree N) {M : ℝ}
    (hf : ∀ n : ℤ, n ≤ 0 → (jacobiSym n N : ℂ) * f ((n : ℝ) / M) = 0) :
    (∑' n : ℕ+, (jacobiSym (n : ℤ) N : ℂ) * f ((n : ℝ) / M)) =
      (((|M| : ℝ) : ℂ) *
        @gaussSum (ZMod N) _ (@ZMod.fintype N ⟨hs.ne_zero⟩) ℂ _
        (@TauCeti.jacobiChar ℂ _ N ⟨hs.ne_zero⟩) (@ZMod.stdAddChar N ⟨hs.ne_zero⟩) / (N : ℂ)) *
        ∑' n : ℤ, (jacobiSym n N : ℂ) * (𝓕 f) (M * n / N) := by
  let : NeZero N := ⟨hs.ne_zero⟩
  rcases eq_or_ne M 0 with rfl | hM
  · have hneg : (jacobiSym (-1) N : ℂ) ≠ 0 := by
      norm_cast
      simp [jacobiSym.eq_zero_iff_not_coprime]
    have hz : f 0 = 0 := by
      exact (mul_eq_zero.mp (by simpa only [div_zero] using hf (-1) (by decide))).resolve_left hneg
    simp [hz]
  let g := f.dilate (inv_ne_zero hM)
  have hg (x : ℝ) : g x = f (x / M) := by rw [dilate_apply, smul_eq_mul, div_eq_inv_mul]
  have hfourier (y : ℝ) : (𝓕 g) y = ((|M| : ℝ) : ℂ) * (𝓕 f) (M * y) := by
    rw [fourier_dilate_apply, Complex.real_smul]
    simp only [Module.finrank_self, pow_one, abs_inv, inv_inv, smul_eq_mul]
  have hleft :
      (∑' n : ℕ+, (jacobiSym (n : ℤ) N : ℂ) * f ((n : ℝ) / M)) =
        ∑' n : ℤ, (jacobiSym n N : ℂ) * g n := by
    have hinj : Function.Injective (fun n : ℕ+ ↦ (n : ℤ)) :=
      (Nat.cast_injective (R := ℤ)).comp PNat.coe_injective
    convert hinj.tsum_eq (f := fun n : ℤ ↦ (jacobiSym n N : ℂ) * g n) ?_ using 2
    · simp only [hg, Int.cast_natCast]
    · intro n hn
      have hn₀ : 0 < n := lt_of_not_ge fun h ↦ hn (by simpa only [hg] using hf n h)
      exact Set.mem_range.mpr (CanLift.prf (β := ℕ+) n hn₀)
  rw [hleft, g.tsum_jacobiSym_mul_eq_gaussSum_mul_tsum_fourier hN hs]
  simp_rw [hfourier, mul_left_comm (jacobiSym _ _ : ℂ) ((|M| : ℝ) : ℂ),
    ← mul_div_assoc, tsum_mul_left]
  ring

end SchwartzMap
