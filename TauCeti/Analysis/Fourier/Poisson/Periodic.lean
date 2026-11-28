/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.ZMod
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.ZLattice
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Poisson summation with periodic coefficients

`SchwartzMap.tsum_apply_int_mul_add_eq_tsum_fourier` applies Mathlib’s
`SchwartzMap.tsum_eq_tsum_fourier` after dilation to sum along a real progression.
`SchwartzMap.tsum_mul_periodic_eq_tsum_invDFT_fourier` splits an integer sum over its residue
classes and applies `SchwartzMap.tsum_eq_tsum_fourier` to each class. The dual coefficients
are the normalized inverse discrete Fourier transform on `ZMod N`.
`SchwartzMap.tsum_mul_dirichletCharacter_eq_gaussSum_mul_tsum_fourier` evaluates this inverse
transform for primitive characters using `DirichletCharacter.IsPrimitive.invDFT_apply`.

This is the analytic step in Heath-Brown's *A mean value estimate for real character sums*,
Lemma 11, where the periodic coefficients are the values of a Jacobi symbol.
-/

public section

open scoped SchwartzMap FourierTransform
open ZMod

namespace SchwartzMap

/-- Poisson summation on the real progression `a + T ℤ`. At `T = 0` both totalized sums
are zero. -/
theorem tsum_apply_int_mul_add_eq_tsum_fourier (f : 𝓢(ℝ, ℂ)) (T a : ℝ) :
    (∑' n : ℤ, f (n * T + a)) = ∑' n : ℤ,
      ((|T|⁻¹ : ℝ) : ℂ) * (𝓕 f) ((n : ℝ) / T) * fourier n ((a / T : ℝ) : UnitAddCircle) := by
  rcases eq_or_ne T 0 with rfl | hT
  · have hz : ((|0|⁻¹ : ℝ) : ℂ) = 0 := by simp only [abs_zero, _root_.inv_zero, Complex.ofReal_zero]
    simp only [mul_zero, zero_add, hz, zero_mul, tsum_zero, tsum_const,
      Nat.card_eq_zero_of_infinite, zero_nsmul]
  calc
    _ = ∑' n : ℤ, f.dilate hT (a / T + n) := by
      refine tsum_congr fun n ↦ ?_
      rw [dilate_apply, mul_add, mul_div_cancel₀ _ hT, mul_comm T, add_comm]
    _ = _ := by
      rw [(f.dilate hT).tsum_eq_tsum_fourier]
      simp_rw [fourier_dilate_apply, Complex.real_smul]

/-- Poisson summation for a Schwartz function weighted by a periodic family of complex numbers.
The dual series is sampled at integer multiples of `1 / N`. -/
theorem tsum_mul_periodic_eq_tsum_invDFT_fourier (f : 𝓢(ℝ, ℂ))
    {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) :
    (∑' n : ℤ, Φ n * f n) = ∑' n : ℤ, (ZMod.dft.symm Φ) n * (𝓕 f) ((n : ℝ) / N) := by
  classical
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hSchwartz (g : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ ↦ ‖g (n : ℝ)‖) := by
    have h := g.summable_norm_apply_sum_intCast_smul (OrthonormalBasis.singleton Unit ℝ)
    have hinj : Function.Injective (fun (n : ℤ) (_ : Unit) ↦ n) := fun _ _ hn ↦ congrFun hn ()
    simpa only [Function.comp_def, Finset.univ_unique, OrthonormalBasis.singleton_apply,
      smul_eq_mul, mul_one, Finset.sum_singleton] using h.comp_injective hinj
  have hs : Summable fun n : ℤ ↦ Φ n * f (n : ℝ) := by
    refine ((hSchwartz f).mul_left (∑ a : ZMod N, ‖Φ a‖)).of_norm_bounded ?_
    intro n
    rw [norm_mul]
    gcongr
    exact Finset.single_le_sum (fun a _ ↦ norm_nonneg (Φ a)) (Finset.mem_univ (n : ZMod N))
  let g := (𝓕 f).dilate (inv_ne_zero hN.ne')
  have hg (n : ℤ) : g n = (𝓕 f) ((n : ℝ) / N) := by
    rw [dilate_apply, div_eq_inv_mul]
  have hd (a : ZMod N) : Summable fun n : ℤ ↦
      Φ a * ((N : ℂ)⁻¹ * (𝓕 f) ((n : ℝ) / N) * stdAddChar (a * (n : ZMod N))) := by
    refine ((hSchwartz g).mul_left (‖Φ a‖ * ‖(N : ℂ)⁻¹‖)).of_norm_bounded ?_
    intro n
    simp only [norm_mul, AddChar.norm_apply, mul_one, hg, mul_assoc, le_refl]
  rw [TauCeti.tsum_int_eq_sum_fin_tsum hs N]
  -- Rewrite each residue-class sum using the shifted Poisson formula.
  calc
    _ = ∑ a : ZMod N, ∑' n : ℤ,
        Φ a * ((N : ℂ)⁻¹ * (𝓕 f) ((n : ℝ) / N) * stdAddChar (a * (n : ZMod N))) := by
      rw [← (finEquiv N).toEquiv.sum_comp]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      push_cast
      simp only [natCast_self, mul_zero, zero_add]
      have ha := f.tsum_apply_int_mul_add_eq_tsum_fourier N (a.val : ℝ)
      simp_rw [abs_of_pos hN, Complex.ofReal_inv, Complex.ofReal_natCast] at ha
      have heq : (finEquiv N).toEquiv a = (a.val : ZMod N) := finEquiv_apply a
      simpa only [heq, tsum_mul_left, ← fourier_val_div_eq_stdAddChar,
        val_cast_of_lt a.isLt] using congrArg (Φ (a.val : ZMod N) * ·) ha
    _ = _ := by
      rw [← Summable.tsum_finsetSum fun a _ ↦ hd a]
      refine tsum_congr fun n ↦ ?_
      rw [invDFT_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [smul_eq_mul]
      ring

/-- Poisson summation weighted by a primitive Dirichlet character. On the dual side the
inverse character weights the Fourier samples at `n / N`, with the Gauss sum divided by `N`. -/
theorem tsum_mul_dirichletCharacter_eq_gaussSum_mul_tsum_fourier (f : 𝓢(ℝ, ℂ))
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    (∑' n : ℤ, χ n * f n) = (gaussSum χ stdAddChar / (N : ℂ)) *
      ∑' n : ℤ, χ⁻¹ (n : ZMod N) * (𝓕 f) ((n : ℝ) / N) := by
  simpa only [hχ.invDFT_apply, mul_assoc, tsum_mul_left] using
    f.tsum_mul_periodic_eq_tsum_invDFT_fourier (χ : ZMod N → ℂ)

end SchwartzMap
