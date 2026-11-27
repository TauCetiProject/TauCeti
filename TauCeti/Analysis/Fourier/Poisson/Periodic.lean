/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.ZMod
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.PoissonSummation
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Poisson summation with periodic coefficients

`SchwartzMap.tsum_mul_periodic_eq_tsum_invDFT_fourier` splits an integer sum over its residue
classes and applies `SchwartzMap.tsum_eq_tsum_fourier` to each class. The dual coefficients
are the normalized inverse discrete Fourier transform on `ZMod N`.

This is the analytic step in Heath-Brown's *A mean value estimate for real character sums*,
Lemma 11, where the periodic coefficients are the values of a Jacobi symbol.
-/

public section

open scoped SchwartzMap FourierTransform
open ZMod

namespace SchwartzMap

/-- Poisson summation on the progression `a + N ℤ`, with positive modulus `N`. -/
theorem tsum_apply_int_mul_add_eq_tsum_fourier (f : 𝓢(ℝ, ℂ)) {N : ℕ} [NeZero N] (a : ZMod N) :
    (∑' n : ℤ, f (n * (N : ℝ) + a.val)) =
      ∑' n : ℤ, (N : ℂ)⁻¹ * (𝓕 f) ((n : ℝ) / N) * stdAddChar (a * (n : ZMod N)) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 N hN.ne')
  let g := compCLMOfContinuousLinearEquiv ℂ e f
  have hg : (g : ℝ → ℂ) = fun x ↦ f ((N : ℝ) • x) := by
    funext x
    simp only [g, e, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, smul_eq_mul, mul_comm]
  have hfg (n : ℤ) : (𝓕 g) n = (N : ℂ)⁻¹ * (𝓕 f) ((n : ℝ) / N) := by
    rw [fourier_coe g, hg, TauCeti.fourier_comp_smul, fourier_coe f]
    simp only [Module.finrank_self, pow_one, abs_of_pos hN, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_inv_mul]
  calc
    _ = ∑' n : ℤ, g (a.val / (N : ℝ) + n) := by
      refine tsum_congr fun n ↦ ?_
      rw [hg]
      dsimp only
      rw [smul_eq_mul, mul_add, mul_div_cancel₀ _ hN.ne', mul_comm (N : ℝ), add_comm]
    _ = _ := by rw [g.tsum_eq_tsum_fourier]; simp_rw [hfg, fourier_val_div_eq_stdAddChar]

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
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (N : ℝ)⁻¹ (inv_ne_zero hN.ne'))
  let g := compCLMOfContinuousLinearEquiv ℂ e (𝓕 f)
  have hg (n : ℤ) : g n = (𝓕 f) ((n : ℝ) / N) := by
    simp only [g, e, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, div_eq_mul_inv]
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
      have ha := f.tsum_apply_int_mul_add_eq_tsum_fourier (a.val : ZMod N)
      rw [val_cast_of_lt a.isLt] at ha
      have heq : (finEquiv N).toEquiv a = (a.val : ZMod N) := finEquiv_apply a
      simp only [heq, tsum_mul_left, ha]
    _ = _ := by
      rw [← Summable.tsum_finsetSum fun a _ ↦ hd a]
      refine tsum_congr fun n ↦ ?_
      rw [invDFT_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [smul_eq_mul]
      ring

end SchwartzMap
