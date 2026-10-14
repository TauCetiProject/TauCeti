/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The sharp spectral gap on the circle

For a mean-zero complex `L²` function on the circle, its squared norm is at most the
sum of `n²` times its squared Fourier coefficients, provided this spectral energy is
summable. Equality holds exactly on the span of the two first harmonics. The Haar
measure in these statements has total mass one.

This is the spectral comparison underlying the sharp periodic Wirtinger inequality
and its equality case. It does not assume differentiability: identifying the spectral
energy with a derivative integral is a separate integration-by-parts step. In particular,
the equality conclusion remains available when that step uses only a weak or an
almost-everywhere derivative.

The proofs use Mathlib's Fourier Hilbert basis and Parseval identity.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Theorem 258.
-/

public section

open MeasureTheory AddCircle

namespace TauCeti

variable {T : ℝ} [Fact (0 < T)]

private theorem sq_fourierCoeff_le_frequency_sq (f : Lp ℂ 2 (@haarAddCircle T _))
    (hzero : fourierCoeff f 0 = 0) (n : ℤ) :
    ‖fourierCoeff f n‖ ^ 2 ≤ (n : ℝ) ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, hzero]
  have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
  nlinarith [sq_nonneg ‖fourierCoeff f n‖]

/-- The sharp spectral-gap inequality for a mean-zero `L²` function on the circle.
Summability is essential: an unsummable real `tsum` would otherwise be zero. -/
theorem integral_norm_sq_le_tsum_frequency_sq_fourierCoeff
    (f : Lp ℂ 2 (@haarAddCircle T _)) (hzero : fourierCoeff f 0 = 0)
    (henergy : Summable (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeff f n‖ ^ 2)) :
    (∫ t, ‖f t‖ ^ 2 ∂haarAddCircle) ≤
      ∑' n : ℤ, (n : ℝ) ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
  rw [← tsum_sq_fourierCoeff f]
  exact (hasSum_sq_fourierCoeff f).summable.tsum_le_tsum
    (sq_fourierCoeff_le_frequency_sq f hzero) henergy

private theorem eq_first_harmonics_of_fourierCoeff_eq_zero
    (f : Lp ℂ 2 (@haarAddCircle T _))
    (h : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → fourierCoeff f n = 0) :
    f = fourierCoeff f 1 • fourierLp 2 1 + fourierCoeff f (-1) • fourierLp 2 (-1) := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ)
    (s := ({1, -1} : Finset ℤ))
    (f := fun n => fourierCoeff f n • fourierLp (T := T) 2 n) (by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [h n hn.1 hn.2])
  simpa using (hasSum_fourier_series_L2 f).unique hs

/-- Equality in the circle spectral gap holds exactly for linear combinations of
its positive and negative first harmonics. Equality is in `L²`, hence is independent
of the choice of almost-everywhere representative. -/
theorem integral_norm_sq_eq_tsum_frequency_sq_fourierCoeff_iff
    (f : Lp ℂ 2 (@haarAddCircle T _)) (hzero : fourierCoeff f 0 = 0)
    (henergy : Summable (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeff f n‖ ^ 2)) :
    (∫ t, ‖f t‖ ^ 2 ∂haarAddCircle) =
        ∑' n : ℤ, (n : ℝ) ^ 2 * ‖fourierCoeff f n‖ ^ 2 ↔
      ∃ a b : ℂ, f = a • fourierLp 2 1 + b • fourierLp 2 (-1) := by
  constructor
  · intro heq
    refine ⟨_, _, eq_first_harmonics_of_fourierCoeff_eq_zero f ?_⟩
    intro n hn hp
    by_contra hc
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hc (hn0 ▸ hzero)
    have hn2 : (1 : ℝ) < (n : ℝ) ^ 2 := by
      have hi : (1 : ℤ) < n ^ 2 := by
        have : n ≤ -2 ∨ 2 ≤ n := by omega
        rcases this with h | h <;> nlinarith
      exact_mod_cast hi
    have hstrict : ‖fourierCoeff f n‖ ^ 2 <
        (n : ℝ) ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
      have := sq_pos_of_pos (norm_pos_iff.mpr hc)
      nlinarith
    have hlt := (hasSum_sq_fourierCoeff f).summable.tsum_lt_tsum
      (sq_fourierCoeff_le_frequency_sq f hzero) hstrict henergy
    rw [tsum_sq_fourierCoeff, heq] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨a, b, hf⟩
    rw [← tsum_sq_fourierCoeff f]
    apply tsum_congr
    intro n
    by_cases hn : n = 1
    · simp [hn]
    by_cases hp : n = -1
    · simp [hp]
    have hc : fourierCoeff f n = 0 := by
      rw [hf, ← fourierBasis_repr]
      rw [← coe_fourierBasis]
      simp only [map_add, map_smul, HilbertBasis.repr_self, lp.coeFn_add,
        lp.coeFn_smul, lp.coeFn_single]
      dsimp only [Pi.add_apply, Pi.smul_apply]
      simp [hn, hp]
    simp [hc]

end TauCeti
