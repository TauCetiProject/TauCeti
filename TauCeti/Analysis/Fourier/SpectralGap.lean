/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle

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

The interval versions below identify first harmonics by their Fourier support. They provide the
bridge between the abstract circle equality case and cosine--sine formulas on a real interval.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Theorem 258.
-/

public section

open MeasureTheory AddCircle Set Complex
open scoped Real

namespace TauCeti

variable {T : ℝ} [Fact (0 < T)]

section Interval

variable {a b : ℝ}

/-- A first harmonic on `[a, b]` has no Fourier coefficients outside the frequencies `±1`. -/
theorem fourierCoeffOn_cos_smul_add_sin_smul (hab : a < b) (u v : ℂ) {n : ℤ}
    (hn₁ : n ≠ 1) (hn₂ : n ≠ -1) :
    fourierCoeffOn hab (fun t => Real.cos (2 * π * t / (b - a)) • u +
      Real.sin (2 * π * t / (b - a)) • v) n = 0 := by
  have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  let G : C(AddCircle (b - a), ℂ) :=
    ((u - I * v) / 2) • fourier 1 + ((u + I * v) / 2) • fourier (-1)
  have hG : AddCircle.liftIoc (b - a) a (fun t => Real.cos (2 * π * t / (b - a)) • u +
      Real.sin (2 * π * t / (b - a)) • v) = G := by
    funext x
    obtain ⟨t, ht, rfl⟩ : x ∈ ((↑) : ℝ → AddCircle (b - a)) '' Ioc a (a + (b - a)) := by
      rw [AddCircle.coe_image_Ioc_eq]
      trivial
    rw [AddCircle.liftIoc_coe_apply ht]
    simp only [G, ContinuousMap.add_apply, ContinuousMap.smul_apply, fourier_one_coe_apply,
      fourier_neg_one_coe_apply, real_smul, smul_eq_mul]
    linear_combination ((Real.sin (2 * π * t / (b - a)) : ℂ) * v) * I_sq
  have hint (k : ℤ) : Integrable (fourier k : AddCircle (b - a) → ℂ) AddCircle.haarAddCircle :=
    (map_continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- By definition, `fourierCoeffOn` is the Fourier coefficient of the `liftIoc` periodization.
  change fourierCoeff (AddCircle.liftIoc (b - a) a _) n = 0
  rw [hG, ContinuousMap.coe_add, ContinuousMap.coe_smul, ContinuousMap.coe_smul,
    fourierCoeff.add ((hint 1).smul _) ((hint (-1)).smul _)]
  simp [fourierCoeff.const_smul, fourierCoeff_fourier, hn₁, hn₂]

/-- A continuous closed curve on `[a, b]` whose Fourier coefficients vanish outside the
frequencies `±1` is a first harmonic at every point of `[a, b]`. -/
theorem exists_cos_smul_add_sin_smul (hab : a < b) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc a b)) (hgab : g a = g b)
    (h : ∀ n : ℤ, n ≠ 1 → n ≠ -1 → fourierCoeffOn hab g n = 0) :
    ∃ u v : ℂ, ∀ t ∈ Icc a b, g t = Real.cos (2 * π * t / (b - a)) • u +
      Real.sin (2 * π * t / (b - a)) • v := by
  have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  let G : C(AddCircle (b - a), ℂ) := ⟨AddCircle.liftIoc (b - a) a g,
    AddCircle.liftIoc_continuous (by rwa [add_sub_cancel]) (by rwa [add_sub_cancel])⟩
  -- By definition, `fourierCoeffOn` is the Fourier coefficient of the `liftIoc` periodization.
  have hc (n : ℤ) : fourierCoeff G n = fourierCoeffOn hab g n := rfl
  have hsupp (n : ℤ) (hn : n ∉ ({1, -1} : Finset ℤ)) : fourierCoeff G n = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [hc, h n hn.1 hn.2]
  have hrepr (x : AddCircle (b - a)) : G x = fourierCoeffOn hab g 1 * fourier 1 x +
      fourierCoeffOn hab g (-1) * fourier (-1) x := by
    have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ)
      (s := ({1, -1} : Finset ℤ))
      (f := fun n => fourierCoeff G n • fourier n x) fun n hn => by simp [hsupp n hn]
    rw [(has_pointwise_sum_fourier_series_of_summable
      (summable_of_ne_finset_zero hsupp) x).unique hs, Finset.sum_pair (by decide)]
    rfl
  have hab' : ((b : ℝ) : AddCircle (b - a)) = (a : ℝ) := by
    simpa using AddCircle.coe_add_period (b - a) a
  have hGg (t : ℝ) (ht : t ∈ Icc a b) : g t = G t := by
    rcases ht.1.eq_or_lt with rfl | hlt
    · rw [hgab, ← hab']
      exact (AddCircle.liftIoc_coe_apply (by simp [hab])).symm
    · exact (AddCircle.liftIoc_coe_apply (by simp [hlt, ht.2])).symm
  refine ⟨fourierCoeffOn hab g 1 + fourierCoeffOn hab g (-1),
    I * (fourierCoeffOn hab g 1 - fourierCoeffOn hab g (-1)), fun t ht => ?_⟩
  rw [hGg t ht, hrepr, fourier_one_coe_apply, fourier_neg_one_coe_apply, real_smul, real_smul]
  ring

end Interval

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

private theorem fourierCoeff_first_harmonics (a b : ℂ) (n : ℤ) :
    fourierCoeff (a • fourierLp 2 1 + b • fourierLp 2 (-1) : Lp ℂ 2 (@haarAddCircle T _)) n =
      (if n = 1 then a else 0) + (if n = -1 then b else 0) := by
  classical
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, coe_fourierBasis]
  simp [inner_add_right, inner_smul_right,
    orthonormal_iff_ite.mp (orthonormal_fourier (T := T)), mul_ite]

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
      rw [hf, fourierCoeff_first_harmonics]
      simp [hn, hp]
    simp [hc]

end TauCeti
