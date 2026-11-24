/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ConstantOffDiagonal
public import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence

/-!
# Spectral stability under constant upper-entry perturbations

Adding a Hermitian matrix with upper entries tending to zero preserves weak spectral limits,
uniformly in both the dimension and the unperturbed matrix. The lower entries are conjugate
and the diagonal is zero. No operator-norm bound or rank bound on the whole perturbation is
assumed: for a purely imaginary upper entry it can have full rank.

For block size `d + 1` and nonreal `z`, the transform error is at most

`2 / ((d + 1) |Im z|) + √(d + 1) ‖c‖ / |Im z|²`.

The first term comes from the rank of the block approximation, and the second from the
Frobenius norm of its error. First let the upper entry tend to zero, then let the block size
tend to infinity. This is the deterministic reduction needed to center complex Wigner entries.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), proof of Theorem 2.1.
-/

public section

noncomputable section

open Filter MeasureTheory TauCeti
open scoped Topology Matrix.Norms.Frobenius

namespace Matrix

/-- A dimension-independent bound for the spectral-transform error of a constant upper-entry
perturbation. The block size `d + 1` is free and positive, and `c` may be nonreal. -/
theorem norm_resolventTransform_spectralMeasure_add_hermitianOffDiagonal_sub_le
    {n : ℕ} [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : ℂ) (d : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform ((A + hermitianOffDiagonal c n).spectralMeasure
        (hA.add (isHermitian_hermitianOffDiagonal c n)) : Measure ℝ) z -
      resolventTransform (A.spectralMeasure hA : Measure ℝ) z‖ ≤
      2 / ((d + 1) * |z.im|) + Real.sqrt (d + 1) * ‖c‖ / |z.im| ^ 2 := by
  obtain ⟨B, hB, hrank, herr⟩ :=
    exists_isHermitian_rank_le_frobenius_norm_sub_sq_le_hermitianOffDiagonal c n d
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hF : ‖hermitianOffDiagonal c n - B‖ / Real.sqrt n ≤ Real.sqrt (d + 1) * ‖c‖ := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hn)]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ (n : ℝ) * (d + 1) * ‖c‖ ^ 2 := herr
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt hn.le]
        ring
  have hR : (B.rank : ℝ) / ((n : ℝ) * |z.im|) ≤ 2 / ((d + 1) * |z.im|) := by
    have hcast : (B.rank : ℝ) ≤ 2 * ((n / (d + 1) : ℕ) : ℝ) := by exact_mod_cast hrank
    have hdiv : ((n / (d + 1) : ℕ) : ℝ) ≤ (n : ℝ) / (d + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.cast_div_le (m := n) (n := d + 1) :
        ((n / (d + 1) : ℕ) : ℝ) ≤ (n : ℝ) / (d + 1 : ℕ))
    calc
      _ ≤ (2 * ((n : ℝ) / (d + 1))) / ((n : ℝ) * |z.im|) :=
        div_le_div_of_nonneg_right
          (hcast.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))) (by positivity)
      _ = _ := by field_simp
  have h := norm_resolventTransform_spectralMeasure_sub_le_rank_add_frobenius
    (hA.add (isHermitian_hermitianOffDiagonal c n)) hA hB hz
  simp only [add_sub_cancel_left, Fintype.card_fin] at h
  have hF' := mul_le_mul_of_nonneg_left hF (sq_nonneg |z.im|⁻¹)
  simp only [← mul_div_assoc] at hF'
  have heq : |z.im|⁻¹ ^ 2 * (Real.sqrt (d + 1) * ‖c‖) =
      Real.sqrt (d + 1) * ‖c‖ / |z.im| ^ 2 := by ring
  rw [heq] at hF'
  linarith

section Limits

variable {ι : Type*} {l : Filter ι} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {c : ι → ℂ}

/-- Vanishing constant upper entries change every nonreal spectral transform by a quantity
tending to zero. Dimensions are arbitrary positive integers and need not tend to infinity. -/
theorem tendsto_resolventTransform_spectralMeasure_add_hermitianOffDiagonal_sub
    (hc : Tendsto c l (𝓝 0)) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun i ↦ resolventTransform
      ((A i + hermitianOffDiagonal (c i) (n i)).spectralMeasure
        ((hA i).add (isHermitian_hermitianOffDiagonal (c i) (n i))) : Measure ℝ) z -
      resolventTransform ((A i).spectralMeasure (hA i) : Measure ℝ) z) l (𝓝 0) := by
  -- For each tolerance, choose the fixed block size before using convergence of the entries.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : Tendsto (fun d : ℕ ↦ 2 / (((d : ℝ) + 1) * |z.im|)) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div, mul_one_div, mul_zero, zero_div] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).div_const |z.im|
  obtain ⟨d, hd⟩ := (hsmall.eventually (gt_mem_nhds (half_pos hε))).exists
  have hentry : Tendsto (fun i ↦ Real.sqrt (d + 1) * ‖c i‖ / |z.im| ^ 2) l (𝓝 0) := by
    simpa only [norm_zero, mul_zero, zero_div] using
      ((hc.norm.const_mul (Real.sqrt (d + 1))).div_const (|z.im| ^ 2))
  filter_upwards [hentry.eventually (gt_mem_nhds (half_pos hε))] with i hi
  rw [dist_zero_right]
  exact lt_of_le_of_lt
    (norm_resolventTransform_spectralMeasure_add_hermitianOffDiagonal_sub_le (hA i) (c i) d hz)
    (by linarith)

/-- Vanishing constant upper-entry perturbations preserve weak spectral limits in both
directions. No bound on the matrix family or growth condition on its dimensions is needed. -/
theorem tendsto_spectralMeasure_add_hermitianOffDiagonal_iff [l.IsCountablyGenerated]
    (hc : Tendsto c l (𝓝 0)) {μ : ProbabilityMeasure ℝ} :
    Tendsto (fun i ↦ (A i + hermitianOffDiagonal (c i) (n i)).spectralMeasure
      ((hA i).add (isHermitian_hermitianOffDiagonal (c i) (n i)))) l (𝓝 μ) ↔
      Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_resolventTransform,
    ProbabilityMeasure.tendsto_iff_tendsto_resolventTransform]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  apply tendsto_iff_of_dist
  simpa only [dist_eq_norm, norm_zero] using
    (tendsto_resolventTransform_spectralMeasure_add_hermitianOffDiagonal_sub A hA hc hz.ne').norm

end Limits

end Matrix
