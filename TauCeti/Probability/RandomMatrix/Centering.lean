/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Analysis.Matrix.SpectralMeasure.ConstantOffDiagonal

/-!
# Removing a complex Wigner mean

Subtracting a fixed complex number from every upper entry of an infinite Wigner array preserves
weak convergence of its empirical spectral measures, pointwise and almost surely. In particular,
one may subtract the common mean before proving a semicircle law. The real diagonal is kept,
and no assumption is made on its moments or its dependence on the upper entries.

The difference is the Hermitian matrix with upper entries `c / √n`. Its imaginary part generally
has large rank and operator norm, so rank-one centering alone does not suffice. The block
approximation of `TauCeti.hermitianOffDiagonal` gives vanishing spectral-transform error for the
whole complex shift. This argument is deterministic and places no independence, distribution,
or moment assumptions on the arrays.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), proof of Theorem 2.1.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

variable {Ω : Type*}

/-- Centering only the upper entries changes a Wigner matrix by the constant-upper-entry
Hermitian matrix with upper entry `c / √n`. The identity also holds at dimension zero. -/
theorem wignerMatrix_eq_center_add_hermitianOffDiagonal
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (c : ℂ) (n : ℕ) (ω : Ω) :
    wignerMatrix ξ η n ω = wignerMatrix (fun ij ω ↦ ξ ij ω - c) η n ω +
      hermitianOffDiagonal ((Real.sqrt n)⁻¹ • c) n := by
  ext i j
  rw [Matrix.add_apply]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h,
      hermitianOffDiagonal_apply_of_lt _ (Fin.mk_lt_mk.mpr h), Complex.real_smul]
    push_cast
    ring
  · obtain rfl := Fin.ext h
    simp
  · simp only [wignerMatrix_apply_of_gt _ _ _ h,
      hermitianOffDiagonal_apply_of_gt _ (Fin.mk_lt_mk.mpr h), star_sub,
      star_smul, star_trivial]
    simp only [Complex.real_smul]
    push_cast
    ring

open scoped Matrix.Norms.L2Operator in
/-- Subtracting a common constant from the upper entries changes the normalized Wigner
matrix by at most `√n * ‖c‖` in operator norm. -/
theorem l2_opNorm_wignerMatrix_sub_center_le
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (c : ℂ) (n : ℕ) (ω : Ω) :
    ‖wignerMatrix ξ η n ω - wignerMatrix (fun ij ω' ↦ ξ ij ω' - c) η n ω‖ ≤
      Real.sqrt n * ‖c‖ := by
  rw [wignerMatrix_eq_center_add_hermitianOffDiagonal ξ η c n ω, add_sub_cancel_left]
  refine (l2_opNorm_hermitianOffDiagonal_le _ _).trans_eq ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc]
  congr 1
  exact (mul_inv_eq_iff_eq_mul₀ hs.ne').2 (by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)])

section Limits

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {n : ι → ℕ} [∀ i, NeZero (n i)]
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)

/-- Subtracting a fixed complex upper-entry mean preserves the weak spectral limit of the
Wigner corners, at each sample point. The sizes may follow any diverging dimension sequence. -/
theorem tendsto_spectralMeasure_wignerMatrix_center_iff
    (hn : Tendsto n l atTop) (c : ℂ) (ω : Ω) {μ : ProbabilityMeasure ℝ} :
    Tendsto (fun i ↦ (wignerMatrix ξ η (n i) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n i))) l (𝓝 μ) ↔
      Tendsto (fun i ↦ (wignerMatrix (fun ij ω ↦ ξ ij ω - c) η (n i) ω).spectralMeasure
        (wignerMatrix_isHermitian _ η ω (n i))) l (𝓝 μ) := by
  have hscale : Tendsto (fun i ↦ (Real.sqrt (n i))⁻¹ • c) l (𝓝 (0 : ℂ)) := by
    have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
    simpa using (tendsto_inv_atTop_zero.comp hs).smul_const c
  simpa only [← wignerMatrix_eq_center_add_hermitianOffDiagonal] using
    Matrix.tendsto_spectralMeasure_add_hermitianOffDiagonal_iff
      (fun i ↦ wignerMatrix (fun ij ω ↦ ξ ij ω - c) η (n i) ω)
      (fun i ↦ wignerMatrix_isHermitian _ η ω (n i)) hscale (μ := μ)

end Limits

/-- A complex common mean can be removed in an almost-sure Wigner spectral limit, without
any assumptions on the diagonal or on the coupling of the matrix sizes. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_center_iff [MeasurableSpace Ω]
    (P : Measure Ω) (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (c : ℂ)
    (μ : ProbabilityMeasure ℝ) :
    (∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1))) atTop (𝓝 μ)) ↔
      ∀ᵐ ω ∂P, Tendsto (fun n ↦
        (wignerMatrix (fun ij ω ↦ ξ ij ω - c) η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian _ η ω (n + 1))) atTop (𝓝 μ) := by
  exact eventually_congr (Eventually.of_forall fun ω ↦
    tendsto_spectralMeasure_wignerMatrix_center_iff ξ η (tendsto_add_atTop_nat 1) c ω)

end TauCeti
