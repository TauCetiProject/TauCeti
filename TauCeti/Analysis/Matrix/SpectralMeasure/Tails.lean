/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Spectral tails controlled by trace powers

A normalized even trace controls both the mass outside a bounded interval and the tails of
all lower absolute moments of the empirical spectral measure. In particular, a uniform bound
on normalized traces of order `2 * k` gives uniformly small absolute-moment tails of every
order strictly below `2 * k`, even when matrix dimensions vary. Such estimates justify
truncating unbounded monomials in the moment method; a positive even trace bound also gives
tightness of the spectral measures.

The estimates use eigenvalues with multiplicity, not distinct spectral points. Matrices are
Hermitian over an arbitrary `RCLike` field and have positive dimension.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [RCLike 𝕜]

/-- The absolute moment of order `p` beyond radius `R` is bounded by the normalized even trace
of order `2 * k`, divided by `R ^ (2 * k - p)`. The radius is strictly positive, and equality
of the two orders is allowed. -/
theorem setIntegral_abs_pow_spectralMeasure_le_trace_pow (A : Matrix n n 𝕜)
    (hA : A.IsHermitian) {p k : ℕ} (hp : p ≤ 2 * k) {R : ℝ} (hR : 0 < R) :
    ∫ x in {x : ℝ | R ≤ |x|}, |x| ^ p ∂(A.spectralMeasure hA : Measure ℝ) ≤
      ((Fintype.card n : ℝ)⁻¹ * RCLike.re (A ^ (2 * k)).trace) / R ^ (2 * k - p) := by
  classical
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := isClosed_le continuous_const continuous_abs
    |>.measurableSet
  rw [← integral_indicator hs, integral_spectralMeasure, smul_eq_mul,
    hA.trace_pow_eq_sum_eigenvalues_pow, map_sum]
  simp_rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  calc
    _ ≤ (Fintype.card n : ℝ)⁻¹ *
        ∑ i, (hA.eigenvalues i) ^ (2 * k) / R ^ (2 * k - p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      by_cases hx : R ≤ |hA.eigenvalues i|
      · rw [Set.indicator_of_mem hx]
        apply (le_div_iff₀ (pow_pos hR _)).2
        calc
          _ ≤ |hA.eigenvalues i| ^ p * |hA.eigenvalues i| ^ (2 * k - p) := by
            gcongr
          _ = (hA.eigenvalues i) ^ (2 * k) := by
            rw [pow_mul_pow_sub _ hp, pow_abs_two_mul]
      · rw [Set.indicator_of_notMem hx]
        exact div_nonneg (by rw [pow_mul]; positivity) (by positivity)
    _ = _ := by rw [← Finset.sum_div]; ring

/-- The proportion of eigenvalues of absolute value at least `R` is at most the normalized
trace of `A ^ (2 * k)` divided by `R ^ (2 * k)`. -/
theorem spectralMeasure_real_abs_ge_le_trace_pow (A : Matrix n n 𝕜) (hA : A.IsHermitian)
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    (A.spectralMeasure hA : Measure ℝ).real {x : ℝ | R ≤ |x|} ≤
      ((Fintype.card n : ℝ)⁻¹ * RCLike.re (A ^ (2 * k)).trace) / R ^ (2 * k) := by
  simpa using A.setIntegral_abs_pow_spectralMeasure_le_trace_pow hA (p := 0) (by omega) hR

section Families

variable {ι : Type*} {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
  [∀ i, Nonempty (d i)]

/-- A uniform bound on a normalized even trace gives uniformly small tails of every strictly
lower absolute moment. The family may have varying dimensions. -/
theorem exists_pos_setIntegral_abs_pow_spectralMeasure_lt
    (A : ∀ i, Matrix (d i) (d i) 𝕜) (hA : ∀ i, (A i).IsHermitian)
    {p k : ℕ} (hp : p < 2 * k) {C : ℝ}
    (hC : ∀ i, (Fintype.card (d i) : ℝ)⁻¹ * RCLike.re (A i ^ (2 * k)).trace ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ i,
      ∫ x in {x : ℝ | R ≤ |x|}, |x| ^ p ∂((A i).spectralMeasure (hA i) : Measure ℝ) < ε := by
  have hlim : Tendsto (fun R : ℝ => C / R ^ (2 * k - p)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨R, hR, fun i => ?_⟩
  exact ((A i).setIntegral_abs_pow_spectralMeasure_le_trace_pow (hA i) hp.le hR).trans_lt
    ((div_le_div_of_nonneg_right (hC i) (by positivity)).trans_lt hsmall)

/-- Spectral measures with uniformly bounded normalized traces of a fixed positive even order
form a tight family, with no common-dimension assumption. -/
theorem isTightMeasureSet_range_spectralMeasure_of_trace_pow_le
    (A : ∀ i, Matrix (d i) (d i) 𝕜) (hA : ∀ i, (A i).IsHermitian)
    {k : ℕ} (hk : 0 < k) {C : ℝ}
    (hC : ∀ i, (Fintype.card (d i) : ℝ)⁻¹ * RCLike.re (A i ^ (2 * k)).trace ≤ C) :
    IsTightMeasureSet (Set.range fun i => ((A i).spectralMeasure (hA i) : Measure ℝ)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨R, hR, htail⟩ := exists_pos_setIntegral_abs_pow_spectralMeasure_lt A hA
    (p := 0) (k := k) (by omega) hC (ε := (δ : ℝ)) (by exact_mod_cast hδ)
  refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
  rintro μ ⟨i, rfl⟩
  have hreal : ((A i).spectralMeasure (hA i) : Measure ℝ).real {x : ℝ | R ≤ |x|} ≤ δ := by
    simpa using (htail i).le
  calc
    _ ≤ ((A i).spectralMeasure (hA i) : Measure ℝ) {x : ℝ | R ≤ |x|} := by
      apply measure_mono
      intro x hx
      exact le_of_not_gt fun h => hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
    _ = ENNReal.ofReal
        (((A i).spectralMeasure (hA i) : Measure ℝ).real {x : ℝ | R ≤ |x|}) :=
      (ofReal_measureReal (by finiteness)).symm
    _ ≤ δ := by simpa using ENNReal.ofReal_le_ofReal hreal
    _ ≤ ε := hδε.le

end Families

end Matrix
