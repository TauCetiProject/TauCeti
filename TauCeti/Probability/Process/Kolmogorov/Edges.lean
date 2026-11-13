/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Geometric edge estimates for Kolmogorov processes

A moment bound on increments controls all edges in a sequence of finite nets at once.
At level `n`, allow at most `C * a^n` edges of length at most `D * r^n`, and normalize
their increments by `c^n`. For `c > 0`, if `a * r^q / c^p < 1`, the supremum of the normalized
`p`th powers has a finite moment, bounded by a geometric series. Consequently one
finite random constant bounds every edge at every level, outside one common null set.

These estimates are the probabilistic input to chaining: they do not assume that the
edges form nets, and do not by themselves assert continuity of a modification.
Neither independence nor probability normalization is needed. The value space may be
an extended pseudometric space, and the estimates also apply to almost-everywhere
modifications of native Kolmogorov processes.

The argument is the weighted edge-sum estimate underlying Kolmogorov--Chentsov
continuity proofs; see Krätschmer--Urusov, *A general Kolmogorov--Chentsov type theorem
on general metric spaces*, arXiv:2107.13837v2, Theorem 1.1. We use Mathlib's
`IsAEKolmogorovProcess`, nonnegative Tonelli theorem and geometric-series formula.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory.IsAEKolmogorovProcess

variable {T Ω E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  {p q : ℝ} {M : ℝ≥0} {ι : ℕ → Type*} [∀ n, Finite (ι n)]
  {s t : (n : ℕ) → ι n → T}

/-- The supremum over geometrically sized edge families has a geometric moment bound.
The edge count is allowed to be zero, and endpoints and edges may repeat. -/
theorem lintegral_iSup_edist_div_pow_rpow_le (hX : IsAEKolmogorovProcess X P p q M)
    {C D a r c : ℝ≥0} (hcard : ∀ n, (Nat.card (ι n) : ℝ≥0) ≤ C * a ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (D : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) :
    ∫⁻ ω, ⨆ n, ⨆ i, (edist (X (s n i) ω) (X (t n i) ω) /
      (c : ℝ≥0∞) ^ n) ^ p ∂P ≤
        (C : ℝ≥0∞) * M * (D : ℝ≥0∞) ^ q *
          (1 - (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p)⁻¹ := by
  classical
  let : ∀ n, Fintype (ι n) := fun n ↦ Fintype.ofFinite (ι n)
  -- Dominate the maximum by the total edge energy and apply nonnegative Tonelli.
  calc
    _ ≤ ∫⁻ ω, ∑' n, ∑ i, (edist (X (s n i) ω) (X (t n i) ω) /
          (c : ℝ≥0∞) ^ n) ^ p ∂P := by
      apply lintegral_mono
      intro ω
      refine iSup_le fun n ↦ iSup_le fun i ↦ ?_
      exact (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i)).trans
        (le_tsum (fun n ↦ ∑ i, (edist (X (s n i) ω) (X (t n i) ω) /
          (c : ℝ≥0∞) ^ n) ^ p) n)
    _ = ∑' n, ∫⁻ ω, ∑ i, (edist (X (s n i) ω) (X (t n i) ω) /
          (c : ℝ≥0∞) ^ n) ^ p ∂P := by
      apply lintegral_tsum
      intro n
      exact Finset.aemeasurable_fun_sum _ fun i _ ↦
        (hX.aemeasurable_edist.div_const _).pow_const p
    _ ≤ ∑' n, (C : ℝ≥0∞) * M * (D : ℝ≥0∞) ^ q *
          ((a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p) ^ n := by
      -- At each level, combine the increment moment, edge length and edge count bounds.
      apply tsum_le_tsum
      intro n
      calc
        _ ≤ (M : ℝ≥0∞) * (∑ i, edist (s n i) (t n i) ^ q) /
            ((c : ℝ≥0∞) ^ n) ^ p := by
          simp_rw [ENNReal.div_rpow_of_nonneg _ _ hX.p_pos.le, div_eq_mul_inv]
          rw [lintegral_finsetSum' _ (fun i _ ↦
            (hX.aemeasurable_edist.pow_const p).mul_const _)]
          simp_rw [lintegral_mul_const'' _ (hX.aemeasurable_edist.pow_const p)]
          rw [← Finset.sum_mul, Finset.mul_sum]
          gcongr
          exact hX.kolmogorovCondition _ _
        _ ≤ (M : ℝ≥0∞) * ((Nat.card (ι n) : ℝ≥0∞) *
            ((D : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) ^ q) /
            ((c : ℝ≥0∞) ^ n) ^ p := by
          gcongr
          exact (Finset.sum_le_sum fun i _ ↦
            ENNReal.rpow_le_rpow (hedge n i) hX.q_pos.le).trans_eq (by simp)
        _ ≤ (M : ℝ≥0∞) * (((C : ℝ≥0∞) * (a : ℝ≥0∞) ^ n) *
            ((D : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) ^ q) / ((c : ℝ≥0∞) ^ n) ^ p := by
          gcongr
          exact_mod_cast hcard n
        _ = _ := by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ hX.q_pos.le,
            ENNReal.pow_rpow_comm, mul_pow, div_eq_mul_inv, ENNReal.inv_pow]
          ring
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- For `c ≠ 0` and geometric ratio `a * r ^ q / c ^ p < 1`, almost surely a single
finite random constant bounds all normalized edge increments, simultaneously at every level.
The constant may depend on the sample. -/
theorem ae_exists_edist_le_mul_pow (hX : IsAEKolmogorovProcess X P p q M)
    {C D a r c : ℝ≥0} (hc : c ≠ 0)
    (hcard : ∀ n, (Nat.card (ι n) : ℝ≥0) ≤ C * a ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (D : ℝ≥0∞) * (r : ℝ≥0∞) ^ n)
    (hratio : a * r ^ q / c ^ p < 1) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n i,
      edist (X (s n i) ω) (X (t n i) ω) ≤ (K : ℝ≥0∞) * (c : ℝ≥0∞) ^ n := by
  let Z : Ω → ℝ≥0∞ := fun ω ↦ ⨆ n, ⨆ i,
    (edist (X (s n i) ω) (X (t n i) ω) / (c : ℝ≥0∞) ^ n) ^ p
  have hZ : AEMeasurable Z P := AEMeasurable.iSup fun n ↦ AEMeasurable.iSup fun i ↦
    (hX.aemeasurable_edist.div_const _).pow_const p
  have hratio' : (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p < 1 := by
    rw [← ENNReal.coe_rpow_of_nonneg _ hX.q_pos.le,
      ← ENNReal.coe_rpow_of_nonneg _ hX.p_pos.le, ← ENNReal.coe_mul,
      ← ENNReal.coe_div (NNReal.rpow_pos (pos_iff_ne_zero.mpr hc)).ne']
    exact_mod_cast hratio
  have hfinite : (C : ℝ≥0∞) * M * (D : ℝ≥0∞) ^ q *
      (1 - (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p)⁻¹ ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg hX.q_pos.le ENNReal.coe_ne_top))
      (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hratio')))
  have hZfinite : ∫⁻ ω, Z ω ∂P ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (hX.lintegral_iSup_edist_div_pow_rpow_le hcard hedge)
  filter_upwards [ae_lt_top' hZ hZfinite] with ω hω
  refine ⟨(Z ω).toNNReal ^ p⁻¹, fun n i ↦ ?_⟩
  have hi : (edist (X (s n i) ω) (X (t n i) ω) /
      (c : ℝ≥0∞) ^ n) ^ p ≤ Z ω := le_iSup_of_le n (le_iSup_of_le i le_rfl)
  have hroot := (ENNReal.le_rpow_inv_iff hX.p_pos).mpr hi
  rw [← ENNReal.coe_toNNReal hω.ne, ← ENNReal.coe_rpow_of_nonneg _
    (inv_pos.mpr hX.p_pos).le] at hroot
  exact (ENNReal.div_le_iff (pow_ne_zero _ (by exact_mod_cast hc)) (by simp)).mp hroot

/-- With entropy growth of dimension `d` and `d + p * γ < q`, almost surely a finite
random constant `K`, which may depend on the sample, bounds increments on the supplied edges
by `K * (r ^ n) ^ γ`. This scale decays geometrically when `γ > 0`, since `0 < r < 1`.
This is a bound in the upper length scale `r ^ n`, not a Hölder bound in the actual edge
lengths or a bound on arbitrary pairs of parameter points. No topology or completeness
assumption beyond the native Kolmogorov condition is required. -/
theorem ae_exists_edist_le_mul_pow_rpow (hX : IsAEKolmogorovProcess X P p q M)
    {C D r : ℝ≥0} {d γ : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hcard : ∀ n, (Nat.card (ι n) : ℝ≥0) ≤ C * (r ^ (-d)) ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (D : ℝ≥0∞) * (r : ℝ≥0∞) ^ n)
    (hγ : d + p * γ < q) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, ∀ n i,
      edist (X (s n i) ω) (X (t n i) ω) ≤
        (K : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ γ := by
  have hratio : r ^ (-d) * r ^ q / (r ^ γ) ^ p < 1 := by
    rw [← NNReal.rpow_mul, ← NNReal.rpow_add hr.ne', ← NNReal.rpow_sub hr.ne']
    exact NNReal.rpow_lt_one hr₁ (by linarith)
  filter_upwards [hX.ae_exists_edist_le_mul_pow (NNReal.rpow_pos hr).ne'
    hcard hedge hratio] with ω hω
  obtain ⟨K, hK⟩ := hω
  refine ⟨K, fun n i ↦ ?_⟩
  simpa only [ENNReal.coe_rpow_of_ne_zero hr.ne', ENNReal.pow_rpow_comm] using hK n i

end ProbabilityTheory.IsAEKolmogorovProcess
