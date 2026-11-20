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
At level `n`, allow at most `C * a^n` edges of length at most `r^n`, and normalize
their increments by `c^n`. For `c > 0`, if `a * r^q / c^p < 1`, the supremum of the normalized
`p`th powers has a finite moment, bounded by a geometric series. Consequently one
finite random constant bounds every edge at every level, outside one common null set.

These estimates are the probabilistic input to chaining: they do not assume that the
edges form nets, and do not by themselves assert continuity of a modification. In the
single-edge case (`d = 0`), they also imply almost-sure convergence `X (u n) → X t` along
any sequence approaching `t` at a geometric rate `r ^ n` (`r < 1`).
Neither independence nor probability normalization is needed. The value space may be
an extended pseudometric space, and the estimates also apply to almost-everywhere
modifications of native Kolmogorov processes.

The argument is the weighted edge-sum estimate underlying Kolmogorov--Chentsov
continuity proofs; see Krätschmer--Urusov, *A general Kolmogorov--Chentsov type theorem
on general metric spaces*, arXiv:2107.13837v2, Theorem 1.1. We use Mathlib's
`IsAEKolmogorovProcess`, nonnegative Tonelli theorem and geometric-series formula.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.IsAEKolmogorovProcess

variable {T Ω E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  {p q : ℝ} {M : ℝ≥0}

section EdgeFamily

variable {k : ℕ → ℕ} {s t : (n : ℕ) → Fin (k n) → T}

/-- The supremum over geometrically sized edge families has a geometric moment bound.
The edge count is allowed to be zero, and endpoints and edges may repeat. -/
theorem lintegral_iSup_edist_div_pow_rpow_le (hX : IsAEKolmogorovProcess X P p q M)
    {C a r c : ℝ≥0} (hcard : ∀ n, (k n : ℝ≥0) ≤ C * a ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n) :
    ∫⁻ ω, ⨆ n, ⨆ i, (edist (X (s n i) ω) (X (t n i) ω) /
      (c : ℝ≥0∞) ^ n) ^ p ∂P ≤
        (C : ℝ≥0∞) * M * (1 - (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q /
          (c : ℝ≥0∞) ^ p)⁻¹ := by
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
    _ ≤ ∑' n, (C : ℝ≥0∞) * M *
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
        _ ≤ (M : ℝ≥0∞) * ((k n : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ q) /
            ((c : ℝ≥0∞) ^ n) ^ p := by
          gcongr
          exact (Finset.sum_le_sum fun i _ ↦
            ENNReal.rpow_le_rpow (hedge n i) hX.q_pos.le).trans_eq (by simp)
        _ ≤ (M : ℝ≥0∞) * (((C : ℝ≥0∞) * (a : ℝ≥0∞) ^ n) *
            ((r : ℝ≥0∞) ^ n) ^ q) / ((c : ℝ≥0∞) ^ n) ^ p := by
          gcongr
          exact_mod_cast hcard n
        _ = _ := by
          simp only [ENNReal.pow_rpow_comm, mul_pow, div_eq_mul_inv, ENNReal.inv_pow]
          ring
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- When the geometric ratio is less than one, a single finite constant bounds all
normalized edges, simultaneously at every level. -/
theorem ae_exists_edist_le_mul_pow (hX : IsAEKolmogorovProcess X P p q M)
    {C a r c : ℝ≥0} (hc : c ≠ 0)
    (hcard : ∀ n, (k n : ℝ≥0) ≤ C * a ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n)
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
  have hfinite : (C : ℝ≥0∞) * M *
      (1 - (a : ℝ≥0∞) * (r : ℝ≥0∞) ^ q / (c : ℝ≥0∞) ^ p)⁻¹ ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
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

/-- Entropy growth of dimension `d` permits every edge exponent `γ` with
`d + p * γ < q`, giving a Hölder bound when `γ > 0`.
This is a bound on the supplied edges, not yet on arbitrary pairs
of parameter points. No topology or completeness assumption beyond the native
Kolmogorov condition is required. -/
theorem ae_exists_edist_le_mul_pow_rpow (hX : IsAEKolmogorovProcess X P p q M)
    {C r : ℝ≥0} {d γ : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hcard : ∀ n, (k n : ℝ≥0) ≤ C * (r ^ (-d)) ^ n)
    (hedge : ∀ n i, edist (s n i) (t n i) ≤ (r : ℝ≥0∞) ^ n)
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

end EdgeFamily

/-- Along any sequence `u : ℕ → T` approaching `t` at a geometric rate `r ^ n` (`r < 1`), an
`IsAEKolmogorovProcess` converges almost surely to `X t`. Neither finiteness of `P` nor
completeness or separation of `E` is needed. -/
theorem ae_tendsto_of_edist_le_pow (hX : IsAEKolmogorovProcess X P p q M)
    {u : ℕ → T} {t : T} {r : ℝ≥0} (hr : r < 1)
    (hu : ∀ n, edist (u n) t ≤ (r : ℝ≥0∞) ^ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X t ω)) := by
  have ⟨r', hr'0, hr'1, hu'⟩ :
      ∃ r' : ℝ≥0, 0 < r' ∧ r' < 1 ∧ ∀ n, edist (u n) t ≤ (r' : ℝ≥0∞) ^ n := by
    rcases eq_zero_or_pos r with rfl | hr0
    · exact ⟨2⁻¹, by norm_num, by norm_num, fun n ↦
        (hu n).trans (pow_le_pow_left' (by simp) n)⟩
    · exact ⟨r, hr0, hr, hu⟩
  have hp := hX.p_pos
  have hq := hX.q_pos
  set β : ℝ := q / (2 * p)
  have hβ : 0 < β := by positivity
  have hcard (n : ℕ) : ((1 : ℕ) : ℝ≥0) ≤ 1 * (r' ^ (-(0 : ℝ))) ^ n := by simp
  have hedge (n : ℕ) (_ : Fin 1) : edist (u n) t ≤ (r' : ℝ≥0∞) ^ n := hu' n
  have hβ_lt : 0 + p * β < q := by
    have : p * β = q / 2 := by simp only [β]; field_simp
    linarith
  filter_upwards [hX.ae_exists_edist_le_mul_pow_rpow (C := 1) (r := r') (d := 0) (γ := β)
    (k := fun _ ↦ 1) (s := fun n _ ↦ u n) (t := fun _ _ ↦ t)
    hr'0 hr'1 hcard hedge hβ_lt] with ω ⟨K, hK⟩
  rw [tendsto_iff_edist_tendsto_0]
  have hρ_lt : (r' : ℝ≥0∞) ^ β < 1 :=
    ENNReal.rpow_lt_one (ENNReal.coe_lt_one_iff.mpr hr'1) hβ
  have hlim : Tendsto (fun n : ℕ ↦ (K : ℝ≥0∞) * ((r' : ℝ≥0∞) ^ n) ^ β) atTop (𝓝 0) := by
    simpa only [ENNReal.pow_rpow_comm, mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ_lt)
        (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    fun n ↦ ?_
  simpa using hK n 0

end ProbabilityTheory.IsAEKolmogorovProcess
