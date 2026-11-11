/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import TauCeti.Probability.Moments.SampleMean

/-!
# Second moments of martingale increment sums

Square-integrable predictably weighted increments of a real martingale are orthogonal.
Their finite sums therefore satisfy a discrete isometry. The unweighted case identifies
expected quadratic sums with the second moment of the total increment. These identities
are used to control quadratic sums without constructing a stochastic integral. The algebraic
second-moment expansion reuses
`TauCeti.integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero`.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Chapter IV, §1.
-/

public section

open MeasureTheory ProbabilityTheory Finset

namespace MeasureTheory.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration P ℱ] {M : ι → Ω → ℝ}

/-- A predictable height times a later martingale increment has mean zero whenever the
product is integrable. No separate moment assumption on the height is needed. -/
theorem integral_mul_sub_eq_zero (hM : Martingale M ℱ P) {s t : ι} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hint : Integrable (ξ * (M t - M s)) P) :
    ∫ ω, ξ ω * (M t ω - M s ω) ∂P = 0 := by
  have hzero : P[M t - M s | ℱ s] =ᵐ[P] 0 := by
    refine (condExp_sub (hM.integrable t) (hM.integrable s) _).trans ?_
    simpa only [sub_self] using
      (hM.condExp_ae_eq hst).sub (hM.condExp_ae_eq (i := s) le_rfl)
  have hpull := condExp_mul_of_stronglyMeasurable_left hξ hint
    ((hM.integrable t).sub (hM.integrable s))
  have heq : P[ξ * (M t - M s) | ℱ s] =ᵐ[P] 0 := by
    filter_upwards [hpull, hzero] with ω hp hz
    simpa [hz] using hp
  simpa only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, integral_zero] using
    (integral_condExp (ℱ.le s) (f := ξ * (M t - M s))).symm.trans (integral_congr_ae heq)

variable {τ : ℕ → ι} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- **Discrete martingale isometry.** Predictably weighted increments on a nondecreasing
finite grid are orthogonal. Square integrability of the weighted increments suffices;
heights need not be bounded. -/
theorem integral_sq_sum_mul_sub (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hZ : ∀ i < n, MemLp (fun ω ↦ a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) 2 P) :
    ∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P =
      ∑ i ∈ range n, ∫ ω, (a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P := by
  let Z (i : ℕ) (ω : Ω) := a i ω * (M (τ (i + 1)) ω - M (τ i) ω)
  have hoff (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i < j) :
      ∫ ω, Z i ω * Z j ω ∂P = 0 := by
    have hle (k : ℕ) (hk : k ≤ j) : τ k ≤ τ j :=
      hτ (by simpa using hk.trans hj.le) (by simpa using hj.le) hk
    have hm : StronglyMeasurable[ℱ (τ j)] (fun ω ↦ Z i ω * a j ω) :=
      (((ha i hi).mono (ℱ.mono (hle i hij.le))).mul
        (((hM.stronglyAdapted (τ (i + 1))).mono (ℱ.mono (hle _ hij))).sub
          ((hM.stronglyAdapted (τ i)).mono (ℱ.mono (hle _ hij.le))))).mul (ha j hj)
    have hint := (hZ i hi).integrable_mul (hZ j hj)
    have hstep : τ j ≤ τ (j + 1) :=
      hτ (by simpa using hj.le) (by simpa using hj) (Nat.le_succ j)
    simpa only [Z, mul_assoc] using hM.integral_mul_sub_eq_zero hstep hm
      (by simpa only [Pi.mul_def, Pi.sub_def, Z, mul_assoc] using hint)
  have hpair (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
      ∫ ω, Z i ω * Z j ω ∂P = 0 := by
    rcases hij.lt_or_gt with hij | hij
    · exact hoff i j hi hj hij
    · simpa only [mul_comm] using hoff j i hj hi hij
  simpa only [Real.norm_eq_abs, sq_abs] using
    TauCeti.integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
      (X := Z) (s := range n)
      (fun i hi j hj ↦ by
        simpa only [Real.inner_apply, Pi.mul_def, Z] using
          (hZ i (mem_range.mp hi)).integrable_mul (hZ j (mem_range.mp hj)))
      (fun i hi j hj hij ↦ by
        simpa only [Real.inner_apply] using hpair i j (mem_range.mp hi) (mem_range.mp hj) hij)

/-- The expected sum of squared martingale increments equals the second moment of the
total increment. Empty grids and repeated dates are allowed. -/
theorem integral_sum_sq_sub (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : ∀ i ≤ n, MemLp (M (τ i)) 2 P) :
    ∫ ω, ∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2 ∂P =
      ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  have hΔ (i : ℕ) (hi : i < n) := (h₂ (i + 1) hi).sub (h₂ i hi.le)
  rw [integral_finsetSum _ fun i hi ↦ by
    simpa only [Pi.sub_def] using (hΔ i (mem_range.mp hi)).integrable_sq]
  have h := hM.integral_sq_sum_mul_sub hτ
    (a := fun _ _ ↦ 1) (fun _ _ ↦ stronglyMeasurable_const)
    (fun i hi ↦ by simpa only [Pi.sub_def, one_mul] using hΔ i hi)
  simp only [one_mul] at h
  have htel (ω : Ω) : ∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) =
      M (τ n) ω - M (τ 0) ω := sum_range_sub (fun i ↦ M (τ i) ω) n
  simpa only [htel] using h.symm

omit [SigmaFiniteFiltration P ℱ] in
/-- Quadratic sums of a bounded martingale have a second-moment bound independent of the
number of grid cells. In particular these sums are uniformly integrable on a finite measure
space. The numerical constant is not asserted to be sharp. -/
theorem integral_sq_sum_sq_sub_le [IsFiniteMeasure P] (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ i ≤ n, |M (τ i) ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2) ^ 2 ∂P ≤
      40 * C ^ 4 * P.real Set.univ := by
  -- First establish the finite moments needed for the discrete isometry; no path
  -- regularity or bound on the variation is used in this finite-grid argument.
  let Δ (i : ℕ) (ω : Ω) := M (τ (i + 1)) ω - M (τ i) ω
  let J (ω : Ω) := ∑ i ∈ range n, M (τ i) ω * Δ i ω
  let Q (ω : Ω) := ∑ i ∈ range n, Δ i ω ^ 2
  have h₂ (i : ℕ) (hi : i ≤ n) : MemLp (M (τ i)) 2 P :=
    MemLp.of_bound ((hM.stronglyMeasurable _).mono (ℱ.le _)).aestronglyMeasurable C
      (hb.mono fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω i hi)
  have hΔ (i : ℕ) (hi : i < n) : MemLp (Δ i) 2 P := by
    simpa only [Δ, Pi.sub_def] using (h₂ (i + 1) hi).sub (h₂ i hi.le)
  have hZ (i : ℕ) (hi : i < n) : MemLp (fun ω ↦ M (τ i) ω * Δ i ω) 2 P := by
    apply MemLp.of_bound (((h₂ i hi.le).aestronglyMeasurable).mul
      (hΔ i hi).aestronglyMeasurable) (C * (2 * C))
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    exact mul_le_mul (hω i hi.le)
      (by dsimp [Δ]; nlinarith [abs_sub (M (τ (i + 1)) ω) (M (τ i) ω),
        hω (i + 1) hi, hω i hi.le])
      (abs_nonneg _) hC
  have hJi : Integrable (fun ω ↦ J ω ^ 2) P :=
    (memLp_finsetSum _ fun i hi ↦ hZ i (mem_range.mp hi)).integrable_sq
  have henergy := hM.integral_sum_sq_sub hτ h₂
  -- Bound the transform by C² times the total increment's second moment.
  have hJ : ∫ ω, J ω ^ 2 ∂P ≤ 4 * C ^ 4 * P.real Set.univ := by
    rw [hM.integral_sq_sum_mul_sub hτ (fun _ _ ↦ hM.stronglyMeasurable _) hZ]
    calc
      _ ≤ ∑ i ∈ range n, C ^ 2 * ∫ ω, Δ i ω ^ 2 ∂P := by
        apply sum_le_sum
        intro i hi
        rw [← integral_const_mul]
        apply integral_mono_ae (hZ i (mem_range.mp hi)).integrable_sq
          ((hΔ i (mem_range.mp hi)).integrable_sq.const_mul _)
        filter_upwards [hb] with ω hω
        rw [mul_pow]
        have hs := (sq_le_sq₀ (abs_nonneg _) hC).2 (hω i (mem_range.mp hi).le)
        rw [sq_abs] at hs
        exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
        rw [← mul_sum, ← integral_finsetSum _ fun i hi ↦ (hΔ i (mem_range.mp hi)).integrable_sq]
        exact congrArg (C ^ 2 * ·) henergy
      _ ≤ C ^ 2 * (4 * C ^ 2 * P.real Set.univ) := by
        gcongr
        have hi := integral_mono_ae
          ((h₂ n le_rfl).sub (h₂ 0 (Nat.zero_le n))).integrable_sq
          (integrable_const (4 * C ^ 2))
        simp only [integral_const, smul_eq_mul] at hi
        rw [mul_comm (4 * C ^ 2)]
        apply hi
        filter_upwards [hb] with ω hω
        simp only [Pi.sub_apply]
        have h := (abs_sub (M (τ n) ω) (M (τ 0) ω)).trans
          (add_le_add (hω n le_rfl) (hω 0 (Nat.zero_le n)))
        have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C + C)).2 h
        rw [sq_abs] at hs
        nlinarith
      _ = _ := by ring
  -- The telescoping square identity separates Q into a bounded endpoint term and a
  -- martingale transform. Its isometry gives a bound independent of the partition.
  have hid (ω : Ω) : Q ω = M (τ n) ω ^ 2 - M (τ 0) ω ^ 2 - 2 * J ω := by
    have ht := sum_range_sub (fun i ↦ M (τ i) ω ^ 2) n
    dsimp [Q, J, Δ]
    rw [← ht, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hpoint : ∀ᵐ ω ∂P, Q ω ^ 2 ≤ 8 * C ^ 4 + 8 * J ω ^ 2 := by
    filter_upwards [hb] with ω hω
    have hn := (sq_le_sq₀ (abs_nonneg _) hC).2 (hω n le_rfl)
    have h₀ := (sq_le_sq₀ (abs_nonneg _) hC).2 (hω 0 (Nat.zero_le n))
    rw [sq_abs] at hn h₀
    rw [hid]
    nlinarith [sq_nonneg (M (τ n) ω ^ 2 - M (τ 0) ω ^ 2 + 2 * J ω),
      sq_nonneg (M (τ n) ω ^ 2 - M (τ 0) ω ^ 2)]
  calc
    _ ≤ ∫ ω, 8 * C ^ 4 + 8 * J ω ^ 2 ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
        ((integrable_const _).add (hJi.const_mul _)) hpoint
    _ = 8 * C ^ 4 * P.real Set.univ + 8 * ∫ ω, J ω ^ 2 ∂P := by
      rw [integral_add (integrable_const _) (hJi.const_mul _), integral_const,
        integral_const_mul, smul_eq_mul]
      ring
    _ ≤ 40 * C ^ 4 * P.real Set.univ := by linarith

end MeasureTheory.Martingale
