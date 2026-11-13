/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Second moments of martingale increment sums

`MeasureTheory.Martingale.integral_sq_sum_mul_sub` is the discrete second-moment isometry
for predictably weighted increments of a real martingale. Its unweighted form,
`MeasureTheory.Martingale.integral_sum_sq_sub`, identifies expected quadratic sums with the
second moment of the total increment. Bounded predictable heights give the transform estimate
`MeasureTheory.Martingale.integral_sq_sum_mul_sub_le`.

On a finite measure space, `MeasureTheory.Martingale.integral_sq_sum_sq_sub_le` bounds the
second moment of quadratic sums independently of the grid, using only a deterministic bound
on the terminal martingale value. This estimate is used downstream to establish uniform
integrability of grid families, without constructing a stochastic integral. The algebraic
second-moment expansion reuses `TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero`.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Chapter IV, §1.
-/

public section

open MeasureTheory Finset

namespace MeasureTheory.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration P ℱ] {M : ι → Ω → ℝ}

variable {τ : ℕ → ι} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- **Discrete martingale isometry.** On a nondecreasing finite grid, the second moment of
the sum of square-integrable predictably weighted martingale increments equals the sum of
their second moments. Heights need not be bounded. -/
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
  exact TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero
    (fun i hi ↦ hZ i (mem_range.mp hi))
    (fun i hi j hj hij ↦ hpair i j (mem_range.mp hi) (mem_range.mp hj) hij)

/-- The expected sum of squared martingale increments equals the second moment of the
total increment. Empty grids and repeated dates are allowed. -/
theorem integral_sum_sq_sub (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : MemLp (M (τ n)) 2 P) :
    ∫ ω, ∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2 ∂P =
      ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  have h₂ (i : ℕ) (hi : i ≤ n) : MemLp (M (τ i)) 2 P :=
    (h₂.condExp (m := ℱ (τ i)) (by norm_num)).ae_eq
      (hM.condExp_ae_eq (hτ hi (by simp) hi))
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

/-- Bounded predictable heights bound the second moment of a martingale transform by
`C²` times the second moment of the total increment. Only the terminal martingale value
needs to be square-integrable. -/
theorem integral_sq_sum_mul_sub_le (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : MemLp (M (τ n)) 2 P)
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) {C : ℝ}
    (hb : ∀ i < n, ∀ᵐ ω ∂P, |a i ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P ≤
      C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  have h₂' (i : ℕ) (hi : i ≤ n) : MemLp (M (τ i)) 2 P :=
    (h₂.condExp (m := ℱ (τ i)) (by norm_num)).ae_eq
      (hM.condExp_ae_eq (hτ hi (by simp) hi))
  let Δ (i : ℕ) (ω : Ω) := M (τ (i + 1)) ω - M (τ i) ω
  have hΔ (i : ℕ) (hi : i < n) : MemLp (Δ i) 2 P :=
    (h₂' (i + 1) hi).sub (h₂' i hi.le)
  have hZ (i : ℕ) (hi : i < n) : MemLp (fun ω ↦ a i ω * Δ i ω) 2 P := by
    apply ((hΔ i hi).const_mul C).of_le
      (((ha i hi).mono (ℱ.le _)).aestronglyMeasurable.mul (hΔ i hi).aestronglyMeasurable)
    filter_upwards [hb i hi] with ω hω
    simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
      mul_le_mul_of_nonneg_right (hω.trans (le_abs_self C)) (abs_nonneg (Δ i ω))
  rw [hM.integral_sq_sum_mul_sub hτ ha hZ]
  calc
    _ ≤ ∑ i ∈ range n, C ^ 2 * ∫ ω, Δ i ω ^ 2 ∂P := by
      apply sum_le_sum
      intro i hi
      rw [← integral_const_mul]
      apply integral_mono_ae (hZ i (mem_range.mp hi)).integrable_sq
        ((hΔ i (mem_range.mp hi)).integrable_sq.const_mul _)
      filter_upwards [hb i (mem_range.mp hi)] with ω hω
      rw [mul_pow]
      have hs := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hω)).2 hω
      rw [sq_abs] at hs
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by
      rw [← mul_sum, ← integral_finsetSum _ fun i hi ↦ (hΔ i (mem_range.mp hi)).integrable_sq]
      exact congrArg (C ^ 2 * ·) (hM.integral_sum_sq_sub hτ h₂)

omit [SigmaFiniteFiltration P ℱ] in
/-- On a finite measure space, the quadratic sum of a martingale whose terminal grid value
is bounded by `C` has second moment at most `40 * C ^ 4 * P.real Set.univ`, independently of
the grid. Families sharing a terminal bound can use this estimate downstream to establish
uniform integrability. The numerical constant is not asserted to be sharp. -/
theorem integral_sq_sum_sq_sub_le [IsFiniteMeasure P] (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, |M (τ n) ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2) ^ 2 ∂P ≤
      40 * C ^ 4 * P.real Set.univ := by
  by_cases hP : P = 0
  · simp [hP]
  have : NeZero P := ⟨hP⟩
  have hC : 0 ≤ C := (abs_nonneg _).trans hb.exists.choose_spec
  have hb : ∀ᵐ ω ∂P, ∀ i ≤ n, |M (τ i) ω| ≤ C := by
    apply ae_all_iff.2
    intro i
    by_cases hi : i ≤ n
    · filter_upwards [hM.ae_norm_le_of_le (hτ hi (by simp) hi)
        (by simpa only [Real.norm_eq_abs] using hb)] with ω hω
      simpa only [Real.norm_eq_abs] using fun _ ↦ hω
    · exact Filter.Eventually.of_forall fun _ ↦ fun h ↦ (hi h).elim
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
  -- Bound the transform by C² times the total increment's second moment.
  have hJ : ∫ ω, J ω ^ 2 ∂P ≤ 4 * C ^ 4 * P.real Set.univ := by
    calc
      _ ≤ C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P :=
        hM.integral_sq_sum_mul_sub_le hτ (h₂ n le_rfl)
          (fun _ _ ↦ hM.stronglyMeasurable _)
          (fun i hi ↦ hb.mono fun ω hω ↦ hω i hi.le)
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
