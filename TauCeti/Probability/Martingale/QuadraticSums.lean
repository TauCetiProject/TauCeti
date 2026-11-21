/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Second moments of martingale increment sums

`MeasureTheory.Martingale.integral_sq_sum_mul_sub_of_pairwise_disjoint` is the discrete
second-moment isometry for predictably weighted increments on chronologically disjoint
intervals. Its grid specialization is `MeasureTheory.Martingale.integral_sq_sum_mul_sub`.
The unweighted form, `MeasureTheory.Martingale.integral_sum_sq_sub`, identifies expected
quadratic sums with the second moment of the total increment. Bounded predictable heights
give the transform estimate `MeasureTheory.Martingale.integral_sq_sum_mul_sub_le`.

`MeasureTheory.Martingale.integral_sq_sum_sq_sub_le` bounds the second moment of quadratic
sums by `10 * C²` times the second moment of the total increment, independently of the grid,
using only a deterministic bound `C` on that increment, not on the initial value. On a finite
measure space, `MeasureTheory.Martingale.integral_sq_sum_sq_sub_le_of_isFiniteMeasure`
bounds it by `10 * C⁴` times the total mass.
This estimate establishes uniform integrability of grid families, without constructing a stochastic
integral. The algebraic second-moment expansion reuses
`TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero`.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Chapter IV, §1.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace MeasureTheory.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ι mΩ} {M : ι → Ω → ℝ}

/-- **Discrete martingale isometry.** The second moment of a finite sum of square-integrable
predictably weighted martingale increments on chronologically disjoint intervals equals
the sum of their second moments. Heights need only be a.e. strongly measurable. -/
theorem integral_sq_sum_mul_sub_of_pairwise_disjoint
    (hM : Martingale M ℱ P)
    {κ : Type*} (I : Finset κ) {s t : κ → ι} {a : κ → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : (I : Set κ).Pairwise fun i j ↦ t i ≤ s j ∨ t j ≤ s i)
    (ha : ∀ i ∈ I, AEStronglyMeasurable[ℱ (s i)] (a i) P)
    (hZ : ∀ i ∈ I, MemLp (fun ω ↦ a i ω * (M (t i) ω - M (s i) ω)) 2 P) :
    ∫ ω, (∑ i ∈ I, a i ω * (M (t i) ω - M (s i) ω)) ^ 2 ∂P =
      ∑ i ∈ I, ∫ ω, (a i ω * (M (t i) ω - M (s i) ω)) ^ 2 ∂P := by
  let Z (i : κ) (ω : Ω) := a i ω * (M (t i) ω - M (s i) ω)
  have hoff (i j : κ) (hi : i ∈ I) (hj : j ∈ I) (hij : t i ≤ s j) :
      ∫ ω, Z i ω * Z j ω ∂P = 0 := by
    have hm : AEStronglyMeasurable[ℱ (s j)] (fun ω ↦ Z i ω * a j ω) P :=
      (((ha i hi).mono (ℱ.mono ((hst i hi).trans hij))).mul
        ((((hM.stronglyMeasurable (t i)).mono (ℱ.mono hij)).sub
          ((hM.stronglyMeasurable (s i)).mono
            (ℱ.mono ((hst i hi).trans hij)))).aestronglyMeasurable)).mul (ha j hj)
    by_cases hσ : SigmaFinite (P.trim (ℱ.le (s j)))
    · simpa only [Z, mul_assoc] using hM.integral_mul_sub_eq_zero (hst j hj) hm
        (by simpa only [Pi.mul_def, Pi.sub_def, Z, mul_assoc] using
          (hZ i hi).integrable_mul (hZ j hj))
    · have ht : ¬SigmaFinite (P.trim (ℱ.le (t i))) := fun _ ↦
        hσ (sigmaFiniteTrim_mono (ℱ.le (s j)) (ℱ.mono hij))
      have hs : ¬SigmaFinite (P.trim (ℱ.le (s i))) := fun _ ↦
        ht (sigmaFiniteTrim_mono (ℱ.le (t i)) (ℱ.mono (hst i hi)))
      have hti := hM.condExp_ae_eq (i := t i) le_rfl
      have hsi := hM.condExp_ae_eq (i := s i) le_rfl
      simp only [condExp_of_not_sigmaFinite _ ht, condExp_of_not_sigmaFinite _ hs] at hti hsi
      apply integral_eq_zero_of_ae
      filter_upwards [hti, hsi] with ω htω hsω
      simp only [Pi.zero_apply] at htω hsω
      simp [Z, ← htω, ← hsω]
  apply TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero hZ
  intro i hi j hj hij
  rcases hdisj hi hj hij with h | h
  · exact hoff i j hi hj h
  · simpa only [mul_comm] using hoff j i hj hi h

variable {τ : ℕ → ι} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- On a nondecreasing finite grid, the second moment of the sum of square-integrable
predictably weighted martingale increments equals the sum of their second moments.
Heights need not be bounded. -/
theorem integral_sq_sum_mul_sub (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, AEStronglyMeasurable[ℱ (τ i)] (a i) P)
    (hZ : ∀ i < n, MemLp (fun ω ↦ a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) 2 P) :
    ∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P =
      ∑ i ∈ range n, ∫ ω, (a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P := by
  apply hM.integral_sq_sum_mul_sub_of_pairwise_disjoint (range n)
    (fun i hi ↦ hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
    (ha := fun i hi ↦ ha i (mem_range.mp hi)) (hZ := fun i hi ↦ hZ i (mem_range.mp hi))
  intro i hi j hj hij
  rcases hij.lt_or_gt with h | h
  · exact Or.inl (hτ (by simpa using (mem_range.mp hi)) (mem_range.mp hj).le h)
  · exact Or.inr (hτ (by simpa using (mem_range.mp hj)) (mem_range.mp hi).le h)

/-- The expected sum of squared martingale increments equals the second moment of the
total increment. Only this increment needs to be square-integrable; empty grids and
repeated dates are allowed. -/
theorem integral_sum_sq_sub (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : MemLp (M (τ n) - M (τ 0)) 2 P) :
    ∫ ω, ∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2 ∂P =
      ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  have hΔ (i : ℕ) (hi : i < n) := hM.memLp_sub_of_monotoneOn hτ (by norm_num) h₂ hi
  rw [integral_finsetSum _ fun i hi ↦ by
    simpa only [Pi.sub_def] using (hΔ i (mem_range.mp hi)).integrable_sq]
  have h := hM.integral_sq_sum_mul_sub hτ
    (a := fun _ _ ↦ 1) (fun _ _ ↦ aestronglyMeasurable_const)
    (fun i hi ↦ by simpa only [Pi.sub_def, one_mul] using hΔ i hi)
  simp only [one_mul] at h
  have htel (ω : Ω) : ∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) =
      M (τ n) ω - M (τ 0) ω := sum_range_sub (fun i ↦ M (τ i) ω) n
  simpa only [htel] using h.symm

/-- Bounded a.e. predictable heights bound the second moment of a martingale transform by
`C²` times the second moment of the total increment. Only this increment needs to be
square-integrable. -/
theorem integral_sq_sum_mul_sub_le (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : MemLp (M (τ n) - M (τ 0)) 2 P)
    (ha : ∀ i < n, AEStronglyMeasurable[ℱ (τ i)] (a i) P) {C : ℝ}
    (hb : ∀ i < n, ∀ᵐ ω ∂P, |a i ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P ≤
      C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  let Δ (i : ℕ) (ω : Ω) := M (τ (i + 1)) ω - M (τ i) ω
  have hΔ (i : ℕ) (hi : i < n) : MemLp (Δ i) 2 P :=
    hM.memLp_sub_of_monotoneOn hτ (by norm_num) h₂ hi
  have hZ (i : ℕ) (hi : i < n) : MemLp (fun ω ↦ a i ω * Δ i ω) 2 P :=
    (memLp_top_of_bound ((ha i hi).mono (ℱ.le _)) C
      (by simpa only [Real.norm_eq_abs] using hb i hi)).mul (hΔ i hi)
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
      have hs : a i ω ^ 2 ≤ C ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by
      rw [← mul_sum, ← integral_finsetSum _ fun i hi ↦ (hΔ i (mem_range.mp hi)).integrable_sq]
      exact congrArg (C ^ 2 * ·) (hM.integral_sum_sq_sub hτ h₂)

/-- On a finite measure space, bounds `C` on the predictable heights and `B` on the total
martingale increment bound the transform's second moment by `C² * B²` times the total mass. -/
theorem integral_sq_sum_mul_sub_le_of_bound [IsFiniteMeasure P] (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, AEStronglyMeasurable[ℱ (τ i)] (a i) P) {B C : ℝ}
    (hB : ∀ᵐ ω ∂P, |M (τ n) ω - M (τ 0) ω| ≤ B)
    (hC : ∀ i < n, ∀ᵐ ω ∂P, |a i ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P ≤
      C ^ 2 * (B ^ 2 * P.real Set.univ) := by
  have h₂ : MemLp (M (τ n) - M (τ 0)) 2 P := MemLp.of_bound
    ((hM.integrable _).sub (hM.integrable _)).aestronglyMeasurable B hB
  apply (hM.integral_sq_sum_mul_sub_le hτ h₂ ha hC).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
  simpa only [Real.norm_eq_abs, sq_abs] using TauCeti.integral_norm_sq_le_of_ae_bound
    (f := fun ω ↦ M (τ n) ω - M (τ 0) ω)
    (by simpa only [Real.norm_eq_abs] using hB)

/-- If a martingale's total grid increment is bounded by `C`, the second moment of its
quadratic sum is at most `10 * C²` times the second moment of that increment, independently
of the grid. The numerical constant is not asserted to be sharp. -/
theorem integral_sq_sum_sq_sub_le (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, |M (τ n) ω - M (τ 0) ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2) ^ 2 ∂P ≤
      10 * C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  let a (i : ℕ) (ω : Ω) := M (τ i) ω - M (τ 0) ω
  have ha (i : ℕ) (hi : i ≤ n) : StronglyMeasurable[ℱ (τ i)] (a i) :=
    (hM.stronglyMeasurable _).sub
      ((hM.stronglyMeasurable _).mono (ℱ.mono (hτ (by simp) hi (Nat.zero_le i))))
  have hb' (i : ℕ) (hi : i ≤ n) : ∀ᵐ ω ∂P, |a i ω| ≤ C := by
    simpa only [Real.norm_eq_abs] using hM.ae_norm_sub_le_of_le
      (hτ (by simp) hi (Nat.zero_le i)) (hτ hi (by simp) hi) hb
  have hint := (hM.integrable (τ n)).sub (hM.integrable (τ 0))
  have h₂ : MemLp (a n) 2 P :=
    (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).2 (by
      simpa only [pow_two] using hint.bdd_mul hint.aestronglyMeasurable
        (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hb))
  let J (ω : Ω) := ∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)
  have hJi : Integrable (fun ω ↦ J ω ^ 2) P := (memLp_finsetSum _ fun i hi ↦
    (memLp_top_of_bound ((ha i (mem_range.mp hi).le).mono (ℱ.le _)).aestronglyMeasurable C
      (by simpa only [Real.norm_eq_abs] using hb' i (mem_range.mp hi).le)).mul
        (hM.memLp_sub_of_monotoneOn hτ (by norm_num) h₂ (mem_range.mp hi))).integrable_sq
  have hJ := hM.integral_sq_sum_mul_sub_le hτ h₂
    (fun i hi ↦ (ha i hi.le).aestronglyMeasurable) (fun i hi ↦ hb' i hi.le)
  have hpoint : ∀ᵐ ω ∂P,
      (∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2) ^ 2 ≤
        2 * C ^ 2 * a n ω ^ 2 + 8 * J ω ^ 2 := by
    filter_upwards [hb' n le_rfl] with ω hω
    have hid : ∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2 =
        a n ω ^ 2 - 2 * J ω := by
      simpa [a, J] using sum_range_sq_sub_eq (fun i ↦ a i ω) n
    rw [hid]
    have hs : a n ω ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (a n ω)),
      sq_nonneg (a n ω ^ 2 + 2 * J ω)]
  calc
    _ ≤ ∫ ω, 2 * C ^ 2 * a n ω ^ 2 + 8 * J ω ^ 2 ∂P := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      ((h₂.integrable_sq.const_mul _).add (hJi.const_mul _)) hpoint
    _ = 2 * C ^ 2 * ∫ ω, a n ω ^ 2 ∂P + 8 * ∫ ω, J ω ^ 2 ∂P := by
      rw [integral_add (h₂.integrable_sq.const_mul _) (hJi.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ 10 * C ^ 2 * ∫ ω, a n ω ^ 2 ∂P := by linarith

/-- On a finite measure space, the quadratic sum of a martingale whose total grid increment
is bounded by `C` has second moment at most `10 * C⁴` times the total mass, independently of
the grid. Families sharing an increment bound can use this estimate to establish uniform
integrability. -/
theorem integral_sq_sum_sq_sub_le_of_isFiniteMeasure [IsFiniteMeasure P] (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, |M (τ n) ω - M (τ 0) ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2) ^ 2 ∂P ≤
      10 * C ^ 4 * P.real Set.univ := by
  have hbound : ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P ≤ C ^ 2 * P.real Set.univ := by
    simpa only [Real.norm_eq_abs, sq_abs] using TauCeti.integral_norm_sq_le_of_ae_bound
      (f := fun ω ↦ M (τ n) ω - M (τ 0) ω)
      (by simpa only [Real.norm_eq_abs] using hb)
  calc
    _ ≤ 10 * C ^ 2 * (C ^ 2 * P.real Set.univ) :=
      (hM.integral_sq_sum_sq_sub_le hτ hb).trans
        (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ = _ := by ring

end MeasureTheory.Martingale
