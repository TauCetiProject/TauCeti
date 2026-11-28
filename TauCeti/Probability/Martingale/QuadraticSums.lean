/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import TauCeti.Probability.Process.QuadraticVariation
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Bounded
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Process.Adapted

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

For `ℝ≥0`-indexed real martingales, set-integral and second-moment bounds for the discrete
quadratic sum `TauCeti.Probability.quadraticSum Y g` along finite nondecreasing time grids are
also provided:
* `MeasureTheory.Martingale.setIntegral_sq_sub_eq_quadraticSum`: over any event in `ℱ s`, the
  set integral of `Y t ^ 2 - Y s ^ 2` for an `L²` real martingale equals that of its discrete
  quadratic sum along any nondecreasing finite grid from `s` to `t`.
* `MeasureTheory.Martingale.integral_mul_sub_sq_le`: a nonnegative bounded `ℱ u`-measurable
  weight multiplied by `(Y v - Y u) ^ 2` has expectation bounded by `c * (v - u) * E[W]` when
  `Y ^ 2 - A` is a martingale and `A` has `c`-Lipschitz increments.
* `MeasureTheory.Martingale.integral_sub_sq_le`: the unweighted second-moment increment bound
  `E[(Y v - Y u) ^ 2] ≤ c * (v - u) * μ.real univ`.
* `MeasureTheory.Martingale.integral_sub_pow_four_le`: the unweighted fourth-moment bound
  `E[(Y v - Y u) ^ 4] ≤ B ^ 2 * (c * (v - u) * μ.real univ)` for a bounded increment.
* `MeasureTheory.Martingale.integral_quadraticSum_le`: the first-moment bound
  `E[quadraticSum Y g] ≤ c * (g (Fin.last n) - g 0) * μ.real univ`.
* `MeasureTheory.Martingale.integral_quadraticSum_sq_le`: a bounded continuous-bracket real
  martingale satisfies an `L²` bound on `quadraticSum Y g` depending only on the uniform bound on
  `Y` and the Lipschitz bracket increment `c * (g (Fin.last n) - g 0)`.

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
    · have ht : ¬SigmaFinite (P.trim (ℱ.le (t i))) := fun _ ↦
        hσ (sigmaFiniteTrim_mono (ℱ.le (s j)) (ℱ.mono hij))
      have hs : ¬SigmaFinite (P.trim (ℱ.le (s i))) := fun _ ↦
        ht (sigmaFiniteTrim_mono (ℱ.le (t i)) (ℱ.mono (hst i hi)))
      apply integral_eq_zero_of_ae
      filter_upwards [hM.ae_eq_zero_of_not_sigmaFinite ht, hM.ae_eq_zero_of_not_sigmaFinite hs]
        with ω htω hsω
      simp only [Pi.zero_apply] at htω hsω
      simp [Z, htω, hsω]
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

-- Keep the integrability witness alongside the estimate so the quadratic-sum proof can use
-- both without re-establishing square integrability of the weighted increments.
private theorem integrable_sq_sum_mul_sub_and_le (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : MemLp (M (τ n) - M (τ 0)) 2 P)
    (ha : ∀ i < n, AEStronglyMeasurable[ℱ (τ i)] (a i) P) {C : ℝ}
    (hb : ∀ i < n, ∀ᵐ ω ∂P, |a i ω| ≤ C) :
    Integrable (fun ω ↦ (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2) P ∧
      (∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P) ≤
        C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P := by
  let Δ (i : ℕ) (ω : Ω) := M (τ (i + 1)) ω - M (τ i) ω
  have hΔ (i : ℕ) (hi : i < n) : MemLp (Δ i) 2 P :=
    hM.memLp_sub_of_monotoneOn hτ (by norm_num) h₂ hi
  have hZ (i : ℕ) (hi : i < n) : MemLp (fun ω ↦ a i ω * Δ i ω) 2 P :=
    (memLp_top_of_bound ((ha i hi).mono (ℱ.le _)) C
      (by simpa only [Real.norm_eq_abs] using hb i hi)).mul (hΔ i hi)
  refine ⟨(memLp_finsetSum _ fun i hi ↦ hZ i (mem_range.mp hi)).integrable_sq, ?_⟩
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

/-- Bounded a.e. predictable heights bound the second moment of a martingale transform by
`C²` times the second moment of the total increment. Only this increment needs to be
square-integrable. -/
theorem integral_sq_sum_mul_sub_le (hM : Martingale M ℱ P)
    (hτ : MonotoneOn τ (Set.Iic n)) (h₂ : MemLp (M (τ n) - M (τ 0)) 2 P)
    (ha : ∀ i < n, AEStronglyMeasurable[ℱ (τ i)] (a i) P) {C : ℝ}
    (hb : ∀ i < n, ∀ᵐ ω ∂P, |a i ω| ≤ C) :
    ∫ ω, (∑ i ∈ range n, a i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂P ≤
      C ^ 2 * ∫ ω, (M (τ n) ω - M (τ 0) ω) ^ 2 ∂P :=
  (hM.integrable_sq_sum_mul_sub_and_le hτ h₂ ha hb).2

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
    ((hM.integrable _).sub (hM.integrable _)).aestronglyMeasurable B
    (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hB)
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
  obtain ⟨hJi, hJ⟩ := hM.integrable_sq_sum_mul_sub_and_le hτ h₂
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

section

open ProbabilityTheory TauCeti.Probability
open scoped NNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-- Over any event `E ∈ ℱ s`, the set integral of `Y t ^ 2 - Y s ^ 2` for a real martingale `Y`
with square-integrable values on the grid `g` equals the set integral of `quadraticSum Y g`. -/
theorem setIntegral_sq_sub_eq_quadraticSum [SigmaFiniteFiltration μ ℱ] {Y : ℝ≥0 → Ω → ℝ}
    (hY : Martingale Y ℱ μ) {s t : ℝ≥0} {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) (hg0 : g 0 = s) (hgl : g (Fin.last n) = t)
    (hmem : ∀ k, MemLp (Y (g k)) 2 μ) :
    ∫ ω in E, (Y t ω ^ 2 - Y s ω ^ 2) ∂μ = ∫ ω in E, quadraticSum Y g ω ∂μ := by
  have hI2 (k : Fin (n + 1)) : IntegrableOn (fun ω ↦ Y (g k) ω ^ 2) E μ :=
    (hmem k).integrable_sq.integrableOn
  have hinc_int (i : Fin n) :
      Integrable (fun ω ↦ (Y (g i.succ) ω - Y (g i.castSucc) ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using ((hmem i.succ).sub (hmem i.castSucc)).integrable_sq
  have hstep (i : Fin n) : ∫ ω in E, (Y (g i.succ) ω ^ 2 - Y (g i.castSucc) ω ^ 2) ∂μ =
      ∫ ω in E, (Y (g i.succ) ω - Y (g i.castSucc) ω) ^ 2 ∂μ := by
    have hEu : MeasurableSet[ℱ (g i.castSucc)] E := ℱ.mono (hg0 ▸ hg (Fin.zero_le _)) E hE
    have h1 := setIntegral_congr_ae (ℱ.le _ E hEu)
      ((hY.condExp_sq (hg (Fin.castSucc_le_succ i)) (hmem i.succ)).mono fun _ hω _ ↦ hω)
    rw [setIntegral_condExp (ℱ.le _) (hmem i.succ).integrable_sq hEu,
      integral_add (hI2 i.castSucc) integrable_condExp.integrableOn,
      setIntegral_condExp (ℱ.le _) (hinc_int i) hEu] at h1
    rw [integral_sub (hI2 i.succ) (hI2 i.castSucc)]; linarith
  have hsub_int (i : Fin n) : IntegrableOn (fun ω ↦ Y (g i.succ) ω ^ 2 - Y (g i.castSucc) ω ^ 2)
      E μ := (hI2 i.succ).sub (hI2 i.castSucc)
  rw [quadraticSum_def, integral_finsetSum _ fun i _ ↦ (hinc_int i).integrableOn,
    ← Finset.sum_congr rfl fun i _ ↦ hstep i,
    ← integral_finsetSum Finset.univ
      (f := fun (i : Fin n) ω ↦ Y (g i.succ) ω ^ 2 - Y (g i.castSucc) ω ^ 2) fun i _ ↦ hsub_int i]
  congr 1; ext ω; rw [Fin.sum_univ_succ_sub_castSucc (fun i ↦ Y (g i) ω ^ 2), hg0, hgl]

/-- For a real `L²` martingale `Y` whose compensated square `Y ^ 2 - A` is a martingale with
`c`-Lipschitz increments `A v - A u ≤ c * (v - u)`, multiplying `(Y v - Y u) ^ 2` by any bounded
nonnegative `ℱ u`-measurable weight `W` yields expectation at most `c * (v - u) * ∫ W ∂μ`. -/
theorem integral_mul_sub_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) (hYu : MemLp (Y u) 2 μ) (hYv : MemLp (Y v) 2 μ)
    {W : Ω → ℝ} {C : ℝ} (hW_sm : StronglyMeasurable[ℱ u] W)
    (hW_bd : ∀ᵐ ω ∂μ, W ω ≤ C) (hW_nn : ∀ ω, 0 ≤ W ω) :
    ∫ ω, W ω * (Y v ω - Y u ω) ^ 2 ∂μ ≤ c * ((v : ℝ) - u) * ∫ ω, W ω ∂μ := by
  have hA : StronglyAdapted ℱ A := hY.stronglyAdapted.of_sq_sub hQ.stronglyAdapted
  have hd : Integrable (fun ω ↦ (Y v ω - Y u ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using (hYv.sub hYu).integrable_sq
  have ha : Integrable (fun ω ↦ A v ω - A u ω) μ := hA.integrable_sub_of_nonneg_le (hA_step u v huv)
  have hW_asm : AEStronglyMeasurable W μ := (hW_sm.mono (ℱ.le _)).aestronglyMeasurable
  have hW_nbd : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ C :=
    hW_bd.mono fun ω h ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg (hW_nn ω)]
  have h0 := hY.setIntegral_sq_sub_smul_eq_zero hQ huv MeasurableSet.univ hW_sm.aestronglyMeasurable
    ((((hQ.integrable v).sub (hQ.integrable u)).mul_bdd hW_asm hW_nbd).integrableOn) (by
      have hmul : Integrable (fun ω ↦ (Y v ω - Y u ω) * Y u ω) μ := by
        convert (hYv.sub hYu).integrable_mul hYu
      simpa only [smul_eq_mul, mul_assoc] using (hmul.mul_bdd hW_asm hW_nbd).integrableOn)
  have hmul_eq (ω : Ω) : ((Y v ω - Y u ω) ^ 2 - (A v ω - A u ω)) • W ω =
      W ω * (Y v ω - Y u ω) ^ 2 - W ω * (A v ω - A u ω) := by simp only [smul_eq_mul]; ring
  simp_rw [Measure.restrict_univ, hmul_eq] at h0
  rw [integral_sub (hd.bdd_mul hW_asm hW_nbd) (ha.bdd_mul hW_asm hW_nbd), sub_eq_zero] at h0
  rw [h0, ← integral_const_mul]
  exact integral_mono_ae (ha.bdd_mul hW_asm hW_nbd)
    (((integrable_const C).mono' hW_asm hW_nbd).const_mul _) ((hA_step u v huv).mono fun ω hω ↦ by
      dsimp only; rw [mul_comm (c * _)]; exact mul_le_mul_of_nonneg_left hω.2 (hW_nn ω))

/-- Unweighted second-moment bound for the increment of a real `L²` martingale `Y` whose
compensated square `Y ^ 2 - A` is a martingale with `c`-Lipschitz increments. -/
theorem integral_sub_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) (hYu : MemLp (Y u) 2 μ) (hYv : MemLp (Y v) 2 μ) :
    ∫ ω, (Y v ω - Y u ω) ^ 2 ∂μ ≤ c * ((v : ℝ) - u) * μ.real Set.univ := by
  simpa [integral_const, mul_comm (μ.real Set.univ)] using
    hY.integral_mul_sub_sq_le hQ hA_step huv hYu hYv (W := fun _ ↦ (1 : ℝ))
      stronglyMeasurable_const (C := 1) (ae_of_all μ fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)

/-- Fourth-moment bound for a bounded increment of a real `L²` martingale `Y` whose
compensated square `Y ^ 2 - A` is a martingale with `c`-Lipschitz increments. -/
theorem integral_sub_pow_four_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {B c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {u v : ℝ≥0} (huv : u ≤ v) (hYu : MemLp (Y u) 2 μ) (hYv : MemLp (Y v) 2 μ)
    (hB : ∀ᵐ ω ∂μ, |Y v ω - Y u ω| ≤ B) :
    ∫ ω, (Y v ω - Y u ω) ^ 4 ∂μ ≤ B ^ 2 * (c * ((v : ℝ) - u) * μ.real Set.univ) := by
  have hd2 : ∀ᵐ ω ∂μ, (Y v ω - Y u ω) ^ 2 ≤ B ^ 2 :=
    hB.mono fun _ hω ↦ by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hd_lp : MemLp (fun ω ↦ (Y v ω - Y u ω) ^ 2) 2 μ := MemLp.of_bound
    ((hYv.sub hYu).aestronglyMeasurable.pow 2) (B ^ 2)
    (hd2.mono fun _ hω ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
  have hint2 : Integrable (fun ω ↦ (Y v ω - Y u ω) ^ 2) μ := by
    simpa only [Pi.sub_apply] using (hYv.sub hYu).integrable_sq
  have h2 := hY.integral_sub_sq_le hQ hA_step huv hYu hYv
  refine ((integral_mono_ae (by simpa only [← pow_mul] using hd_lp.integrable_sq)
    (hint2.const_mul (B ^ 2)) (hd2.mono fun ω hω ↦
      (show (Y v ω - Y u ω) ^ 4 = (Y v ω - Y u ω) ^ 2 * (Y v ω - Y u ω) ^ 2 by ring) ▸
        mul_le_mul_of_nonneg_right hω (sq_nonneg _))).trans_eq
    (integral_const_mul _ _)).trans (by gcongr)

/-- First-moment bound for the discrete quadratic sum of a real `L²` martingale `Y` along a
nondecreasing finite grid `g : Fin (n + 1) → ℝ≥0`, when `Y ^ 2 - A` is a martingale and `A` has
nonnegative `c`-Lipschitz increments. -/
theorem integral_quadraticSum_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) (hmem : ∀ k, MemLp (Y (g k)) 2 μ) :
    ∫ ω, quadraticSum Y g ω ∂μ ≤ c * ((g (Fin.last n) : ℝ) - g 0) * μ.real Set.univ := by
  rw [quadraticSum_def, integral_finsetSum _ fun j _ ↦ by
    simpa only [Pi.sub_apply] using ((hmem j.succ).sub (hmem j.castSucc)).integrable_sq]
  refine (Finset.sum_le_sum fun j _ ↦ hY.integral_sub_sq_le hQ hA_step (hg (Fin.castSucc_le_succ j))
    (hmem j.castSucc) (hmem j.succ)).trans_eq ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_succ_sub_castSucc (fun k ↦ (g k : ℝ))]

private lemma integral_quadraticSum_mul_last_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ}
    {R c : ℝ} (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (hc : 0 ≤ c) {n : ℕ} {g : Fin (n + 2) → ℝ≥0} (hg' : Monotone (g ∘ Fin.castSucc))
    (hstep_le : g (Fin.last n).castSucc ≤ g (Fin.last (n + 1)))
    (hYR : ∀ k, ∀ᵐ ω ∂μ, |Y (g k) ω| ≤ R) (hmem : ∀ k, MemLp (Y (g k)) 2 μ) :
    ∫ ω, quadraticSum Y (g ∘ Fin.castSucc) ω *
        (Y (g (Fin.last (n + 1))) ω - Y (g (Fin.last n).castSucc) ω) ^ 2 ∂μ ≤
      c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) *
        (c * ((g (Fin.last n).castSucc : ℝ) - g 0) * μ.real Set.univ) := by
  let g' : Fin (n + 1) → ℝ≥0 := g ∘ Fin.castSucc
  refine (hY.integral_mul_sub_sq_le hQ hA_step hstep_le (hmem (Fin.last n).castSucc)
    (hmem (Fin.last (n + 1))) (hY.stronglyAdapted.stronglyMeasurable_quadraticSum hg')
    (ae_quadraticSum_le_of_bound g' fun k ↦ hYR k.castSucc)
    (fun _ ↦ quadraticSum_nonneg Y g' _)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (by simpa only [g', Function.comp_apply, Fin.castSucc_zero] using
      integral_quadraticSum_le hY hQ hA_step hg' fun k ↦ hmem k.castSucc)
    (mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hstep_le)))

/-- Second-moment bound for the discrete quadratic sum of a uniformly bounded real martingale `Y`
along a nondecreasing finite grid `g : Fin (n + 1) → ℝ≥0`, when `Y ^ 2 - A` is a martingale and
`A` has nonnegative `c`-Lipschitz increments (`0 ≤ c`). -/
theorem integral_quadraticSum_sq_le [IsFiniteMeasure μ] {Y A : ℝ≥0 → Ω → ℝ} {R c : ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    (hA_step : ∀ u v, u ≤ v → ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u))
    (hc : 0 ≤ c) {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g)
    (hYR : ∀ k, ∀ᵐ ω ∂μ, |Y (g k) ω| ≤ R) :
    ∫ ω, quadraticSum Y g ω ^ 2 ∂μ ≤
      (4 * R ^ 2 * (c * ((g (Fin.last n) : ℝ) - g 0)) +
        2 * (c * ((g (Fin.last n) : ℝ) - g 0)) ^ 2) * μ.real Set.univ := by
  induction n with
  | zero => simp [quadraticSum_zero, Fin.last_zero]
  | succ n ih =>
    -- Split `S_{n+1} = S_n + d` and control `E[S_n^2]`, `E[S_n d]`, and `E[d^2]`.
    let g' : Fin (n + 1) → ℝ≥0 := g ∘ Fin.castSucc
    have hg' : Monotone g' := fun _ _ hij ↦ hg (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hstep_le : g (Fin.last n).castSucc ≤ g (Fin.last (n + 1)) := by
      simpa [Fin.succ_last] using hg (Fin.castSucc_le_succ (Fin.last n))
    have hmem (k : Fin (n + 2)) : MemLp (Y (g k)) 2 μ :=
      MemLp.of_bound ((hY.stronglyAdapted (g k)).mono (ℱ.le _)).aestronglyMeasurable R
        ((hYR k).mono fun _ hω ↦ by rwa [Real.norm_eq_abs])
    let d (ω : Ω) : ℝ := (Y (g (Fin.last (n + 1))) ω - Y (g (Fin.last n).castSucc) ω) ^ 2
    have hd_lp : MemLp d 2 μ := memLp_sub_sq_of_bound 2 (hmem _).aestronglyMeasurable
      (hmem _).aestronglyMeasurable (hYR _) (hYR _)
    have hS'_lp := memLp_quadraticSum_of_bound 2 g'
      (fun k ↦ (hmem k.castSucc).aestronglyMeasurable) (fun k ↦ hYR k.castSucc)
    have ih' := ih hg' fun k ↦ hYR k.castSucc
    have hcross := integral_quadraticSum_mul_last_sq_le hY hQ hA_step hc hg' hstep_le hYR hmem
    have hquart : ∫ ω, d ω ^ 2 ∂μ ≤ 4 * R ^ 2 * (c * ((g (Fin.last (n + 1)) : ℝ) -
        g (Fin.last n).castSucc) * μ.real Set.univ) := by
      rw [show (4 * R ^ 2 : ℝ) = (2 * R) ^ 2 by ring]
      simpa only [d, ← pow_mul] using hY.integral_sub_pow_four_le hQ hA_step hstep_le
        (hmem _) (hmem _) (ae_abs_sub_le_two_mul (hYR _) (hYR _))
    have hS_sq (ω : Ω) : quadraticSum Y g ω ^ 2 = quadraticSum Y g' ω ^ 2 +
        2 * (quadraticSum Y g' ω * d ω) + d ω ^ 2 := by rw [quadraticSum_castSucc_add Y g ω]; ring
    have h2S : Integrable (fun ω ↦ 2 * (quadraticSum Y g' ω * d ω)) μ :=
      (hS'_lp.integrable_mul hd_lp).const_mul 2
    simp_rw [hS_sq]
    rw [integral_add (f := fun ω ↦ quadraticSum Y g' ω ^ 2 + 2 * (quadraticSum Y g' ω * d ω))
        (hS'_lp.integrable_sq.add h2S) hd_lp.integrable_sq,
      integral_add hS'_lp.integrable_sq h2S, integral_const_mul]
    simp only [g', Function.comp_apply, Fin.castSucc_zero] at ih'
    have hL0 := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2
      (hg (Fin.zero_le (Fin.last n).castSucc))))
    have hδ0 := mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 hstep_le))
    have hsplit : (g (Fin.last (n + 1)) : ℝ) - g 0 = ((g (Fin.last n).castSucc : ℝ) - g 0) +
        ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc) := by ring
    have hμ0 : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    nlinarith [ih', hcross, hquart, hsplit, mul_nonneg (mul_nonneg hL0 hδ0) hμ0,
      mul_nonneg (sq_nonneg (c * ((g (Fin.last (n + 1)) : ℝ) - g (Fin.last n).castSucc))) hμ0]

end MeasureTheory.Martingale

end
