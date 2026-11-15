/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation
public import TauCeti.Probability.BrownianMotion.WeightedQuadraticVariation
public import TauCeti.Probability.Process.Stratonovich
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.Calculus.Taylor.Symmetric
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Brownian Stratonovich symmetric-endpoint and temporal-midpoint partition limits

Along deterministic partitions of `[a, b]` with vanishing mesh, two discrete approximations to the
Stratonovich integral of a `C¹` function `h` with primitive `H` along Brownian motion `B` converge
in probability to `H(B_b) - H(B_a)` without any second derivative of `h` or moment assumption on
`h(B)` or `H(B)`:

* **Symmetric-endpoint sums**
  (`IsBrownianReal.tendstoInMeasure_sum_half_add_mul_sub`):
  `∑ (h(B_{t_i}) + h(B_{t_{i+1}})) / 2 * (B_{t_{i+1}} - B_{t_i}) → H(B_b) - H(B_a)` in probability.
  Because this follows from path continuity and unweighted quadratic-sum convergence alone, the
  same limit holds for `B + A` when `A` has continuous bounded-variation paths
  (`IsBrownianReal.tendstoInMeasure_sum_half_add_mul_sub_add_of_boundedVariationOn`).
* **Temporal-midpoint sums**
  (`IsBrownianReal.tendstoInMeasure_sum_midpoint_mul_sub`):
  `∑ h(B_{(t_i + t_{i+1}) / 2}) * (B_{t_{i+1}} - B_{t_i}) → H(B_b) - H(B_a)` in probability.
  Comparing the midpoint sample with the symmetric endpoint average isolates the alternating
  half-step quadratic sum
  `1 / 2 * ∑ h'(B_{t_i}) * ((B_{m_i} - B_{t_i})² - (B_{t_{i+1}} - B_{m_i})²)`,
  whose `L²` norm is computed exactly on predictable and bounded left weights
  (`TauCeti.Probability.IsFilteredPreBrownianReal.integral_sq_sum_mul_midpoint_sq_sub_sq`,
  `IsPreBrownianReal.integral_sq_sum_comp_mul_midpoint_sq_sub_sq`) and extended
  to general continuous `h'` by pathwise localization on `[a, b]`
  (`IsBrownianReal.tendstoInMeasure_sum_mul_midpoint_sq_sub_sq`).

In contrast to the symmetric-endpoint rule, temporal-midpoint convergence genuinely depends on the
Brownian half-step increment law: for a deterministically time-changed pre-Brownian motion `B ∘ A`
evaluated at intermediate clock values `a_i ≤ c_i ≤ a_{i+1}`, the temporal-midpoint sum for the
identity integrand has exact mean bias `1 / 2 * ∑ ((c_i - a_i) - (a_{i+1} - c_i))` and variance
`1 / 2 * ∑ ((c_i - a_i)² + (a_{i+1} - c_i)²)`
(`IsPreBrownianReal.integral_sum_comp_midpoint_mul_sub_sub_half_sq`,
`IsPreBrownianReal.variance_sum_comp_midpoint_mul_sub_sub_half_sq`), so under
vanishing clock mesh and asymptotic clock asymmetry `β` it converges in probability to
`(B(A_1)² - B(A_0)²) / 2 + β`
(`IsPreBrownianReal.tendstoInMeasure_sum_comp_midpoint_mul_sub`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter V, §5.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open Finset Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ range (2 * n), f j = ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ, add_assoc]

private theorem tendstoInMeasure_add_zero {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {l : Filter ι} {f₁ f₂ : ι → Ω → ℝ}
    (h₁ : TendstoInMeasure μ f₁ l (fun _ ↦ 0))
    (h₂ : TendstoInMeasure μ f₂ l (fun _ ↦ 0)) :
    TendstoInMeasure μ (fun k ω ↦ f₁ k ω + f₂ k ω) l (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_norm] at h₁ h₂ ⊢
  intro ε hε
  have h0 : Tendsto (fun k ↦ μ {ω | ε / 2 ≤ ‖f₁ k ω - 0‖} + μ {ω | ε / 2 ≤ ‖f₂ k ω - 0‖})
      l (𝓝 0) := by
    simpa only [add_zero] using (h₁ (ε / 2) (half_pos hε)).add (h₂ (ε / 2) (half_pos hε))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun _ ↦ by positivity) fun k ↦ ?_
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  have hlt₁ : ‖f₁ k ω‖ < ε / 2 := by simpa only [Set.mem_ofPred_eq, sub_zero, not_le] using hnot.1
  have hlt₂ : ‖f₂ k ω‖ < ε / 2 := by simpa only [Set.mem_ofPred_eq, sub_zero, not_le] using hnot.2
  have hsum : ‖f₁ k ω + f₂ k ω - 0‖ < ε := by
    rw [sub_zero]
    exact (norm_add_le _ _).trans_lt (by linarith)
  exact hsum.not_ge hω

private theorem tendstoInMeasure_const_mul_zero {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {l : Filter ι} (c : ℝ) {f : ι → Ω → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ ↦ 0)) :
    TendstoInMeasure μ (fun k ω ↦ c * f k ω) l (fun _ ↦ 0) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [tendstoInMeasure_iff_norm]
    intro ε hε
    simp only [zero_mul, sub_self, norm_zero, hε.not_ge, Set.ofPred_false, measure_empty]
    exact tendsto_const_nhds
  · rw [tendstoInMeasure_iff_norm] at hf ⊢
    intro ε hε
    have hcpos : 0 < |c| := abs_pos.2 hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hf (ε / |c|) (div_pos hε hcpos)) (fun _ ↦ by positivity) fun k ↦ measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_mul] at hω ⊢
    rwa [div_le_iff₀' hcpos]

private theorem monotoneOn_Iic_of_le_succ {α : Type*} [Preorder α] {f : ℕ → α} {N : ℕ}
    (h : ∀ j < N, f j ≤ f (j + 1)) : MonotoneOn f (Set.Iic N) := by
  have hrec : ∀ a b, a ≤ b → b ≤ N → f a ≤ f b := by
    intro a b hab
    induction hab with
    | refl => intro _; exact le_rfl
    | @step m _ ih =>
      intro hm
      exact (ih (Nat.le_of_succ_le hm)).trans (h m (Nat.lt_of_succ_le hm))
  exact fun a _ b hb hab ↦ hrec a b hab hb

private theorem monotoneOn_even_odd_Iic {α : Type*} [Preorder α] {n : ℕ} {a c : ℕ → α}
    (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    MonotoneOn (fun j ↦ if j % 2 = 0 then a (j / 2) else c (j / 2)) (Set.Iic (2 * n)) := by
  refine monotoneOn_Iic_of_le_succ fun j hj ↦ ?_
  have hi : j / 2 < n := by omega
  obtain ⟨h₁, h₂⟩ := hac (j / 2) hi
  rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
  · have hdiv1 : (j + 1) / 2 = j / 2 := by omega
    have hmod1 : (j + 1) % 2 = 1 := by omega
    simpa only [hmod, ↓reduceIte, hmod1, one_ne_zero, hdiv1] using h₁
  · have hdiv1 : (j + 1) / 2 = j / 2 + 1 := by omega
    have hmod1 : (j + 1) % 2 = 0 := by omega
    simpa only [hmod, one_ne_zero, ↓reduceIte, hmod1, hdiv1] using h₂

private theorem nnreal_le_midpoint_and_le {x y : ℝ≥0} (h : x ≤ y) :
    x ≤ (x + y) / 2 ∧ (x + y) / 2 ≤ y := by
  constructor <;> · rw [← NNReal.coe_le_coe]; push_cast; linarith [NNReal.coe_le_coe.2 h]

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- For square-integrable heights `Y i` measurable at `t i`, weighting the difference of squared
half-step Brownian increments
`(B((t_i + t_{i+1}) / 2) - B(t_i))² - (B(t_{i+1}) - B((t_i + t_{i+1}) / 2))²`
cancels the deterministic half-step drifts identically and yields exact second moment
`∑ E[Y_i²] (t_{i+1} - t_i)²`. -/
theorem integral_sq_sum_mul_midpoint_sq_sub_sq (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {Y : ℕ → Ω → ℝ}
    (hY : ∀ i < n, Measurable[ℱ (t i)] (Y i)) (hYi : ∀ i < n, MemLp (Y i) 2 P) :
    (∫ ω, (∑ i ∈ range n, Y i ω *
      ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
        (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) =
      ∑ i ∈ range n, (∫ ω, Y i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  let u : ℕ → ℝ≥0 := fun j ↦
    if j % 2 = 0 then t (j / 2) else (t (j / 2) + t (j / 2 + 1)) / 2
  have hu_even (i : ℕ) : u (2 * i) = t i := by simp [u]
  have hu_odd (i : ℕ) : u (2 * i + 1) = (t i + t (i + 1)) / 2 := by
    have hdiv : (2 * i + 1) / 2 = i := by omega
    have hmod : (2 * i + 1) % 2 = 1 := by omega
    simp [u, hdiv, hmod]
  have hu : MonotoneOn u (Set.Iic (2 * n)) :=
    monotoneOn_even_odd_Iic fun i hi ↦ nnreal_le_midpoint_and_le (ht hi.le hi (Nat.le_succ _))
  let H : ℕ → Ω → ℝ := fun j ↦
    if j % 2 = 0 then Y (j / 2) else fun ω ↦ -Y (j / 2) ω
  have hH_even (i : ℕ) : H (2 * i) = Y i := by simp [H]
  have hH_odd (i : ℕ) : H (2 * i + 1) = fun ω ↦ -Y i ω := by
    have hdiv : (2 * i + 1) / 2 = i := by omega
    have hmod : (2 * i + 1) % 2 = 1 := by omega
    simp [H, hdiv, hmod]
  have hHm : ∀ j < 2 * n, Measurable[ℱ (u j)] (H j) := by
    intro j hj
    have hi : j / 2 < n := by omega
    rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
    · have hj_eq : j = 2 * (j / 2) := by omega
      rw [hj_eq, hu_even, hH_even]
      exact hY _ hi
    · have hj_eq : j = 2 * (j / 2) + 1 := by omega
      have hle : t (j / 2) ≤ u (2 * (j / 2) + 1) := by
        rw [hu_odd]
        exact (nnreal_le_midpoint_and_le (ht hi.le hi (Nat.le_succ _))).1
      rw [hj_eq, hH_odd]
      exact (hY _ hi).neg.mono (ℱ.mono hle) le_rfl
  have hHi : ∀ j < 2 * n, MemLp (H j) 2 P := by
    intro j hj
    have hi : j / 2 < n := by omega
    rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
    · have hj_eq : j = 2 * (j / 2) := by omega
      rw [hj_eq, hH_even]
      exact hYi _ hi
    · have hj_eq : j = 2 * (j / 2) + 1 := by omega
      rw [hj_eq, hH_odd]
      exact (hYi _ hi).neg
  have hid := hB.integral_sq_sum_mul_sq_sub_sub hu hHm hHi
  have hlhs (ω : Ω) :
      ∑ j ∈ range (2 * n), H j ω *
        ((B (u (j + 1)) ω - B (u j) ω) ^ 2 - ((u (j + 1) : ℝ) - u j)) =
      ∑ i ∈ range n, Y i ω *
        ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
          (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2) := by
    rw [sum_range_two_mul]
    refine sum_congr rfl fun i _ ↦ ?_
    have h2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [h2, hu_even, hu_odd, hu_even, hH_even, hH_odd]
    push_cast
    ring
  have hrhs :
      2 * ∑ j ∈ range (2 * n), (∫ ω, H j ω ^ 2 ∂P) * ((u (j + 1) : ℝ) - u j) ^ 2 =
        ∑ i ∈ range n, (∫ ω, Y i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
    rw [sum_range_two_mul, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    have h2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [h2, hu_even, hu_odd, hu_even, hH_even, hH_odd]
    simp only [neg_sq]
    push_cast
    ring
  simp_rw [hlhs] at hid
  exact hid.trans hrhs

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For Borel-measurable functions `g i` with square-integrable left evaluations `g i (B (t i))`,
the alternating half-step Brownian quadratic sum has exact second moment
`∑ E[g_i(B_{t_i})²] (t_{i+1} - t_i)²`. Only the finite-dimensional pre-Brownian laws are needed. -/
theorem integral_sq_sum_comp_mul_midpoint_sq_sub_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {g : ℕ → ℝ → ℝ}
    (hg : ∀ i < n, Measurable (g i))
    (hgi : ∀ i < n, MemLp (fun ω ↦ g i (B (t i) ω)) 2 P) :
    (∫ ω, (∑ i ∈ range n, g i (B (t i) ω) *
      ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
        (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) =
      ∑ i ∈ range n, (∫ ω, g i (B (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  let W : ℝ≥0 → Ω → ℝ := fun u ↦ (hB.aemeasurable u).aestronglyMeasurable.mk (B u)
  have hWmeas : ∀ u, StronglyMeasurable (W u) :=
    fun u ↦ (hB.aemeasurable u).aestronglyMeasurable.stronglyMeasurable_mk
  have hBW : ∀ u, B u =ᵐ[P] W u :=
    fun u ↦ (hB.aemeasurable u).aestronglyMeasurable.ae_eq_mk
  have hWf := (hB.congr hBW).isFilteredPreBrownianReal_natural hWmeas
  have hYm : ∀ i < n, Measurable[Filtration.natural W hWmeas (t i)] (fun ω ↦ g i (W (t i) ω)) :=
    fun i hi ↦ (hg i hi).comp (hWf.adapted (t i))
  have hYi : ∀ i < n, MemLp (fun ω ↦ g i (W (t i) ω)) 2 P := fun i hi ↦
    (hgi i hi).ae_eq ((hBW (t i)).fun_comp (g i))
  have hid := hWf.integral_sq_sum_mul_midpoint_sq_sub_sq ht hYm hYi
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ range n,
      B (t i) ω = W (t i) ω ∧
      B ((t i + t (i + 1)) / 2) ω = W ((t i + t (i + 1)) / 2) ω ∧
      B (t (i + 1)) ω = W (t (i + 1)) ω := by
    rw [eventually_all_finset]
    intro i _
    filter_upwards [hBW (t i), hBW ((t i + t (i + 1)) / 2), hBW (t (i + 1))] with ω h₀ hm h₁
    exact ⟨h₀, hm, h₁⟩
  have hlhs :
      (∫ ω, (∑ i ∈ range n, g i (B (t i) ω) *
        ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
          (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) =
      (∫ ω, (∑ i ∈ range n, g i (W (t i) ω) *
        ((W ((t i + t (i + 1)) / 2) ω - W (t i) ω) ^ 2 -
          (W (t (i + 1)) ω - W ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) := by
    refine integral_congr_ae (hall.mono fun ω hω ↦ ?_)
    dsimp only
    congr 1
    refine sum_congr rfl fun i hi ↦ ?_
    obtain ⟨h₀, hm, h₁⟩ := hω i hi
    rw [h₀, hm, h₁]
  have hrhs :
      ∑ i ∈ range n, (∫ ω, g i (W (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 =
        ∑ i ∈ range n, (∫ ω, g i (B (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
    refine sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact integral_congr_ae ((hBW (t i)).symm.mono fun ω hω ↦ by simp [hω])
  exact (hlhs.trans hid).trans hrhs

/-- Uniformly bounded Borel left weights bound the second moment of the alternating half-step
Brownian quadratic sum by `C ^ 2 * (t n - t 0) * δ` whenever every grid step is at most `δ`. -/
theorem integral_sq_sum_comp_mul_midpoint_sq_sub_sq_le (hB : IsPreBrownianReal B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {g : ℕ → ℝ → ℝ} {C δ : ℝ}
    (hg : ∀ i < n, Measurable (g i)) (hbound : ∀ i < n, ∀ y, |g i y| ≤ C)
    (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    (∫ ω, (∑ i ∈ range n, g i (B (t i) ω) *
      ((B ((t i + t (i + 1)) / 2) ω - B (t i) ω) ^ 2 -
        (B (t (i + 1)) ω - B ((t i + t (i + 1)) / 2) ω) ^ 2)) ^ 2 ∂P) ≤
      C ^ 2 * ((t n : ℝ) - t 0) * δ := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hgi : ∀ i < n, MemLp (fun ω ↦ g i (B (t i) ω)) 2 P := by
    intro i hi
    refine MemLp.of_bound ((hg i hi).aestronglyMeasurable.comp_aemeasurable (hB.aemeasurable (t i)))
      C (ae_of_all _ fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hbound i hi (B (t i) ω)
  rw [hB.integral_sq_sum_comp_mul_midpoint_sq_sub_sq ht hg hgi]
  have hsum :
      ∑ i ∈ range n, (∫ ω, g i (B (t i) ω) ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 ≤
        ∑ i ∈ range n, C ^ 2 * (((t (i + 1) : ℝ) - t i) * δ) := by
    refine sum_le_sum fun i hi ↦ ?_
    have hi' := mem_range.1 hi
    have hstep0 : 0 ≤ (t (i + 1) : ℝ) - t i :=
      sub_nonneg.2 (NNReal.coe_le_coe.2 (ht hi'.le hi' (Nat.le_succ i)))
    have hint_le : ∫ ω, g i (B (t i) ω) ^ 2 ∂P ≤ C ^ 2 := by
      have hpt : ∀ ω, g i (B (t i) ω) ^ 2 ≤ C ^ 2 := fun ω ↦ by
        have hb := abs_le.1 (hbound i hi' (B (t i) ω))
        nlinarith
      calc
        ∫ ω, g i (B (t i) ω) ^ 2 ∂P ≤ ∫ _, C ^ 2 ∂P :=
          integral_mono (hgi i hi').integrable_sq (integrable_const _) hpt
        _ = C ^ 2 := by simp
    have hsq_le : ((t (i + 1) : ℝ) - t i) ^ 2 ≤ ((t (i + 1) : ℝ) - t i) * δ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (hmesh i hi') hstep0
    exact mul_le_mul hint_le hsq_le (sq_nonneg _) (sq_nonneg _)
  refine hsum.trans_eq ?_
  rw [← mul_sum, ← sum_mul, sum_range_sub (fun i ↦ (t i : ℝ)) n]
  ring

/-- On any interleaved deterministic clock `a_0 ≤ c_0 ≤ a_1 ≤ … ≤ a_n`, the difference between
the intermediate-sample sum `∑ B(c_i)(B(a_{i+1}) - B(a_i))` and the symmetric Stratonovich value
`(B(a_n)² - B(a_0)²) / 2` has exact expectation equal to half the net clock asymmetry
`1 / 2 * ∑ ((c_i - a_i) - (a_{i+1} - c_i))`. -/
theorem integral_sum_comp_midpoint_mul_sub_sub_half_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {a c : ℕ → ℝ≥0} (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    (∫ ω, ((∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2) ∂P) =
      1 / 2 * ∑ i ∈ range n, (((c i : ℝ) - a i) - ((a (i + 1) : ℝ) - c i)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hid (ω : Ω) :
      (∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2 =
      ∑ i ∈ range n, 1 / 2 *
        ((B (c i) ω - B (a i) ω) ^ 2 - (B (a (i + 1)) ω - B (c i) ω) ^ 2) := by
    rw [← TauCeti.sum_half_add_mul_sub_id (fun i ↦ B (a i) ω) n, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    ring
  simp_rw [hid]
  have hint (i : ℕ) : Integrable (fun ω ↦
      (B (c i) ω - B (a i) ω) ^ 2 - (B (a (i + 1)) ω - B (c i) ω) ^ 2) P := by
    simpa only [Pi.sub_def] using
      (hB.integrable_pow_sub (a i) (c i) 2).sub (hB.integrable_pow_sub (c i) (a (i + 1)) 2)
  rw [integral_finsetSum (range n) fun i _ ↦ (hint i).const_mul (1 / 2), mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  obtain ⟨h₁, h₂⟩ := hac i (mem_range.1 hi)
  rw [integral_const_mul,
    integral_sub (hB.integrable_pow_sub (a i) (c i) 2) (hB.integrable_pow_sub (c i) (a (i + 1)) 2),
    hB.integral_sq_sub_of_le h₁, hB.integral_sq_sub_of_le h₂]

/-- On any interleaved deterministic clock `a_0 ≤ c_0 ≤ a_1 ≤ … ≤ a_n`, the variance of the
deviation `(∑ B(c_i)(B(a_{i+1}) - B(a_i))) - (B(a_n)² - B(a_0)²) / 2` equals
`1 / 2 * ∑ ((c_i - a_i)² + (a_{i+1} - c_i)²)`. -/
theorem variance_sum_comp_midpoint_mul_sub_sub_half_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {a c : ℕ → ℝ≥0} (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    Var[fun ω ↦ (∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2; P] =
      1 / 2 * ∑ i ∈ range n, (((c i : ℝ) - a i) ^ 2 + ((a (i + 1) : ℝ) - c i) ^ 2) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let u : ℕ → ℝ≥0 := fun m ↦ if m % 2 = 0 then a (m / 2) else c (m / 2)
  have hu_even (i : ℕ) : u (2 * i) = a i := by simp [u]
  have hu_odd (i : ℕ) : u (2 * i + 1) = c i := by
    have hdiv : (2 * i + 1) / 2 = i := by omega
    have hmod : (2 * i + 1) % 2 = 1 := by omega
    simp [u, hdiv, hmod]
  have hu : MonotoneOn u (Set.Iic (2 * n)) := monotoneOn_even_odd_Iic hac
  let τ : Fin (2 * n + 1) → ℝ≥0 := fun j ↦ u j
  have hτ : Monotone τ := fun j₁ j₂ hle ↦
    hu (Nat.le_of_lt_succ j₁.isLt) (Nat.le_of_lt_succ j₂.isLt) hle
  let sgn : ℕ → ℝ := fun m ↦ if m % 2 = 0 then 1 / 2 else -1 / 2
  let ξ : Fin (2 * n) → Ω → ℝ := fun j ω ↦
    sgn j * (B (τ j.succ) ω - B (τ j.castSucc) ω) ^ 2
  have hL (j : Fin (2 * n)) : MemLp (ξ j) 2 P :=
    (hB.memLp_sq_sub (τ j.succ) (τ j.castSucc)).const_mul (sgn j)
  have hind := (hB.hasIndepIncrements (2 * n) τ hτ).comp
    (fun j (x : ℝ) ↦ sgn j * x ^ 2) (by fun_prop)
  have hv := IndepFun.variance_sum (s := univ) (fun j _ ↦ hL j)
    (fun i _ j _ hij ↦ hind.indepFun hij)
  have hfun : (fun ω ↦ (∑ i ∈ range n, B (c i) ω * (B (a (i + 1)) ω - B (a i) ω)) -
        (B (a n) ω ^ 2 - B (a 0) ω ^ 2) / 2) =
      ∑ j : Fin (2 * n), ξ j := by
    ext ω
    rw [Finset.sum_apply]
    have hfin : ∑ j : Fin (2 * n), ξ j ω =
        ∑ m ∈ range (2 * n), sgn m * (B (u (m + 1)) ω - B (u m) ω) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun m ↦ sgn m * (B (u (m + 1)) ω - B (u m) ω) ^ 2) (2 * n)
    rw [hfin, sum_range_two_mul,
      ← TauCeti.sum_half_add_mul_sub_id (fun i ↦ B (a i) ω) n, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    have h2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    have hm0 : (2 * i) % 2 = 0 := by omega
    have hm1 : (2 * i + 1) % 2 = 1 := by omega
    rw [h2, hu_even, hu_odd, hu_even]
    simp only [sgn, hm0, hm1, ↓reduceIte, one_ne_zero]
    ring
  rw [hfun, hv]
  have hterm (j : Fin (2 * n)) :
      Var[ξ j; P] = 1 / 2 * ((u ((j : ℕ) + 1) : ℝ) - u j) ^ 2 := by
    have hsq_sgn : sgn j ^ 2 = 1 / 4 := by
      dsimp [sgn]
      split_ifs <;> norm_num
    have hv_sq : Var[fun ω ↦ (B (τ j.succ) ω - B (τ j.castSucc) ω) ^ 2; P] =
        2 * ((τ j.succ : ℝ) - τ j.castSucc) ^ 2 := by
      rw [variance_eq_sub (hB.memLp_sq_sub (τ j.succ) (τ j.castSucc))]
      simp only [Pi.pow_def, ← pow_mul, Nat.reduceMul]
      rw [hB.integral_sq_sub_of_le (hτ (Fin.castSucc_le_succ j)),
        hB.integral_pow_four_sub_of_le (hτ (Fin.castSucc_le_succ j))]
      ring
    change Var[fun ω ↦ sgn j * (B (τ j.succ) ω - B (τ j.castSucc) ω) ^ 2; P] = _
    rw [variance_const_mul, hsq_sgn, hv_sq]
    dsimp [τ]
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ 1 / 2 * ((u (m + 1) : ℝ) - u m) ^ 2) (2 * n),
    sum_range_two_mul, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  have h2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
  rw [h2, hu_even, hu_odd, hu_even]
  ring

/-- **Biased-clock temporal-midpoint limit.** Along deterministic clock partitions
`A₀ = a n 0 ≤ c n 0 ≤ a n 1 ≤ … ≤ a n (k n) = A₁` whose clock mesh `(a n (i + 1) - a n i)` tends
to zero and whose net half-step clock asymmetry
`1 / 2 * ∑ ((c n i - a n i) - (a n (i + 1) - c n i))` converges to `β`, the intermediate-sample
sums `∑ B(c n i)(B(a n (i + 1)) - B(a n i))` converge in probability to
`(B(A₁)² - B(A₀)²) / 2 + β`. In particular, for a clock splitting every dyadic interval in ratio
`p : (1 - p)` with `p ≠ 1 / 2` and `A₀ < A₁`, the limit shifts from the symmetric Stratonovich
value `(B(A₁)² - B(A₀)²) / 2` by `(p - 1 / 2) * (A₁ - A₀) ≠ 0`. -/
theorem tendstoInMeasure_sum_comp_midpoint_mul_sub (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {A₀ A₁ : ℝ≥0} {k : ι → ℕ} {a c : ι → ℕ → ℝ≥0}
    (ha₀ : ∀ n, a n 0 = A₀) (ha₁ : ∀ n, a n (k n) = A₁)
    (hac : ∀ n, ∀ i < k n, a n i ≤ c n i ∧ c n i ≤ a n (i + 1))
    {δ : ι → ℝ} (hmesh : ∀ n, ∀ i < k n, (a n (i + 1) : ℝ) - a n i ≤ δ n)
    (hδ : Tendsto δ l (𝓝 0))
    {β : ℝ}
    (hβ : Tendsto (fun n ↦ 1 / 2 * ∑ i ∈ range (k n),
      (((c n i : ℝ) - a n i) - ((a n (i + 1) : ℝ) - c n i))) l (𝓝 β)) :
    TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), B (c n i) ω * (B (a n (i + 1)) ω - B (a n i) ω))
      l (fun ω ↦ (B A₁ ω ^ 2 - B A₀ ω ^ 2) / 2 + β) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let D : ι → Ω → ℝ := fun n ω ↦
    (∑ i ∈ range (k n), B (c n i) ω * (B (a n (i + 1)) ω - B (a n i) ω)) -
      (B (a n (k n)) ω ^ 2 - B (a n 0) ω ^ 2) / 2
  let μ : ι → ℝ := fun n ↦
    1 / 2 * ∑ i ∈ range (k n), (((c n i : ℝ) - a n i) - ((a n (i + 1) : ℝ) - c n i))
  have hD_lp (n : ι) : MemLp (D n) 2 P := by
    have hid : D n = fun ω ↦ ∑ i ∈ range (k n),
        1 / 2 * ((B (c n i) ω - B (a n i) ω) ^ 2 -
          (B (a n (i + 1)) ω - B (c n i) ω) ^ 2) := by
      ext ω
      dsimp [D]
      rw [← TauCeti.sum_half_add_mul_sub_id (fun i ↦ B (a n i) ω) (k n), ← sum_sub_distrib]
      refine sum_congr rfl fun _ _ ↦ ?_
      ring
    rw [hid]
    exact memLp_finsetSum (range (k n)) fun i _ ↦
      ((hB.memLp_sq_sub (c n i) (a n i)).sub
        (hB.memLp_sq_sub (a n (i + 1)) (c n i))).const_mul (1 / 2)
  have hvar_le (n : ι) :
      ∫ ω, (D n ω - μ n) ^ 2 ∂P ≤ 1 / 2 * ((A₁ : ℝ) - A₀) * max (δ n) 0 := by
    have hmean : ∫ ω, D n ω ∂P = μ n :=
      hB.integral_sum_comp_midpoint_mul_sub_sub_half_sq (hac n)
    rw [← hmean, ← variance_eq_integral (hD_lp n).aemeasurable,
      hB.variance_sum_comp_midpoint_mul_sub_sub_half_sq (hac n)]
    have hsum : ∑ i ∈ range (k n), (((c n i : ℝ) - a n i) ^ 2 + ((a n (i + 1) : ℝ) - c n i) ^ 2) ≤
        ∑ i ∈ range (k n), ((a n (i + 1) : ℝ) - a n i) * max (δ n) 0 := by
      refine sum_le_sum fun i hi ↦ ?_
      have hi' := mem_range.1 hi
      obtain ⟨h₁, h₂⟩ := hac n i hi'
      have hu0 : 0 ≤ (c n i : ℝ) - a n i := sub_nonneg.2 (NNReal.coe_le_coe.2 h₁)
      have hv0 : 0 ≤ (a n (i + 1) : ℝ) - c n i := sub_nonneg.2 (NNReal.coe_le_coe.2 h₂)
      have hsq1 : ((c n i : ℝ) - a n i) ^ 2 + ((a n (i + 1) : ℝ) - c n i) ^ 2 ≤
          ((a n (i + 1) : ℝ) - a n i) ^ 2 := by nlinarith
      have hsq2 : ((a n (i + 1) : ℝ) - a n i) ^ 2 ≤
          ((a n (i + 1) : ℝ) - a n i) * max (δ n) 0 := by
        rw [sq]
        exact mul_le_mul_of_nonneg_left ((hmesh n i hi').trans (le_max_left _ _)) (by linarith)
      exact hsq1.trans hsq2
    have htel : ∑ i ∈ range (k n), ((a n (i + 1) : ℝ) - a n i) * max (δ n) 0 =
        ((A₁ : ℝ) - A₀) * max (δ n) 0 := by
      rw [← sum_mul, sum_range_sub (fun i ↦ (a n i : ℝ)) (k n), ha₁ n, ha₀ n]
    linarith
  have hD_lim : TendstoInMeasure P D l (fun _ ↦ β) := by
    apply tendstoInMeasure_of_tendsto_integral_norm_sq
    · exact Eventually.of_forall fun n ↦ ((hD_lp n).sub (memLp_const β)).norm.integrable_sq
    · simp only [Real.norm_eq_abs, sq_abs]
      have h1 : Tendsto (fun n ↦ max (δ n) 0) l (𝓝 0) := by
        simpa only [max_self] using hδ.max (tendsto_const_nhds (x := (0 : ℝ)))
      have h2 : Tendsto (fun n ↦ (μ n - β) ^ 2) l (𝓝 0) := by
        have hsub : Tendsto (fun n ↦ μ n - β) l (𝓝 (β - β)) := hβ.sub_const β
        rw [sub_self] at hsub
        have hp := hsub.pow 2
        rwa [zero_pow two_ne_zero] at hp
      have hbound_lim :=
        (h1.const_mul (2 * (1 / 2 * ((A₁ : ℝ) - A₀)))).add (h2.const_mul 2)
      simp only [mul_zero, add_zero] at hbound_lim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_lim
        (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) fun n ↦ ?_
      have hpt : ∀ ω, (D n ω - β) ^ 2 ≤ 2 * (D n ω - μ n) ^ 2 + 2 * (μ n - β) ^ 2 := fun ω ↦ by
        have := sq_nonneg ((D n ω - μ n) - (μ n - β))
        linarith
      have hi1 : Integrable (fun ω ↦ (D n ω - μ n) ^ 2) P :=
        ((hD_lp n).sub (memLp_const (μ n))).integrable_sq
      calc
        ∫ ω, (D n ω - β) ^ 2 ∂P
            ≤ ∫ ω, (2 * (D n ω - μ n) ^ 2 + 2 * (μ n - β) ^ 2) ∂P :=
              integral_mono (((hD_lp n).sub (memLp_const β)).integrable_sq)
                ((hi1.const_mul 2).add (integrable_const _)) hpt
        _ = 2 * (∫ ω, (D n ω - μ n) ^ 2 ∂P) + 2 * (μ n - β) ^ 2 := by
              rw [integral_add (hi1.const_mul 2) (integrable_const _), integral_const_mul,
                integral_const]
              simp
        _ ≤ 2 * (1 / 2 * ((A₁ : ℝ) - A₀)) * max (δ n) 0 + 2 * (μ n - β) ^ 2 := by
              linarith [hvar_le n]
  rw [tendstoInMeasure_iff_norm] at hD_lim ⊢
  intro ε hε
  refine (hD_lim ε hε).congr fun n ↦ ?_
  congr with ω
  dsimp [D]
  rw [ha₁ n, ha₀ n]
  ring_nf

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem grid_mem_Icc {a b : ℝ≥0} {k : ℕ} {π : ℕ → ℝ≥0}
    (hmono : MonotoneOn π (Set.Iic k)) (ha : π 0 = a) (hb : π k = b)
    {i : ℕ} (hi : i ≤ k) : π i ∈ Icc a b :=
  ⟨ha ▸ hmono (Nat.zero_le _) hi (Nat.zero_le _), hb ▸ hmono hi Set.self_mem_Iic hi⟩

private theorem dist_grid_succ_le {k : ℕ} {π : ℕ → ℝ≥0}
    (hmono : MonotoneOn π (Set.Iic k)) {δ : ℝ}
    (hmesh : ∀ i < k, (π (i + 1) : ℝ) - π i ≤ δ)
    {i : ℕ} (hi : i < k) : dist (π (i + 1)) (π i) ≤ δ := by
  rw [NNReal.dist_eq, abs_of_nonneg
    (sub_nonneg.2 (NNReal.coe_le_coe.2 (hmono hi.le hi (Nat.le_succ _))))]
  exact hmesh i hi

private theorem tendstoInMeasure_sq_sum_range (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), (B (π n (i + 1)) ω - B (π n i) ω) ^ 2)
      atTop (fun _ ↦ (b : ℝ) - a) := by
  let grid : ∀ n, Fin (k n + 1) → ℝ≥0 := fun n j ↦ π n j
  have hgrid : ∀ n, Monotone (grid n) := fun n i j hij ↦
    hmono n (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
  have hq := hB.tendstoInMeasure_quadraticSum hgrid
    (fun n ↦ ha n) (fun n ↦ hb n)
    (fun n (i : Fin (k n)) ↦ hmesh n i i.isLt) hδ
  refine hq.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  rw [quadraticSum_def]
  exact Fin.sum_univ_eq_sum_range
    (fun i ↦ (B (π n (i + 1)) ω - B (π n i) ω) ^ 2) (k n)

/-- For any continuous function `g`, the alternating half-step Brownian quadratic sums
`∑ g(B_{t_i}) ((B_{(t_i + t_{i+1}) / 2} - B_{t_i})² - (B_{t_{i+1}} - B_{(t_i + t_{i+1}) / 2})²)`
converge to zero in probability along vanishing-mesh deterministic partitions of `[a, b]`, with no
growth or moment bound on `g`. -/
theorem tendstoInMeasure_sum_mul_midpoint_sq_sub_sq (hB : IsBrownianReal B P)
    {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n), g (B (π n i) ω) *
      ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
        (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))
      atTop (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let trunc (M : ℕ) (y : ℝ) : ℝ := max (-(M : ℝ)) (min (M : ℝ) (g y))
  have htrunc_meas (M : ℕ) : Measurable (trunc M) :=
    (continuous_const.max (continuous_const.min hg)).measurable
  have htrunc_le (M : ℕ) (y : ℝ) : |trunc M y| ≤ M :=
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) M]) (min_le_left _ _)⟩
  have htrunc_eq (M : ℕ) {y : ℝ} (hy : |g y| ≤ M) : trunc M y = g y := by
    obtain ⟨h₁, h₂⟩ := abs_le.1 hy
    simp only [trunc, min_eq_right h₂, max_eq_right h₁]
  let S_trunc (M n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range (k n), trunc M (B (π n i) ω) *
    ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
      (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2)
  have hS_trunc (M : ℕ) : TendstoInMeasure P (S_trunc M) atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_integral_norm_sq
    · refine Eventually.of_forall fun n ↦ ?_
      have hlp : MemLp (S_trunc M n) 2 P := by
        refine memLp_finsetSum (range (k n)) fun i _ ↦ ?_
        have hd : MemLp (fun ω ↦
            (B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
              (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2) 2 P :=
          (hB.toIsPreBrownianReal.memLp_sq_sub _ _).sub
            (hB.toIsPreBrownianReal.memLp_sq_sub _ _)
        have htm : AEStronglyMeasurable
            (fun ω ↦ trunc M (B (π n i) ω) *
              ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
                (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2)) P := by
          simpa only [Pi.mul_def, Function.comp_def] using
            ((htrunc_meas M).aestronglyMeasurable.comp_aemeasurable
              (hB.aemeasurable (π n i))).mul hd.aestronglyMeasurable
        exact hd.of_le_mul (c := (M : ℝ)) htm (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (htrunc_le M _) (abs_nonneg _))
      simpa only [sub_zero] using hlp.norm.integrable_sq
    · simp only [sub_zero, Real.norm_eq_abs, sq_abs]
      have hm0 : Tendsto (fun n ↦ max (δ n) 0) atTop (𝓝 0) := by
        simpa only [max_self] using hδ.max (tendsto_const_nhds (x := (0 : ℝ)))
      have h0 := hm0.const_mul ((M : ℝ) ^ 2 * ((b : ℝ) - a))
      simp only [mul_zero] at h0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) fun n ↦ ?_
      simpa only [S_trunc, hb n, ha n] using
        hB.toIsPreBrownianReal.integral_sq_sum_comp_mul_midpoint_sq_sub_sq_le (hmono n)
          (fun _ _ ↦ htrunc_meas M) (fun _ _ y ↦ htrunc_le M y)
          (fun i hi ↦ (hmesh n i hi).trans (le_max_left _ _))
  let F (M : ℕ) : Set Ω := ⋃ (n : ℕ) (i : Fin (k n)), {ω | (M : ℝ) < |g (B (π n i) ω)|}
  have hF_meas (M : ℕ) : NullMeasurableSet (F M) P :=
    NullMeasurableSet.iUnion fun n ↦ NullMeasurableSet.iUnion fun i ↦
      ((continuous_abs.comp hg).measurable.comp_aemeasurable
        (hB.aemeasurable (π n i))).nullMeasurableSet_preimage measurableSet_Ioi
  have hF_anti : Antitone F := by
    intro M₁ M₂ hle ω hω
    simp only [F, mem_iUnion, mem_ofPred_eq] at hω ⊢
    obtain ⟨n, i, hi⟩ := hω
    exact ⟨n, i, (Nat.cast_le.2 hle).trans_lt hi⟩
  have hF_inter : (⋂ M : ℕ, F M) ⊆ {ω | ¬Continuous (B · ω)} := by
    intro ω hω hc
    obtain ⟨C, hC⟩ :=
      (isCompact_Icc (a := a) (b := b) |>.image ((continuous_abs.comp hg).comp hc)).bddAbove
    obtain ⟨M, hMC⟩ := exists_nat_ge C
    have hM := mem_iInter.1 hω M
    simp only [F, mem_iUnion, mem_ofPred_eq] at hM
    obtain ⟨n, i, hgt⟩ := hM
    have hle : |g (B (π n i) ω)| ≤ M :=
      (hC ⟨π n i, grid_mem_Icc (hmono n) (ha n) (hb n) i.isLt.le, rfl⟩).trans hMC
    exact hgt.not_ge hle
  have hF_inf : ⨅ M : ℕ, P (F M) = 0 := by
    rw [← hF_anti.measure_iInter hF_meas ⟨0, measure_ne_top P _⟩]
    exact measure_mono_null hF_inter (ae_iff.1 hB.cont)
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  rw [← hF_inf, iInf_lt_iff] at hη2
  obtain ⟨M, hFM⟩ := hη2
  have htrunc_ε := (tendstoInMeasure_iff_norm.1 (hS_trunc M)) ε hε
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 htrunc_ε (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsub :
      {ω | ε ≤ ‖(∑ i ∈ range (k n), g (B (π n i) ω) *
        ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
          (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2)) - 0‖} ⊆
      {ω | ε ≤ ‖S_trunc M n ω - 0‖} ∪ F M := by
    intro ω hω
    by_cases hmem : ω ∈ F M
    · exact Or.inr hmem
    · left
      have heq : S_trunc M n ω = ∑ i ∈ range (k n), g (B (π n i) ω) *
          ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
            (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2) := by
        refine sum_congr rfl fun i hi ↦ ?_
        have hi' := mem_range.1 hi
        have hle : |g (B (π n i) ω)| ≤ M := by
          by_contra hlt
          exact hmem (mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨⟨i, hi'⟩, not_le.1 hlt⟩⟩)
        rw [htrunc_eq M hle]
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rwa [heq]
  calc
    P _ ≤ P ({ω | ε ≤ ‖S_trunc M n ω - 0‖} ∪ F M) := measure_mono hsub
    _ ≤ P {ω | ε ≤ ‖S_trunc M n ω - 0‖} + P (F M) := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hN n hn) hFM.le
    _ = η := ENNReal.add_halves η

/-- For a `C¹` function `h`, the cross-increment sums
`∑ (h(B_{t_{i+1}}) - h(B_{t_i}))(B_{t_{i+1}} - B_{t_i})` differ from the left-weighted Brownian
quadratic sums `∑ h'(B_{t_i})(B_{t_{i+1}} - B_{t_i})²` by an error tending to zero in probability
along vanishing-mesh partitions of `[a, b]`. -/
theorem tendstoInMeasure_sum_sub_mul_sub_sub_deriv_mul_sq (hB : IsBrownianReal B P)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦
      (∑ i ∈ range (k n),
        (h (B (π n (i + 1)) ω) - h (B (π n i) ω)) * (B (π n (i + 1)) ω - B (π n i) ω)) -
      ∑ i ∈ range (k n),
        deriv h (B (π n i) ω) * (B (π n (i + 1)) ω - B (π n i) ω) ^ 2)
      atTop (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact TauCeti.Probability.tendstoInMeasure_sum_sub_mul_sub_sub_deriv_mul_sq
    (s := Icc a b) isCompact_Icc hh
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n _ hi ↦ dist_grid_succ_le (hmono n) (hmesh n) hi)
    hδ
    (fun n i _ ↦ (hB.aemeasurable (π n i)).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    (tendstoInMeasure_sq_sum_range hB.toIsPreBrownianReal hmono ha hb hmesh hδ)

/-- **Brownian symmetric-endpoint Stratonovich convergence.** For a `C¹` function `h` with
primitive `H`, along deterministic partitions `a = π n 0 ≤ … ≤ π n (k n) = b` whose mesh tends to
zero, the symmetric-endpoint sums
`∑ (h(B_{t_i}) + h(B_{t_{i+1}})) / 2 * (B_{t_{i+1}} - B_{t_i})` converge in probability to
`H(B_b) - H(B_a)`. -/
theorem tendstoInMeasure_sum_half_add_mul_sub (hB : IsBrownianReal B P)
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        (h (B (π n i) ω) + h (B (π n (i + 1)) ω)) / 2 * (B (π n (i + 1)) ω - B (π n i) ω))
      atTop (fun ω ↦ H (B b ω) - H (B a ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact TauCeti.Probability.tendstoInMeasure_sum_half_add_mul_sub
    (s := Icc a b) isCompact_Icc hh hH ha hb
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n _ hi ↦ dist_grid_succ_le (hmono n) (hmesh n) hi)
    hδ
    (fun n i _ ↦ (hB.aemeasurable (π n i)).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    (tendstoInMeasure_sq_sum_range hB.toIsPreBrownianReal hmono ha hb hmesh hδ)

/-- Perturbing Brownian motion by an almost surely continuous bounded-variation process `A` on
`[a, b]` preserves the symmetric-endpoint Stratonovich chain rule: the symmetric-endpoint sums of
`B + A` converge in probability to `H((B + A)_b) - H((B + A)_a)`, with no integrability or
adaptedness assumption on `A`. -/
theorem tendstoInMeasure_sum_half_add_mul_sub_add_of_boundedVariationOn
    (hB : IsBrownianReal B P) {A : ℝ≥0 → Ω → ℝ}
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hAmeas : ∀ n, ∀ i ≤ k n, AEStronglyMeasurable (A (π n i)) P)
    (hA : ∀ᵐ ω ∂P, ContinuousOn (A · ω) (Icc a b) ∧ BoundedVariationOn (A · ω) (Icc a b)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        (h ((B + A) (π n i) ω) + h ((B + A) (π n (i + 1)) ω)) / 2 *
          ((B + A) (π n (i + 1)) ω - (B + A) (π n i) ω))
      atTop (fun ω ↦ H ((B + A) b ω) - H ((B + A) a ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let grid : ∀ n, Fin (k n + 1) → ℝ≥0 := fun n j ↦ π n j
  have hgrid : ∀ n, Monotone (grid n) := fun n i j hij ↦
    hmono n (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
  have hqv_grid := hB.tendstoInMeasure_quadraticSum_add_of_boundedVariationOn hgrid
    (fun n ↦ ha n) (fun n ↦ hb n)
    (fun n i ↦ dist_grid_succ_le (hmono n) (hmesh n) i.isLt) hδ
    (fun n j ↦ hAmeas n j (Nat.le_of_lt_succ j.isLt)) hA
  have hqv : TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ range (k n), ((B + A) (π n (i + 1)) ω - (B + A) (π n i) ω) ^ 2)
      atTop (fun _ ↦ (b : ℝ) - a) := by
    refine hqv_grid.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
    rw [quadraticSum_def]
    exact Fin.sum_univ_eq_sum_range
      (fun i ↦ ((B + A) (π n (i + 1)) ω - (B + A) (π n i) ω) ^ 2) (k n)
  exact TauCeti.Probability.tendstoInMeasure_sum_half_add_mul_sub
    (s := Icc a b) isCompact_Icc hh hH ha hb
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n _ hi ↦ dist_grid_succ_le (hmono n) (hmesh n) hi)
    hδ
    (fun n i hi ↦ ((hB.aemeasurable (π n i)).aestronglyMeasurable).add (hAmeas n i hi))
    (by
      filter_upwards [hB.cont, hA] with ω hcB hcA
      exact hcB.continuousOn.add hcA.1)
    hqv

/-- **Brownian temporal-midpoint Stratonovich convergence.** For a `C¹` function `h` with primitive
`H`, along deterministic partitions `a = π n 0 ≤ … ≤ π n (k n) = b` whose mesh tends to zero, the
temporal-midpoint sums `∑ h(B_{(t_i + t_{i+1}) / 2}) * (B_{t_{i+1}} - B_{t_i})` converge in
probability to `H(B_b) - H(B_a)`. -/
theorem tendstoInMeasure_sum_midpoint_mul_sub (hB : IsBrownianReal B P)
    {h H : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hH : ∀ y, HasDerivAt H (h y) y)
    {a b : ℝ≥0} {k : ℕ → ℕ} {π : ℕ → ℕ → ℝ≥0}
    (hmono : ∀ n, MonotoneOn (π n) (Set.Iic (k n)))
    (ha : ∀ n, π n 0 = a) (hb : ∀ n, π n (k n) = b)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, (π n (i + 1) : ℝ) - π n i ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
        h (B ((π n i + π n (i + 1)) / 2) ω) * (B (π n (i + 1)) ω - B (π n i) ω))
      atTop (fun ω ↦ H (B b ω) - H (B a ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let u (n j : ℕ) : ℝ≥0 :=
    if j % 2 = 0 then π n (j / 2) else (π n (j / 2) + π n (j / 2 + 1)) / 2
  have hu_even (n i : ℕ) : u n (2 * i) = π n i := by simp [u]
  have hu_odd (n i : ℕ) : u n (2 * i + 1) = (π n i + π n (i + 1)) / 2 := by
    have hdiv : (2 * i + 1) / 2 = i := by omega
    have hmod : (2 * i + 1) % 2 = 1 := by omega
    simp [u, hdiv, hmod]
  have hu_mono (n : ℕ) : MonotoneOn (u n) (Set.Iic (2 * k n)) :=
    monotoneOn_even_odd_Iic fun i hi ↦ nnreal_le_midpoint_and_le (hmono n hi.le hi (Nat.le_succ _))
  have hu_mesh (n : ℕ) : ∀ j < 2 * k n, (u n (j + 1) : ℝ) - u n j ≤ max (δ n) 0 := by
    intro j hj
    have hi : j / 2 < k n := by omega
    have hle : π n (j / 2) ≤ π n (j / 2 + 1) := hmono n hi.le hi (Nat.le_succ _)
    have hm : (π n (j / 2 + 1) : ℝ) - π n (j / 2) ≤ max (δ n) 0 :=
      (hmesh n _ hi).trans (le_max_left _ _)
    rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
    · have hu0 : u n j = π n (j / 2) := by simp [u, hmod]
      have hu1 : u n (j + 1) = (π n (j / 2) + π n (j / 2 + 1)) / 2 := by
        have hdiv1 : (j + 1) / 2 = j / 2 := by omega
        have hmod1 : (j + 1) % 2 = 1 := by omega
        simp [u, hdiv1, hmod1]
      rw [hu1, hu0]
      push_cast
      linarith [NNReal.coe_le_coe.2 hle, le_max_right (δ n) 0]
    · have hu0 : u n j = (π n (j / 2) + π n (j / 2 + 1)) / 2 := by simp [u, hmod]
      have hu1 : u n (j + 1) = π n (j / 2 + 1) := by
        have hdiv1 : (j + 1) / 2 = j / 2 + 1 := by omega
        have hmod1 : (j + 1) % 2 = 0 := by omega
        simp [u, hdiv1, hmod1]
      rw [hu1, hu0]
      push_cast
      linarith [NNReal.coe_le_coe.2 hle, le_max_right (δ n) 0]
  have hδ_max : Tendsto (fun n ↦ max (δ n) 0) atTop (𝓝 0) := by
    simpa only [max_self] using hδ.max (tendsto_const_nhds (x := (0 : ℝ)))
  have hqv_u := tendstoInMeasure_sq_sum_range hB.toIsPreBrownianReal hu_mono
    (fun n ↦ (hu_even n 0).trans (ha n))
    (fun n ↦ (hu_even n (k n)).trans (hb n))
    hu_mesh hδ_max
  have hqv_pair : TendstoInMeasure P (fun n ω ↦ ∑ i ∈ range (k n),
      ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 +
        (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))
      atTop (fun _ ↦ (b : ℝ) - a) := by
    refine hqv_u.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
    rw [sum_range_two_mul]
    refine sum_congr rfl fun i _ ↦ ?_
    have h2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [h2, hu_even, hu_odd, hu_even]
  have hmem_left (n i : ℕ) (hi : i < k n) : π n i ∈ Icc a b :=
    grid_mem_Icc (hmono n) (ha n) (hb n) hi.le
  have hmem_right (n i : ℕ) (hi : i < k n) : π n (i + 1) ∈ Icc a b :=
    grid_mem_Icc (hmono n) (ha n) (hb n) hi
  have hmem_mid (n i : ℕ) (hi : i < k n) : (π n i + π n (i + 1)) / 2 ∈ Icc a b := by
    obtain ⟨h1, h2⟩ := nnreal_le_midpoint_and_le (hmono n hi.le hi (Nat.le_succ _))
    exact ⟨(hmem_left n i hi).1.trans h1, h2.trans (hmem_right n i hi).2⟩
  have hR₁ := TauCeti.Probability.tendstoInMeasure_sum_midpoint_sub_half_add_sub_half_deriv
    (s := Icc a b) isCompact_Icc hh
    (x := π) (z := fun n i ↦ (π n i + π n (i + 1)) / 2) (y := fun n i ↦ π n (i + 1))
    hmem_left hmem_mid hmem_right
    (δ := fun n ↦ max (δ n) 0)
    (fun n i hi ↦ by
      obtain ⟨h1, _⟩ := nnreal_le_midpoint_and_le (hmono n hi.le hi (Nat.le_succ _))
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h1))]
      push_cast
      linarith [hmesh n i hi, NNReal.coe_le_coe.2 h1, le_max_left (δ n) 0, le_max_right (δ n) 0])
    (fun n i hi ↦ by
      obtain ⟨_, h2⟩ := nnreal_le_midpoint_and_le (hmono n hi.le hi (Nat.le_succ _))
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h2))]
      push_cast
      linarith [hmesh n i hi, NNReal.coe_le_coe.2 h2, le_max_left (δ n) 0, le_max_right (δ n) 0])
    hδ_max
    (fun n i _ ↦ (hB.aemeasurable _).aestronglyMeasurable)
    (fun n i _ ↦ (hB.aemeasurable _).aestronglyMeasurable)
    (fun n i _ ↦ (hB.aemeasurable _).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    hqv_pair
  have hR₂ := tendstoInMeasure_const_mul_zero (1 / 2)
    (hB.tendstoInMeasure_sum_mul_midpoint_sq_sub_sq hh.continuous_deriv_one hmono ha hb hmesh hδ)
  have hsym := TauCeti.Probability.tendstoInMeasure_sum_half_add_mul_sub_sub
    (s := Icc a b) isCompact_Icc hh hH
    (fun n _ hi ↦ grid_mem_Icc (hmono n) (ha n) (hb n) hi)
    (fun n _ hi ↦ dist_grid_succ_le (hmono n) (hmesh n) hi)
    hδ
    (fun n i _ ↦ (hB.aemeasurable (π n i)).aestronglyMeasurable)
    (hB.cont.mono fun _ hc ↦ hc.continuousOn)
    (tendstoInMeasure_sq_sum_range hB.toIsPreBrownianReal hmono ha hb hmesh hδ)
  have htot := tendstoInMeasure_add_zero (tendstoInMeasure_add_zero hR₁ hR₂) hsym
  rw [tendstoInMeasure_iff_norm] at htot ⊢
  intro ε hε
  refine (htot ε hε).congr fun n ↦ ?_
  congr with ω
  have halg :
      (∑ i ∈ range (k n),
          h (B ((π n i + π n (i + 1)) / 2) ω) * (B (π n (i + 1)) ω - B (π n i) ω)) -
        (H (B b ω) - H (B a ω)) =
      ((∑ i ∈ range (k n),
        (h (B ((π n i + π n (i + 1)) / 2) ω) * (B (π n (i + 1)) ω - B (π n i) ω) -
          (h (B (π n i) ω) + h (B (π n (i + 1)) ω)) / 2 *
            (B (π n (i + 1)) ω - B (π n i) ω) -
          1 / 2 * deriv h (B (π n i) ω) *
            ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
              (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2))) +
        1 / 2 * ∑ i ∈ range (k n), deriv h (B (π n i) ω) *
          ((B ((π n i + π n (i + 1)) / 2) ω - B (π n i) ω) ^ 2 -
            (B (π n (i + 1)) ω - B ((π n i + π n (i + 1)) / 2) ω) ^ 2)) +
      ((∑ i ∈ range (k n),
          (h (B (π n i) ω) + h (B (π n (i + 1)) ω)) / 2 *
            (B (π n (i + 1)) ω - B (π n i) ω)) -
        (H (B (π n (k n)) ω) - H (B (π n 0) ω))) := by
    rw [hb n, ha n, mul_sum, ← sum_add_distrib]
    have hinner : ∑ x ∈ range (k n),
        (h (B ((π n x + π n (x + 1)) / 2) ω) * (B (π n (x + 1)) ω - B (π n x) ω) -
          (h (B (π n x) ω) + h (B (π n (x + 1)) ω)) / 2 *
            (B (π n (x + 1)) ω - B (π n x) ω) -
          1 / 2 * deriv h (B (π n x) ω) *
            ((B ((π n x + π n (x + 1)) / 2) ω - B (π n x) ω) ^ 2 -
              (B (π n (x + 1)) ω - B ((π n x + π n (x + 1)) / 2) ω) ^ 2) +
          1 / 2 * (deriv h (B (π n x) ω) *
            ((B ((π n x + π n (x + 1)) / 2) ω - B (π n x) ω) ^ 2 -
              (B (π n (x + 1)) ω - B ((π n x + π n (x + 1)) / 2) ω) ^ 2))) =
      (∑ i ∈ range (k n),
        h (B ((π n i + π n (i + 1)) / 2) ω) * (B (π n (i + 1)) ω - B (π n i) ω)) -
      ∑ i ∈ range (k n),
        (h (B (π n i) ω) + h (B (π n (i + 1)) ω)) / 2 *
          (B (π n (i + 1)) ω - B (π n i) ω) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun _ _ ↦ ?_
      ring
    rw [hinner]
    ring
  rw [sub_zero, ← halg]

end ProbabilityTheory.IsBrownianReal
