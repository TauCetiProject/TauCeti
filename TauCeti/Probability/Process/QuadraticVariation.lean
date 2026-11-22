/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import TauCeti.Analysis.QuadraticSums.BoundedVariation

/-!
# Quadratic sums and continuous finite-variation perturbations

The quadratic sum of a real process is its sum of squared increments along a finite grid.
Repeated dates and grids with no intervals are allowed.

Adding a continuous finite-variation process to a continuous real process does not change
its partition quadratic-variation limit in probability. The pathwise difference of quadratic
sums tends to zero: both the cross term and the finite-variation square term vanish.
This separates the finite-variation part of a continuous semimartingale from the part
contributing to its quadratic variation.

The result concerns deterministic partitions and their limits, not construction of a bracket.
It requires neither adaptation nor a martingale hypothesis. Path regularity and finite variation
hold outside a common sample-null set; no moment bound on total variation is assumed.

Also provides reusable increment estimates for bounded and dominated processes: almost-sure bounds
on differences (`MeasureTheory.ae_norm_sub_le`, `MeasureTheory.ae_sq_sub_le`), `Lᵖ` membership of
bounded squared increments (`MeasureTheory.memLp_sub_sq_of_bound`) and quadratic sums
(`TauCeti.Probability.memLp_quadraticSum_of_bound`,
`TauCeti.Probability.ae_quadraticSum_le_of_bound`), and integrability of dominated strongly
adapted increments (`MeasureTheory.StronglyAdapted.integrable_sub_of_bound` and
`MeasureTheory.StronglyAdapted.integrable_sub_of_nonneg_le`).

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Chapter IV, §1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

/-- If two functions are almost surely bounded in norm by `R₁` and `R₂`, then their difference is
almost surely bounded in norm by `R₁ + R₂`. -/
theorem ae_norm_sub_le {Ω E : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [SeminormedAddCommGroup E] {f g : Ω → E} {R₁ R₂ : ℝ}
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R₁) (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ R₂) :
    ∀ᵐ ω ∂μ, ‖f ω - g ω‖ ≤ R₁ + R₂ :=
  hf.mp <| hg.mono fun _ h2 h1 ↦ (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- If two real functions are almost surely bounded in absolute value by `R`, then their squared
difference is almost surely bounded by `(2 * R) ^ 2`. -/
theorem ae_sq_sub_le {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} {R : ℝ} (hf : ∀ᵐ ω ∂μ, |f ω| ≤ R) (hg : ∀ᵐ ω ∂μ, |g ω| ≤ R) :
    ∀ᵐ ω ∂μ, (f ω - g ω) ^ 2 ≤ (2 * R) ^ 2 :=
  (ae_norm_sub_le (f := f) (g := g) (R₁ := R) (R₂ := R)
      (hf.mono fun _ h ↦ by rwa [Real.norm_eq_abs])
      (hg.mono fun _ h ↦ by rwa [Real.norm_eq_abs])).mono fun _ hω ↦ by
    rw [Real.norm_eq_abs, ← two_mul] at hω
    rw [← sq_abs]
    gcongr

/-- Under a finite measure, the squared difference of two almost-surely bounded measurable real
functions lies in `Lᵖ` for every `p`. -/
theorem memLp_sub_sq_of_bound {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f g : Ω → ℝ} {R : ℝ} (p : ℝ≥0∞)
    (hf_m : AEStronglyMeasurable f μ) (hg_m : AEStronglyMeasurable g μ)
    (hf_bd : ∀ᵐ ω ∂μ, |f ω| ≤ R) (hg_bd : ∀ᵐ ω ∂μ, |g ω| ≤ R) :
    MemLp (fun ω ↦ (f ω - g ω) ^ 2) p μ :=
  MemLp.of_bound ((hf_m.sub hg_m).pow 2) ((2 * R) ^ 2)
    ((ae_sq_sub_le hf_bd hg_bd).mono fun _ hω ↦ by
      rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])

/-- An increment of a strongly adapted process dominated almost surely by a constant is integrable
under any finite measure. -/
theorem StronglyAdapted.integrable_sub_of_bound {ι Ω E : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] [NormedAddCommGroup E]
    {ℱ : Filtration ι mΩ} {X : ι → Ω → E} (hX : StronglyAdapted ℱ X) {u v : ι} {C : ℝ}
    (hbd : ∀ᵐ ω ∂μ, ‖X v ω - X u ω‖ ≤ C) :
    Integrable (fun ω ↦ X v ω - X u ω) μ :=
  (integrable_const C).mono'
    (((hX v).mono (ℱ.le v)).sub ((hX u).mono (ℱ.le u))).aestronglyMeasurable hbd

/-- A nonnegative real increment of a strongly adapted process bounded almost surely by a constant
is integrable under any finite measure. -/
theorem StronglyAdapted.integrable_sub_of_nonneg_le {ι Ω : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ}
    {A : ι → Ω → ℝ} (hA : StronglyAdapted ℱ A) {u v : ι} {C : ℝ}
    (hbd : ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ C) :
    Integrable (fun ω ↦ A v ω - A u ω) μ :=
  hA.integrable_sub_of_bound <| hbd.mono fun _ hω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2

end MeasureTheory

namespace TauCeti.Probability

/-- The sum of squared increments of a real process along a finite grid. -/
def quadraticSum {Ω : Type*} {n : ℕ} (B : ℝ≥0 → Ω → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin n, (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2

theorem quadraticSum_def {Ω : Type*} {n : ℕ} (B : ℝ≥0 → Ω → ℝ)
    (t : Fin (n + 1) → ℝ≥0) :
    quadraticSum B t = fun ω ↦ ∑ i : Fin n, (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2 :=
  (rfl)

/-- A grid with no intervals has zero quadratic sum. -/
@[simp]
theorem quadraticSum_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : Fin 1 → ℝ≥0) :
    quadraticSum B t = 0 := by
  ext ω
  simp [quadraticSum_def]

/-- Quadratic sums are nonnegative, independently of the order of the grid. -/
theorem quadraticSum_nonneg {Ω : Type*} {n : ℕ} (B : ℝ≥0 → Ω → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (ω : Ω) : 0 ≤ quadraticSum B t ω :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Under a finite measure, the quadratic sum of a process whose grid values are measurable and
almost surely bounded by `R` lies in `Lᵖ` for every `p`. -/
theorem memLp_quadraticSum_of_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (p : ℝ≥0∞) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (hX : ∀ k, AEStronglyMeasurable (X (t k)) μ)
    (hXR : ∀ k, ∀ᵐ ω ∂μ, |X (t k) ω| ≤ R) :
    MemLp (quadraticSum X t) p μ := by
  rw [quadraticSum_def]
  exact memLp_finsetSum _ fun k _ ↦
    memLp_sub_sq_of_bound p (hX k.succ) (hX k.castSucc) (hXR k.succ) (hXR k.castSucc)

/-- If the grid values of `X` are almost surely bounded in absolute value by `R`, then the
quadratic sum along `t : Fin (n + 1) → ℝ≥0` is almost surely at most `n * (2 * R) ^ 2`. -/
theorem ae_quadraticSum_le_of_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (hXR : ∀ k, ∀ᵐ ω ∂μ, |X (t k) ω| ≤ R) :
    ∀ᵐ ω ∂μ, quadraticSum X t ω ≤ (n : ℝ) * (2 * R) ^ 2 := by
  rw [quadraticSum_def]
  refine (ae_all_iff.2 fun k : Fin n ↦ ae_sq_sub_le (hXR k.succ) (hXR k.castSucc)).mono
    fun ω hω ↦ (Finset.sum_le_sum fun k _ ↦ hω k).trans_eq (by simp)

variable {Ω : Type*} {X A : ℝ≥0 → Ω → ℝ} {s : Set ℝ≥0}

private theorem tendsto_quadraticSum_add_sub {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    {grid : ∀ k, Fin (N k + 1) → ℝ≥0} (hgrid : ∀ k, Monotone (grid k))
    (hmem : ∀ k i, grid k i ∈ s) {δ : ι → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) {ω : Ω} (hA : BoundedVariationOn (A · ω) s)
    (hcA : UniformContinuousOn (A · ω) s) (hcX : UniformContinuousOn (X · ω) s) :
    Tendsto (fun k ↦ quadraticSum (X + A) (grid k) ω - quadraticSum X (grid k) ω)
      l (𝓝 0) := by
  -- Extend a finite grid constantly to use the existing natural-index pathwise estimate.
  let u (k : ι) (j : ℕ) :=
    grid k ⟨min j (N k), Nat.lt_succ_of_le (Nat.min_le_right j (N k))⟩
  have hu (k : ι) : MonotoneOn (u k) (Iic (N k)) :=
    fun i _ j _ hij ↦ hgrid k (min_le_min_right (N k) hij)
  have hleft (k : ι) (i : Fin (N k)) : u k i = grid k i.castSucc := by
    simp only [u, min_eq_left (Nat.le_of_lt i.isLt)]
    rfl
  have hright (k : ι) (i : Fin (N k)) : u k (i + 1) = grid k i.succ := by
    simp only [u, min_eq_left (Nat.succ_le_of_lt i.isLt)]
    rfl
  have hmesh' (k : ι) (i : ℕ) (hi : i < N k) :
      dist (u k (i + 1)) (u k i) ≤ δ k := by
    simpa only [hright k ⟨i, hi⟩, hleft k ⟨i, hi⟩] using hmesh k ⟨i, hi⟩
  have hlim := hcX.tendsto_sum_sq_add_sub_of_boundedVariationOn hcA hA hu
    (fun k i _ ↦ hmem k _) hmesh' hδ
  simpa only [← Fin.sum_univ_eq_sum_range, hleft, hright, quadraticSum_def,
    Pi.add_apply] using hlim

/-- A continuous finite-variation perturbation preserves any quadratic-sum limit in
probability. Both processes need only have measurable values at the grid dates. -/
theorem tendstoInMeasure_quadraticSum_add {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hs : IsCompact s) {N : ℕ → ℕ}
    {grid : ∀ k, Fin (N k + 1) → ℝ≥0} (hgrid : ∀ k, Monotone (grid k))
    (hmem : ∀ k i, grid k i ∈ s) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hXmeas : ∀ k i, AEStronglyMeasurable (X (grid k i)) P)
    (hAmeas : ∀ k i, AEStronglyMeasurable (A (grid k i)) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s ∧ ContinuousOn (A · ω) s ∧
      BoundedVariationOn (A · ω) s)
    {V : Ω → ℝ} (hV : TendstoInMeasure P (fun k ↦ quadraticSum X (grid k)) atTop V) :
    TendstoInMeasure P (fun k ↦ quadraticSum (X + A) (grid k)) atTop V := by
  have hmeas (k : ℕ) : AEStronglyMeasurable (quadraticSum (X + A) (grid k)) P := by
    rw [quadraticSum_def]
    simpa only [Finset.sum_fn, Pi.pow_apply, Pi.sub_apply, Pi.add_apply] using
      Finset.aestronglyMeasurable_sum Finset.univ (fun (i : Fin (N k)) _ ↦
        (((hXmeas k i.succ).add (hAmeas k i.succ)).sub
          ((hXmeas k i.castSucc).add (hAmeas k i.castSucc))).pow 2)
  have herr : ∀ᵐ ω ∂P, Tendsto (fun k ↦
      quadraticSum (X + A) (grid k) ω - quadraticSum X (grid k) ω) atTop (𝓝 0) := by
    filter_upwards [hcont] with ω hω
    exact tendsto_quadraticSum_add_sub hgrid hmem hmesh hδ hω.2.2
      (hs.uniformContinuousOn_of_continuous hω.2.1)
      (hs.uniformContinuousOn_of_continuous hω.1)
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).2
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hV.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [herr, hlim] with ω he hv
  have he' := he.comp (hns.comp hms).tendsto_atTop
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using he'.add hv

end TauCeti.Probability
