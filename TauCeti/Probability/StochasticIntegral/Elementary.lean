/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Order.Lattice

/-!
# Bounded elementary predictable integrands

`TauCeti.ElementaryIntegrand` records a finite nondecreasing trading grid and bounded
real positions measurable at the left endpoints. These are presentations, not a quotient
by equality of processes: repeated dates and the empty grid are allowed. The associated
process uses intervals open on the left and closed on the right, and is zero at time zero.

The elementary integral is the existing `TauCeti.Finance.simpleGains`, not a new
integration operator. Its finite-sum formula, path continuity, martingale property and
finite-time Lᵖ membership provide the starting objects for stochastic-integral completion.
Neither completion nor an integral of an arbitrary predictable process is asserted here.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2: elementary predictable processes and their stochastic integrals.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped NNReal ENNReal

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A finite-grid presentation of a bounded elementary real predictable integrand.
The height on `(grid i, grid (i+1)]` is measurable at `grid i`. Boundedness is
pointwise; no probability measure or usual-filtration condition is needed. -/
@[ext]
structure ElementaryIntegrand (ℱ : Filtration ℝ≥0 mΩ) where
  /-- Number of trading intervals. -/
  n : ℕ
  /-- The `n+1` endpoints, including the terminal endpoint. -/
  grid : Fin (n + 1) → ℝ≥0
  /-- Endpoints are nondecreasing; empty intervals are permitted. -/
  monotone_grid : Monotone grid
  /-- The positions on the `n` intervals. -/
  height : Fin n → Ω → ℝ
  /-- Every position is known at its left endpoint. -/
  measurable_height : ∀ i, StronglyMeasurable[ℱ (grid i.castSucc)] (height i)
  /-- Every position is bounded, uniformly over sample points. -/
  bounded_height : ∀ i, ∃ C : ℝ, ∀ ω, |height i ω| ≤ C

namespace ElementaryIntegrand

variable {ℱ : Filtration ℝ≥0 mΩ} (K : ElementaryIntegrand ℱ)

-- The old sum API has natural-number indices. Extend the finite data canonically;
-- these extensions carry no extra data in an elementary-integrand presentation.
private def dates (j : ℕ) : ℝ≥0 := K.grid ⟨min j K.n, by omega⟩

private def positions (j : ℕ) : Ω → ℝ :=
  if h : j < K.n then K.height ⟨j, h⟩ else 0

private theorem monotone_dates : Monotone K.dates := by
  intro i j hij
  exact K.monotone_grid (min_le_min_right _ hij)

private theorem measurable_positions (j : ℕ) (hj : j < K.n) :
    StronglyMeasurable[ℱ (K.dates j)] (K.positions j) := by
  have hd : K.dates j = K.grid (⟨j, hj⟩ : Fin K.n).castSucc := by
    simp [dates, Nat.min_eq_left hj.le, Fin.castSucc]
  rw [hd]
  simpa only [positions, dite_eq_left hj] using K.measurable_height ⟨j, hj⟩

/-- The predictable process represented by the bounded positions and their half-open
trading intervals. It vanishes outside the finite grid. -/
def toProcess : ℝ≥0 → Ω → ℝ :=
  Finance.simpleHolding K.dates K.n K.positions

/-- The elementary integral against an arbitrary real process `X`, with terminal partial
intervals truncated at the evaluation time. -/
def integral (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Finance.simpleGains K.dates K.n K.positions X

/-- Finite-sum formula for the represented predictable process. -/
theorem toProcess_def (t : ℝ≥0) (ω : Ω) :
    K.toProcess t ω = ∑ i : Fin K.n,
      (Set.Ioc (K.grid i.castSucc) (K.grid i.succ)).indicator (fun _ ↦ K.height i ω) t := by
  rw [toProcess, Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp [dates, positions, i.isLt, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]

/-- Finite-sum formula for the elementary integral. -/
theorem integral_def (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    K.integral X t ω = ∑ i : Fin K.n, K.height i ω *
      (X (min (K.grid i.succ) t) ω - X (min (K.grid i.castSucc) t) ω) := by
  rw [integral, Finance.simpleGains_def, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp [dates, positions, i.isLt, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]

/-- On a trading interval the represented process equals its height. -/
theorem toProcess_of_mem_Ioc (i : Fin K.n) {t : ℝ≥0}
    (ht : t ∈ Set.Ioc (K.grid i.castSucc) (K.grid i.succ)) (ω : Ω) :
    K.toProcess t ω = K.height i ω := by
  have ht' : t ∈ Set.Ioc (K.dates i) (K.dates (i + 1)) := by
    simpa [dates, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] using ht
  simpa [toProcess, positions, i.isLt] using
    Finance.simpleHolding_of_mem_Ioc (a := K.positions)
      (K.monotone_dates.monotoneOn _) i.isLt ht' ω

/-- Outside the interval from the first to the last grid point the process vanishes. -/
@[simp]
theorem toProcess_of_notMem_Ioc {t : ℝ≥0}
    (ht : t ∉ Set.Ioc (K.grid 0) (K.grid (Fin.last K.n))) (ω : Ω) :
    K.toProcess t ω = 0 := by
  apply Finance.simpleHolding_of_notMem_Ioc (K.monotone_dates.monotoneOn _)
  simpa [dates, Fin.last] using ht

/-- The elementary integral vanishes up to and including the first grid point. -/
@[simp]
theorem integral_of_le {t : ℝ≥0} (ht : t ≤ K.grid 0)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : K.integral X t ω = 0 := by
  apply Finance.simpleGains_of_le (K.monotone_dates.monotoneOn _)
  simpa [dates] using ht

/-- After the last grid point the elementary integral stays at its terminal value. -/
theorem integral_of_ge {t : ℝ≥0} (ht : K.grid (Fin.last K.n) ≤ t)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    K.integral X t ω = K.integral X (K.grid (Fin.last K.n)) ω := by
  have ht' : K.dates K.n ≤ t := by simpa [dates, Fin.last] using ht
  simpa [integral, dates, Fin.last] using
    Finance.simpleGains_of_ge (a := K.positions) (K.monotone_dates.monotoneOn _) ht' X ω

/-- Elementary integrands are strongly predictable on the original filtration. -/
theorem isStronglyPredictable : IsStronglyPredictable ℱ K.toProcess :=
  Finance.isStronglyPredictable_simpleHolding K.measurable_positions

/-- The represented process has one deterministic bound, independent of time and sample. -/
theorem exists_bound_toProcess : ∃ C : ℝ, ∀ t ω, |K.toProcess t ω| ≤ C := by
  choose C hC using K.bounded_height
  refine ⟨∑ i, |C i|, fun t ω ↦ ?_⟩
  rw [K.toProcess_def]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  by_cases ht : t ∈ Set.Ioc (K.grid i.castSucc) (K.grid i.succ)
  · simpa [ht] using (hC i ω).trans (le_abs_self _)
  · simp [ht]

/-- The holding is zero at the initial time, which belongs to no trading interval. -/
@[simp high]
theorem toProcess_zero (ω : Ω) : K.toProcess 0 ω = 0 := by
  rw [K.toProcess_def]
  exact sum_eq_zero fun i _ ↦ Set.indicator_of_notMem (by simp) _

/-- Every elementary integral starts at zero, even for a nonzero initial integrator. -/
@[simp high]
theorem integral_zero (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : K.integral X 0 ω = 0 := by
  exact K.integral_of_le zero_le X ω

/-- Elementary integration against a continuous path has a continuous path. -/
theorem continuous_integral {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : Continuous (fun t ↦ X t ω)) : Continuous (fun t ↦ K.integral X t ω) := by
  simp_rw [K.integral_def]
  fun_prop

/-- The elementary integral is strongly adapted whenever its integrator is. -/
theorem stronglyAdapted_integral {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X) :
    StronglyAdapted ℱ (K.integral X) :=
  Finance.stronglyAdapted_simpleGains (K.monotone_dates.monotoneOn _) K.measurable_positions hX

/-- Bounded elementary integration preserves the martingale property, without path
regularity or usual conditions on the filtration. -/
theorem martingale_integral {P : Measure Ω} [SigmaFiniteFiltration P ℱ]
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X ℱ P) : Martingale (K.integral X) ℱ P := by
  apply hX.simpleGains_of_bdd (K.monotone_dates.monotoneOn _) K.measurable_positions
  intro j hj
  obtain ⟨C, hC⟩ := K.bounded_height ⟨j, hj⟩
  exact ⟨C, Filter.Eventually.of_forall fun ω ↦ by simpa [positions, hj] using hC ω⟩

/-- Finite-time Lᵖ membership is preserved by elementary integration with bounded heights.
This includes `p = ∞`; only values of the integrator on the truncated finite grid are used. -/
theorem memLp_integral {P : Measure Ω} {p : ℝ≥0∞}
    {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, MemLp (X t) p P) (t : ℝ≥0) :
    MemLp (K.integral X t) p P := by
  have hsum : K.integral X t = fun ω ↦ ∑ i : Fin K.n, K.height i ω *
      (X (min (K.grid i.succ) t) ω - X (min (K.grid i.castSucc) t) ω) :=
    funext (K.integral_def X t)
  rw [hsum]
  apply memLp_finsetSum
  intro i _
  obtain ⟨C, hC⟩ := K.bounded_height i
  have hi : MemLp (K.height i) ∞ P := memLp_top_of_bound
    ((K.measurable_height i).mono (ℱ.le _)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω)
  exact hi.mul ((hX _).sub (hX _))

/-- The empty presentation has no intervals and its sole grid point is zero. -/
instance : Zero (ElementaryIntegrand ℱ) where
  zero :=
    { n := 0
      grid := fun _ ↦ 0
      monotone_grid := monotone_const
      height := Fin.elim0
      measurable_height := fun i ↦ i.elim0
      bounded_height := fun i ↦ i.elim0 }

/-- The empty presentation represents the zero process. -/
@[simp]
theorem toProcess_zero_integrand (t : ℝ≥0) (ω : Ω) :
    (0 : ElementaryIntegrand ℱ).toProcess t ω = 0 := by
  rw [toProcess_def]
  exact Fin.sum_univ_zero _

/-- The elementary integral of the empty presentation is zero. -/
@[simp]
theorem integral_zero_integrand (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (0 : ElementaryIntegrand ℱ).integral X t ω = 0 := by
  rw [integral_def]
  exact Fin.sum_univ_zero _

/-- Scalar multiplication keeps the grid and scales every position. -/
instance : SMul ℝ (ElementaryIntegrand ℱ) where
  smul c K :=
    { n := K.n
      grid := K.grid
      monotone_grid := K.monotone_grid
      height := fun i ω ↦ c * K.height i ω
      measurable_height := fun i ↦ stronglyMeasurable_const.mul (K.measurable_height i)
      bounded_height := fun i ↦ by
        obtain ⟨C, hC⟩ := K.bounded_height i
        exact ⟨|c| * C, fun ω ↦ by
          simpa [abs_mul] using mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩ }

private theorem n_smul (c : ℝ) : (c • K).n = K.n := rfl

private theorem dates_smul (c : ℝ) : (c • K).dates = K.dates := rfl

private theorem positions_smul (c : ℝ) : (c • K).positions = c • K.positions := by
  ext j ω
  by_cases hj : j < K.n
  · simp only [positions, HSMul.hSMul, SMul.smul, hj, dite_true]
    rfl
  · simp only [positions, HSMul.hSMul, SMul.smul, hj, dite_false]
    exact (mul_zero c).symm

/-- Scaling the presentation scales its represented process. -/
@[simp]
theorem toProcess_smul (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    (c • K).toProcess t ω = c * K.toProcess t ω := by
  simpa only [toProcess, n_smul, dates_smul, positions_smul] using
    Finance.simpleHolding_smul K.dates K.n c K.positions t ω

/-- Elementary integration commutes with scaling the positions. -/
@[simp]
theorem integral_smul (c : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (c • K).integral X t ω = c * K.integral X t ω := by
  simpa only [integral, n_smul, dates_smul, positions_smul] using
    Finance.simpleGains_smul K.dates K.n c K.positions X t ω

/-- A one-interval elementary integrand. The height is selected at `s`, not at `t`. -/
def single (s t : ℝ≥0) (hst : s ≤ t) (a : Ω → ℝ)
    (ha : StronglyMeasurable[ℱ s] a) (hb : ∃ C : ℝ, ∀ ω, |a ω| ≤ C) :
    ElementaryIntegrand ℱ where
  n := 1
  grid := ![s, t]
  monotone_grid := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  height := fun _ ↦ a
  measurable_height := fun i ↦ by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ha
  bounded_height := fun _ ↦ hb

/-- A single elementary interval represents exactly its predictable rectangle. -/
@[simp]
theorem toProcess_single (s t : ℝ≥0) (hst : s ≤ t) (a : Ω → ℝ)
    (ha : StronglyMeasurable[ℱ s] a) (hb : ∃ C : ℝ, ∀ ω, |a ω| ≤ C)
    (u : ℝ≥0) (ω : Ω) :
    (single s t hst a ha hb).toProcess u ω = (Set.Ioc s t).indicator (fun _ ↦ a ω) u := by
  simp [toProcess_def, single]

/-- On a single interval the elementary integral is height times the truncated increment. -/
@[simp]
theorem integral_single (s t : ℝ≥0) (hst : s ≤ t) (a : Ω → ℝ)
    (ha : StronglyMeasurable[ℱ s] a) (hb : ∃ C : ℝ, ∀ ω, |a ω| ≤ C)
    (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    (single s t hst a ha hb).integral X u ω = a ω * (X (min t u) ω - X (min s u) ω) := by
  simp [integral_def, single]

end ElementaryIntegrand
end TauCeti
