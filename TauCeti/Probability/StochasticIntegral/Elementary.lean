/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Order.Lattice
public import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# Bounded elementary predictable integrands

`TauCeti.ElementaryIntegrand` records a finite nondecreasing trading grid and bounded
real positions measurable at the left endpoints. These are presentations, not a quotient
by equality of processes: repeated dates and the empty grid are allowed. The associated
process uses intervals open on the left and closed on the right, and is zero at time zero.

The elementary integral is the existing `TauCeti.Finance.simpleGains`, not a new
integration operator. It depends only on the represented process (`integral_congr_toProcess`), and
its finite-sum formula, path continuity, martingale property, finite-time Lᵖ membership, filtration
monotonicity (`monoFiltration`), interval clipping (`clipIocMul`), and construction from bounded
monotone-grid simple holdings (`ofSimpleHolding`) provide the starting objects for
stochastic-integral completion. Neither completion nor an integral of an arbitrary predictable
process is asserted here.

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
The height on `(grid i.castSucc, grid i.succ]` is measurable at `grid i.castSucc`. Boundedness is
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

/-- Canonical extension of `K.grid` to `ℕ`, constant after `K.n`. -/
def dates (j : ℕ) : ℝ≥0 := K.grid ⟨min j K.n, by omega⟩

/-- Canonical extension of `K.height` to `ℕ`, zero at indices `j ≥ K.n`. -/
def positions (j : ℕ) : Ω → ℝ :=
  if h : j < K.n then K.height ⟨j, h⟩ else 0

/-- Beyond `K.n`, `K.dates` stays at the terminal grid point. -/
@[simp]
theorem dates_of_le {j : ℕ} (hj : K.n ≤ j) : K.dates j = K.grid (Fin.last K.n) := by
  simp [dates, Fin.last, min_eq_right hj]

/-- Beyond `K.n`, `K.positions` vanishes. -/
@[simp]
theorem positions_of_le {j : ℕ} (hj : K.n ≤ j) : K.positions j = 0 := by
  simp [positions, not_lt.mpr hj]

/-- On a trading interval index, `K.dates i` is the left endpoint `K.grid i.castSucc`. -/
@[simp]
theorem dates_castSucc (i : Fin K.n) : K.dates i = K.grid i.castSucc := by
  rw [dates]
  congr 1
  ext
  simp

/-- On a trading interval index, `K.dates (i + 1)` is the right endpoint `K.grid i.succ`. -/
@[simp]
theorem dates_succ (i : Fin K.n) : K.dates (i + 1) = K.grid i.succ := by
  simp [dates, Fin.succ]

/-- On a trading interval index, `K.positions i` equals `K.height i`. -/
@[simp]
theorem positions_eq (i : Fin K.n) : K.positions i = K.height i := by
  simp [positions, i.isLt]

/-- The extended grid `K.dates` is monotone. -/
theorem monotone_dates : Monotone K.dates := fun _ _ hij ↦
  K.monotone_grid (min_le_min_right _ hij)

/-- Every extended position `K.positions j` for `j < K.n` is strongly measurable at `K.dates j`. -/
theorem measurable_positions (j : ℕ) (hj : j < K.n) :
    StronglyMeasurable[ℱ (K.dates j)] (K.positions j) := by
  rw [K.dates_castSucc ⟨j, hj⟩, K.positions_eq ⟨j, hj⟩]
  exact K.measurable_height ⟨j, hj⟩

/-- Every extended position `K.positions j` is uniformly bounded. -/
theorem bounded_positions (j : ℕ) : ∃ C : ℝ, ∀ ω, |K.positions j ω| ≤ C := by
  by_cases hj : j < K.n
  · simpa [positions, hj] using K.bounded_height ⟨j, hj⟩
  · exact ⟨0, fun ω ↦ by simp [positions, hj]⟩

/-- All extended positions of an elementary integrand share one deterministic bound. -/
theorem exists_bound_positions : ∃ C : ℝ, ∀ j ω, ‖K.positions j ω‖ ≤ C := by
  choose C hC using K.bounded_positions
  refine ⟨∑ i ∈ range K.n, max (C i) 0, fun j ω ↦ ?_⟩
  by_cases hj : j < K.n
  · rw [Real.norm_eq_abs]
    exact (hC j ω).trans ((le_max_left _ _).trans
      (single_le_sum (fun _ _ ↦ le_max_right _ _) (mem_range.mpr hj)))
  · rw [K.positions_of_le (not_lt.mp hj), Pi.zero_apply, norm_zero]
    exact sum_nonneg fun _ _ ↦ le_max_right _ _

/-- On a finite measure space, every extended position `K.positions j` belongs to `Lᵖ(P)`. -/
theorem memLp_positions (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) (j : ℕ) :
    MemLp (K.positions j) p P := by
  obtain ⟨C, hC⟩ := K.bounded_positions j
  by_cases hj : j < K.n
  · exact MemLp.of_bound
      (((K.measurable_positions j hj).mono (ℱ.le _)).aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω)
  · simp [positions_of_le K (not_lt.mp hj)]

/-- The predictable process represented by the bounded positions and their half-open
trading intervals. It vanishes outside the finite grid. -/
def toProcess : ℝ≥0 → Ω → ℝ :=
  Finance.simpleHolding K.dates K.n K.positions

/-- The elementary integral against an arbitrary real process `X`, with terminal partial
intervals truncated at the evaluation time. -/
def integral (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Finance.simpleGains K.dates K.n K.positions X

/-- `K.toProcess` is `Finance.simpleHolding K.dates K.n K.positions`. -/
theorem toProcess_eq_simpleHolding :
    K.toProcess = Finance.simpleHolding K.dates K.n K.positions := by
  rw [toProcess]

/-- `K.integral X` is `Finance.simpleGains K.dates K.n K.positions X`. -/
theorem integral_eq_simpleGains (X : ℝ≥0 → Ω → ℝ) :
    K.integral X = Finance.simpleGains K.dates K.n K.positions X := by
  rw [integral]

/-- Two elementary integrands that represent the same process have the same elementary integral
against every integrator. -/
theorem integral_congr_toProcess {ℱ 𝒢 : Filtration ℝ≥0 mΩ}
    {K : ElementaryIntegrand ℱ} {L : ElementaryIntegrand 𝒢}
    (hKL : K.toProcess = L.toProcess) (X : ℝ≥0 → Ω → ℝ) :
    K.integral X = L.integral X := by
  let ℱ₀ : Filtration ℝ≥0 mΩ := ⟨fun _ ↦ mΩ, fun _ _ _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  obtain ⟨N, ρ, c, -, hρ, -, hhold, hgain⟩ := Finance.exists_simpleHolding_simpleGains_eq_sub ℱ₀
    (K.monotone_dates.monotoneOn _) (L.monotone_dates.monotoneOn _)
    (fun j hj ↦ (K.measurable_positions j hj).mono (ℱ.le _))
    (fun j hj ↦ (L.measurable_positions j hj).mono (𝒢.le _))
  have hc₀ : ∀ j < N, ∀ ω, c j ω = 0 := by
    intro j hj ω
    have hmem : ρ (j + 1) ∈ Set.Ioc (ρ j) (ρ (j + 1)) :=
      ⟨hρ hj.le hj (Nat.lt_succ_self j), le_rfl⟩
    rw [← Finance.simpleHolding_of_mem_Ioc (a := c) hρ.monotoneOn hj hmem ω, hhold,
      ← toProcess_eq_simpleHolding, ← toProcess_eq_simpleHolding, hKL, sub_self]
  ext t ω
  have hzero : Finance.simpleGains ρ N c X t ω = 0 := by
    rw [Finance.simpleGains_def]
    exact sum_eq_zero fun j hj ↦ by simp [hc₀ j (mem_range.mp hj) ω]
  rw [integral_eq_simpleGains, integral_eq_simpleGains, ← sub_eq_zero, ← hgain, hzero]

/-- Finite-sum formula for the represented predictable process. -/
theorem toProcess_def (t : ℝ≥0) (ω : Ω) :
    K.toProcess t ω = ∑ i : Fin K.n,
      (Set.Ioc (K.grid i.castSucc) (K.grid i.succ)).indicator (fun _ ↦ K.height i ω) t := by
  rw [toProcess, Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ ↦ by rw [K.dates_castSucc i, K.dates_succ i, K.positions_eq i]

/-- Finite-sum formula for the elementary integral. -/
theorem integral_def (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    K.integral X t ω = ∑ i : Fin K.n, K.height i ω *
      (X (min (K.grid i.succ) t) ω - X (min (K.grid i.castSucc) t) ω) := by
  rw [integral, Finance.simpleGains_def, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ ↦ by rw [K.dates_castSucc i, K.dates_succ i, K.positions_eq i]

/-- On a trading interval the represented process equals its height. -/
theorem toProcess_of_mem_Ioc (i : Fin K.n) {t : ℝ≥0}
    (ht : t ∈ Set.Ioc (K.grid i.castSucc) (K.grid i.succ)) (ω : Ω) :
    K.toProcess t ω = K.height i ω := by
  have ht' : t ∈ Set.Ioc (K.dates i) (K.dates (i + 1)) := by
    rwa [K.dates_castSucc i, K.dates_succ i]
  simpa [toProcess, K.positions_eq i] using
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

/-- Enlarging the filtration on the same measurable space preserves `ElementaryIntegrand`. -/
def monoFiltration {𝒢 : Filtration ℝ≥0 mΩ} (hℱ𝒢 : ℱ ≤ 𝒢) : ElementaryIntegrand 𝒢 where
  n := K.n
  grid := K.grid
  monotone_grid := K.monotone_grid
  height := K.height
  measurable_height i := (K.measurable_height i).mono (hℱ𝒢 _)
  bounded_height := K.bounded_height

/-- Enlarging the filtration does not change the represented process. -/
@[simp]
theorem toProcess_monoFiltration {𝒢 : Filtration ℝ≥0 mΩ} (hℱ𝒢 : ℱ ≤ 𝒢) :
    (K.monoFiltration hℱ𝒢).toProcess = K.toProcess := by
  ext t ω
  simp [toProcess_def, monoFiltration]

/-- Enlarging the filtration does not change the elementary integral. -/
@[simp]
theorem integral_monoFiltration {𝒢 : Filtration ℝ≥0 mΩ} (hℱ𝒢 : ℱ ≤ 𝒢) (X : ℝ≥0 → Ω → ℝ) :
    (K.monoFiltration hℱ𝒢).integral X = K.integral X := by
  ext t ω
  simp [integral_def, monoFiltration]

/-- Construct a bounded `ElementaryIntegrand` from a bounded monotone-grid simple holding,
preserving both the represented process and every elementary integral. -/
def ofSimpleHolding {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∃ C : ℝ, ∀ ω, |a j ω| ≤ C) : ElementaryIntegrand ℱ where
  n := n
  grid i := τ i
  monotone_grid i j hij := hτ (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) hij
  height i := a i
  measurable_height i := ha i i.isLt
  bounded_height i := hb i i.isLt

/-- `ofSimpleHolding` preserves the interval count `n`. -/
@[simp]
theorem ofSimpleHolding_n {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∃ C : ℝ, ∀ ω, |a j ω| ≤ C) :
    (ofSimpleHolding hτ ha hb).n = n := by
  rw [ofSimpleHolding]

/-- `ofSimpleHolding` preserves the represented process pointwise. -/
@[simp]
theorem toProcess_ofSimpleHolding {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∃ C : ℝ, ∀ ω, |a j ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    (ofSimpleHolding hτ ha hb).toProcess t ω = Finance.simpleHolding τ n a t ω := by
  rw [toProcess_eq_simpleHolding, Finance.simpleHolding_def, Finance.simpleHolding_def,
    ofSimpleHolding_n]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j < n := mem_range.mp hj
  simp [dates, positions, ofSimpleHolding, hj', Nat.min_eq_left hj'.le]

/-- `ofSimpleHolding` preserves elementary integrals pointwise. -/
@[simp]
theorem integral_ofSimpleHolding {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∃ C : ℝ, ∀ ω, |a j ω| ≤ C) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (ofSimpleHolding hτ ha hb).integral X t ω = Finance.simpleGains τ n a X t ω := by
  rw [integral_eq_simpleGains, Finance.simpleGains_def, Finance.simpleGains_def,
    ofSimpleHolding_n]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j < n := mem_range.mp hj
  simp [dates, positions, ofSimpleHolding, hj', Nat.min_eq_left hj'.le]

/-- The empty presentation has no intervals and its sole grid point is zero. -/
instance : Zero (ElementaryIntegrand ℱ) where
  zero :=
    { n := 0
      grid := 0
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

/-- The sum of two elementary integrands can be represented on a common grid by a single
`ElementaryIntegrand` whose represented process and elementary integrals are the pointwise sums. -/
theorem exists_toProcess_add_integral_add (K L : ElementaryIntegrand ℱ) :
    ∃ M : ElementaryIntegrand ℱ,
      M.toProcess = K.toProcess + L.toProcess ∧
      ∀ X : ℝ≥0 → Ω → ℝ, M.integral X = K.integral X + L.integral X := by
  classical
  let s := (range K.n).disjSum (range L.n)
  let l := Sum.elim K.dates L.dates
  let u := Sum.elim (fun j ↦ K.dates (j + 1)) fun j ↦ L.dates (j + 1)
  let a := Sum.elim K.positions L.positions
  have ha : ∀ i ∈ s, StronglyMeasurable[ℱ (l i)] (a i) := by
    rintro (j | j) hj <;> simp only [s, inl_mem_disjSum, inr_mem_disjSum, mem_range] at hj
    · exact K.measurable_positions j hj
    · exact L.measurable_positions j hj
  obtain ⟨n, τ, b, -, hτ, -, -, hb_meas, -, hb_bdd, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ s l u a ha
  obtain ⟨CK, hCK⟩ := K.exists_bound_positions
  obtain ⟨CL, hCL⟩ := L.exists_bound_positions
  have hb_unif : ∀ j < n, ∃ C : ℝ, ∀ ω, |b j ω| ≤ C := fun j hj ↦ by
    refine ⟨(K.n : ℝ) * CK + (L.n : ℝ) * CL, fun ω ↦ ?_⟩
    refine (hb_bdd j hj ω).trans ?_
    simp only [s, a, sum_disjSum, Sum.elim_inl, Sum.elim_inr]
    exact add_le_add
      ((sum_le_sum fun i _ ↦ hCK i ω).trans_eq (by simp [nsmul_eq_mul]))
      ((sum_le_sum fun i _ ↦ hCL i ω).trans_eq (by simp [nsmul_eq_mul]))
  refine ⟨ofSimpleHolding hτ.monotoneOn (fun j _ ↦ hb_meas j) hb_unif, ?_, fun X ↦ ?_⟩
  · ext t ω
    rw [toProcess_ofSimpleHolding, hhold t ω, sum_disjSum]
    simp only [l, u, a, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, toProcess_eq_simpleHolding,
      Finance.simpleHolding_def]
  · ext t ω
    rw [integral_ofSimpleHolding, hgain X t ω, sum_disjSum]
    simp only [l, u, a, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, integral_eq_simpleGains,
      Finance.simpleGains_def]
    congr 1 <;> refine sum_congr rfl fun j _ ↦ ?_
    · simp [K.monotone_dates (Nat.le_succ j)]
    · simp [L.monotone_dates (Nat.le_succ j)]

/-- Clip a bounded `ElementaryIntegrand` to `(s, t]` and multiply by a bounded
`ℱ s`-measurable random variable `ξ`. -/
def clipIocMul {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    ElementaryIntegrand ℱ :=
  ofSimpleHolding (τ := fun j ↦ (Set.projIcc s t hst (K.dates j) : ℝ≥0))
    (((Subtype.mono_coe _).comp (Set.monotone_projIcc hst)).comp_monotoneOn
      (K.monotone_dates.monotoneOn _))
    (Finance.stronglyMeasurable_clip_Ioc_mul ℱ K.measurable_positions hst hξ)
    fun j _ ↦ by
      obtain ⟨C, hC⟩ := K.exists_bound_positions
      refine ⟨max Cξ 0 * max C 0, fun ω ↦ ?_⟩
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul ((hCξ ω).trans (le_max_left _ _))
          ((Real.norm_eq_abs _ ▸ hC j ω).trans (le_max_left _ _))
          (abs_nonneg _) (le_max_right _ _)
      · rw [abs_zero]
        exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

/-- Clipping an elementary integrand to `(s, t]` and multiplying by `ξ` multiplies its
represented process by `1_{(s, t]} · ξ`. -/
@[simp]
theorem toProcess_clipIocMul {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ)
    (u : ℝ≥0) (ω : Ω) :
    (K.clipIocMul hst hξ hCξ).toProcess u ω =
      if s < u ∧ u ≤ t then ξ ω * K.toProcess u ω else 0 := by
  rw [clipIocMul, toProcess_ofSimpleHolding, toProcess_eq_simpleHolding]
  simpa only [Set.indicator_apply, Set.mem_Ioc] using Finance.simpleHolding_clip_Ioc_mul hst ξ u ω

/-- Clipping an elementary integrand to `(s, t]` and multiplying by `ξ` multiplies the `(s, t]`
increment of its elementary integral by `ξ`. -/
@[simp]
theorem integral_clipIocMul {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    (K.clipIocMul hst hξ hCξ).integral X T ω =
      ξ ω * (K.integral X (min T t) ω - K.integral X (min T s) ω) := by
  rw [clipIocMul, integral_ofSimpleHolding, integral_eq_simpleGains]
  exact Finance.simpleGains_clip_Ioc_mul (K.monotone_dates.monotoneOn _) hst ξ X T ω

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
