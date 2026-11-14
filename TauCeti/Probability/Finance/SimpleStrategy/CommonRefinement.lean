/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# Simultaneous refinement of elementary holdings

A finite family of elementary predictable holdings admits one strictly increasing trading
grid. Refinement preserves each holding separately and its gains against every price path,
not just their sum. Evaluating the refined holding at each new right endpoint shows that any
almost-sure uniform bound on an individual holding survives unchanged; it is not replaced by
a sum of bounds over all the old trading intervals.

This permits comparison of bounded elementary stochastic-integral approximations on different
grids using estimates stated on a common grid. The construction tags each strategy with a
separate sample-space coordinate and applies the scalar interval-refinement theorem once.
There are no probability, path-continuity, or moment assumptions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §§3.2 and 3.5.
-/

public section

noncomputable section

open Finset MeasureTheory Set TauCeti.Finance

namespace MeasureTheory.Filtration

variable {Ω ι κ : Type*} [LinearOrder ι] [OrderBot ι] [Finite κ]

/-- Several elementary predictable holdings can be put on one strictly increasing grid,
with their individual gains unchanged against every price path.
Empty grids, repeated original dates and nonzero original initial dates are allowed. -/
theorem exists_common_simpleHolding_simpleGains {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (n : κ → ℕ) (τ : κ → ℕ → ι) (a : κ → ℕ → Ω → ℝ)
    (hτ : ∀ k, MonotoneOn (τ k) (Set.Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) :
    ∃ (N : ℕ) (σ : ℕ → ι) (b : κ → ℕ → Ω → ℝ),
      σ 0 = ⊥ ∧ StrictMonoOn σ (Set.Iic N) ∧
      (∀ k j, j < N → StronglyMeasurable[ℱ (σ j)] (b k j)) ∧
      (∀ k t ω, simpleHolding σ N (b k) t ω = simpleHolding (τ k) (n k) (a k) t ω) ∧
      ∀ k (X : ι → Ω → ℝ) t ω,
        simpleGains σ N (b k) X t ω = simpleGains (τ k) (n k) (a k) X t ω := by
  classical
  let := Fintype.ofFinite κ
  let : MeasurableSpace κ := ⊤
  let 𝒢 : Filtration ι (inferInstance : MeasurableSpace (κ × Ω)) :=
    ⟨fun t ↦ (⊤ : MeasurableSpace κ).prod (ℱ t),
      fun _ _ h ↦ MeasurableSpace.prod_mono le_rfl (ℱ.mono h),
      fun t ↦ MeasurableSpace.prod_mono le_rfl (ℱ.le t)⟩
  let s : Finset (Σ _ : κ, ℕ) := univ.sigma fun k ↦ range (n k)
  let c (i : Σ _ : κ, ℕ) (p : κ × Ω) := if p.1 = i.1 then a i.1 i.2 p.2 else 0
  obtain ⟨N, σ, b, hzero, hσ, hb, -, hhold, hgain⟩ :=
    exists_simpleHolding_simpleGains_eq_sum 𝒢 s
      (fun i ↦ τ i.1 i.2) (fun i ↦ τ i.1 (i.2 + 1)) c (by
        intro i hi
        exact ((ha i.1 i.2 (by simpa [s] using hi)).comp_measurable measurable_snd).ite
          ((MeasurableSet.of_discrete : MeasurableSet {k : κ | k = i.1}).preimage measurable_fst)
          stronglyMeasurable_const)
  have hhold' (k : κ) (t : ι) (ω : Ω) :
      simpleHolding σ N (fun j ω ↦ b j (k, ω)) t ω =
        simpleHolding (τ k) (n k) (a k) t ω := by
    calc
      _ = ∑ i ∈ s, (Set.Ioc (τ i.1 i.2) (τ i.1 (i.2 + 1))).indicator
          (fun _ ↦ c i (k, ω)) t := by
        simpa only [simpleHolding_def] using hhold t (k, ω)
      _ = _ := by
        simp only [s, sum_sigma]
        rw [sum_eq_single k]
        · simp [c, simpleHolding_def]
        · intro l _ hl
          exact sum_eq_zero fun j _ ↦ by simp [c, Ne.symm hl]
        · simp
  refine ⟨N, σ, fun k j ω ↦ b j (k, ω), hzero, hσ,
    fun k j hj ↦ (hb j hj).comp_measurable (measurable_const.prodMk measurable_id),
    hhold', ?_⟩
  intro k X t ω
  calc
    _ = ∑ i ∈ s, if τ i.1 i.2 ≤ τ i.1 (i.2 + 1) then
        c i (k, ω) * (X (min (τ i.1 (i.2 + 1)) t) ω - X (min (τ i.1 i.2) t) ω)
        else 0 := by
      simpa only [simpleGains_def] using hgain (fun t p ↦ X t p.2) t (k, ω)
    _ = _ := by
      simp only [s, sum_sigma]
      rw [sum_eq_single k, simpleGains_def]
      · apply sum_congr rfl
        intro j hj
        rw [ite_eq_left (hτ k (mem_range.mp hj).le (mem_range.mp hj) (Nat.le_succ j))]
        simp [c]
      · intro l _ hl
        exact sum_eq_zero fun j _ ↦ by simp [c, Ne.symm hl]
      · simp

/-- Simultaneous refinement preserves separate almost-sure uniform bounds, including bounds
that depend on the strategy and the sample. The new heights need satisfy their bounds only
on the active finite grid; no hypothesis is made on unused original heights. -/
theorem exists_common_simpleHolding_simpleGains_of_bound {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (P : Measure Ω) (n : κ → ℕ) (τ : κ → ℕ → ι)
    (a : κ → ℕ → Ω → ℝ) (K : κ → Ω → ℝ)
    (hτ : ∀ k, MonotoneOn (τ k) (Set.Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j))
    (hK : ∀ k, ∀ᵐ ω ∂P, ∀ t, |simpleHolding (τ k) (n k) (a k) t ω| ≤ K k ω) :
    ∃ (N : ℕ) (σ : ℕ → ι) (b : κ → ℕ → Ω → ℝ),
      σ 0 = ⊥ ∧ StrictMonoOn σ (Set.Iic N) ∧
      (∀ k j, j < N → StronglyMeasurable[ℱ (σ j)] (b k j)) ∧
      (∀ k, ∀ᵐ ω ∂P, ∀ j < N, |b k j ω| ≤ K k ω) ∧
      (∀ k t ω, simpleHolding σ N (b k) t ω = simpleHolding (τ k) (n k) (a k) t ω) ∧
      ∀ k (X : ι → Ω → ℝ) t ω,
        simpleGains σ N (b k) X t ω = simpleGains (τ k) (n k) (a k) X t ω := by
  obtain ⟨N, σ, b, hzero, hσ, hb, hhold, hgain⟩ :=
    exists_common_simpleHolding_simpleGains ℱ n τ a hτ ha
  refine ⟨N, σ, b, hzero, hσ, hb, ?_, hhold, hgain⟩
  intro k
  filter_upwards [hK k] with ω hω j hj
  have heq := hhold k (σ (j + 1)) ω
  rw [simpleHolding_of_mem_Ioc hσ.monotoneOn hj
    ⟨hσ hj.le hj (Nat.lt_succ_self j), le_rfl⟩] at heq
  exact heq.symm ▸ hω (σ (j + 1))

end MeasureTheory.Filtration
