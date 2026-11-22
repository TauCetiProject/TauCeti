/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping compatibility of L² Brownian Itô integrals

Against an almost surely continuous filtered pre-Brownian motion `W`, stopping the Itô integral
process of a `BrownianIntegrable` integrand `H` at any stopping time `τ` on a raw filtration
produces an Itô integral of the cutoff integrand `1_{[0, τ]} · H`
(`isItoIntegral_stoppedProcess_of_brownianIntegrable`), and at every deterministic horizon `T` the
stopped integral agrees almost surely with `hW.l2Integral T` evaluated on `1_{[0, τ]} · H`
(`stoppedProcess_ae_eq_l2Integral`).

The proof first realizes stopping of any bounded simple holding at an upward dyadic stopping time
`dyadicCeilTime k ∘ τ` as an exact bounded simple holding on a refined dyadic grid, passes to
the `L²` limit via uniform approximation (`exists_seq_simpleHolding_tendstoUniformlyOn`), and
then sends the dyadic mesh `2⁻ᵏ → 0` via path continuity of the integral and dominated convergence
in `L²`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–D.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The dyadic grid of mesh `2⁻ᵏ` clipped to the interval `[s, b]`. -/
private def clippedDyadicGrid (s b : ℝ≥0) (k j : ℕ) : ℝ≥0 := min b (max s ((j : ℝ≥0) / 2 ^ k))

private theorem clippedDyadicGrid_mono (s b : ℝ≥0) (k : ℕ) : Monotone (clippedDyadicGrid s b k) :=
  fun _ _ hij ↦ min_le_min_left b (max_le_max_left s
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)))

private theorem clippedDyadicGrid_zero {s b : ℝ≥0} (hsb : s ≤ b) (k : ℕ) :
    clippedDyadicGrid s b k 0 = s := by
  simp [clippedDyadicGrid, hsb]

private theorem le_clippedDyadicGrid {s b : ℝ≥0} (hsb : s ≤ b) (k j : ℕ) :
    s ≤ clippedDyadicGrid s b k j := le_min hsb (le_max_left _ _)

private theorem clippedDyadicGrid_le (s b : ℝ≥0) (k j : ℕ) : clippedDyadicGrid s b k j ≤ b :=
  min_le_left _ _

private theorem clippedDyadicGrid_end (s b : ℝ≥0) (k : ℕ) :
    clippedDyadicGrid s b k (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1) = b :=
  min_eq_left <| le_max_of_le_right <| le_of_lt <| (lt_div_iff₀ (by positivity)).mpr <| by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (b * (2 : ℝ≥0) ^ k)

/-- No upward dyadic rounding `dyadicCeilTime k u` lies strictly inside a consecutive step
`(p j, p (j + 1))` of the clipped dyadic grid. -/
private theorem clippedDyadicGrid_le_dyadicCeilTime {s b : ℝ≥0} {k j : ℕ} {u : WithTop ℝ≥0}
    (h : (clippedDyadicGrid s b k j : WithTop ℝ≥0) < dyadicCeilTime k u) :
    (clippedDyadicGrid s b k (j + 1) : WithTop ℝ≥0) ≤ dyadicCeilTime k u := by
  dsimp only [clippedDyadicGrid] at h ⊢
  by_cases hbu : (b : WithTop ℝ≥0) ≤ dyadicCeilTime k u
  · exact (WithTop.coe_le_coe.mpr (min_le_left _ _)).trans hbu
  · rw [WithTop.coe_min] at h
    have hmax : (max s ((j : ℝ≥0) / (2 : ℝ≥0) ^ k) : WithTop ℝ≥0) < dyadicCeilTime k u :=
      (min_lt_iff.mp h).resolve_left fun hb ↦ hbu hb.le
    refine (WithTop.coe_le_coe.mpr (min_le_right _ _)).trans ?_
    rw [WithTop.coe_max]
    exact max_le ((WithTop.coe_le_coe.mpr (le_max_left _ _)).trans hmax.le)
      (le_dyadicCeilTime_of_div_lt k j
        (lt_of_le_of_lt (WithTop.coe_le_coe.mpr (le_max_right _ _)) hmax))

/-- Telescoping identity for stopping a single elementary interval `(s, t]` at `dyadicCeilTime k u`
on horizon `T` (when `s ≤ T`): summing the indicator-weighted increments over the clipped dyadic
grid telescopes to `c * (f (min t (min T σ).untopA) - f (min s (min T σ).untopA))`. -/
private theorem sum_clippedDyadicGrid_telescope {s t T : ℝ≥0} (hst : s ≤ t) (hsT : s ≤ T)
    (k : ℕ) (u : WithTop ℝ≥0) (c : ℝ) (f : ℝ≥0 → ℝ) :
    let b : ℝ≥0 := min t T; let p : ℕ → ℝ≥0 := clippedDyadicGrid s b k
    let σ : WithTop ℝ≥0 := dyadicCeilTime k u
    ∑ j ∈ range (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1),
        (if (p j : WithTop ℝ≥0) < σ then c else 0) * (f (min (p (j + 1)) T) - f (min (p j) T)) =
      c * (f (min t (min (T : WithTop ℝ≥0) σ).untopA) -
        f (min s (min (T : WithTop ℝ≥0) σ).untopA)) := by
  intro b p σ
  have hsb : s ≤ b := le_min hst hsT; have hbT : b ≤ T := min_le_right t T
  have hp0 : p 0 = s := clippedDyadicGrid_zero hsb k
  have hp_end : p (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1) = b := clippedDyadicGrid_end s b k
  have hp_le (j : ℕ) : p j ≤ b := clippedDyadicGrid_le s b k j
  have hterm (j : ℕ) :
      (if (p j : WithTop ℝ≥0) < σ then c else 0) * (f (min (p (j + 1)) T) - f (min (p j) T)) =
        c * (f (min (p (j + 1) : WithTop ℝ≥0) σ).untopA -
          f (min (p j : WithTop ℝ≥0) σ).untopA) := by
    rw [min_eq_left ((hp_le (j + 1)).trans hbT), min_eq_left ((hp_le j).trans hbT)]
    by_cases hgt : (p j : WithTop ℝ≥0) < σ
    · have hno : (p (j + 1) : WithTop ℝ≥0) ≤ σ := clippedDyadicGrid_le_dyadicCeilTime hgt
      simp only [hgt, ite_true, min_eq_left hgt.le, min_eq_left hno,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    · have hle : σ ≤ (p j : WithTop ℝ≥0) := le_of_not_gt hgt
      have hle' : σ ≤ (p (j + 1) : WithTop ℝ≥0) :=
        hle.trans (WithTop.coe_le_coe.mpr (clippedDyadicGrid_mono s b k (Nat.le_succ j)))
      simp only [hgt, ite_false, zero_mul, min_eq_right hle, min_eq_right hle', sub_self, mul_zero]
  simp_rw [hterm, ← Finset.mul_sum,
    Finset.sum_range_sub (fun j ↦ f (min (p j : WithTop ℝ≥0) σ).untopA) (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1),
    hp0, hp_end]
  have hmin_le {r : ℝ≥0} (hrT : r ≤ T) :
      min r (min (T : WithTop ℝ≥0) σ).untopA = (min (r : WithTop ℝ≥0) σ).untopA := by
    have hcoe (x : ℝ≥0) :
        ((min (x : WithTop ℝ≥0) σ).untopA : WithTop ℝ≥0) = min (x : WithTop ℝ≥0) σ := by
      rw [WithTop.untopA_eq_untop (ne_of_lt (lt_of_le_of_lt (min_le_left _ _)
        (WithTop.coe_lt_top x))), WithTop.coe_untop]
    apply WithTop.coe_injective
    rw [WithTop.coe_min, hcoe T, hcoe r, ← min_assoc, min_eq_left (WithTop.coe_le_coe.mpr hrT)]
  have hmin_t : min t (min (T : WithTop ℝ≥0) σ).untopA = (min (b : WithTop ℝ≥0) σ).untopA := by
    rw [← hmin_le hbT]; dsimp only [b]
    rw [min_assoc, min_eq_right (WithTop.untopA_le (min_le_left (T : WithTop ℝ≥0) σ))]
  rw [hmin_t, hmin_le hsT]

/-- Helper: on a single interval `(s, t]` with bounded `ℱ s`-measurable height `ξ`, stopping the
elementary integral at the dyadic stopping time `dyadicCeilTime k ∘ τ` at horizon `T` is realized
exactly by a bounded simple holding equal to `1_{[0, σ]} · 1_{(s, t]} ξ` on `[0, T]`. -/
private theorem exists_stopped_dyadic_single
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    {C : ℝ} (hC : ∀ ω, ‖ξ ω‖ ≤ C) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (k : ℕ) (T : ℝ≥0) :
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    ∃ (N : ℕ) (p : ℕ → ℝ≥0) (ζ : ℕ → Ω → ℝ) (C' : ℝ),
      MonotoneOn p (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (p j)] (ζ j)) ∧
      (∀ j < N, ∀ ω, ‖ζ j ω‖ ≤ C') ∧
      (∀ u ≤ T, ∀ ω, Finance.simpleHolding p N ζ u ω =
        if (u : WithTop ℝ≥0) ≤ σ ω then (Ioc s t).indicator (fun _ ↦ ξ ω) u else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), Finance.simpleGains p N ζ X T ω =
        stoppedProcess (fun u ω ↦ ξ ω * (X (min t u) ω - X (min s u) ω)) σ T ω := by
  intro σ
  by_cases hsT : s ≤ T
  · -- Step 1: build the clipped dyadic grid `p` on `[s, min t T]` and the adapted heights `ζ`.
    let b : ℝ≥0 := min t T; have hsb : s ≤ b := le_min hst hsT
    let N : ℕ := ⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1; let p : ℕ → ℝ≥0 := clippedDyadicGrid s b k
    have hp_mono : Monotone p := clippedDyadicGrid_mono s b k
    have hp0 : p 0 = s := clippedDyadicGrid_zero hsb k
    have hp_end : p N = b := clippedDyadicGrid_end s b k
    let ζ : ℕ → Ω → ℝ := fun j ω ↦ if (p j : WithTop ℝ≥0) < σ ω then ξ ω else 0
    have hζ_meas (j : ℕ) (_ : j < N) : StronglyMeasurable[ℱ (p j)] (ζ j) :=
      (hξ.mono (ℱ.mono (le_clippedDyadicGrid hsb k j))).ite
        (by convert ((hτ.dyadicCeilTime k).measurableSet_le (p j)).compl using 1
            ext ω; simp only [σ, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le])
        stronglyMeasurable_zero
    refine ⟨N, p, ζ, max C 0, hp_mono.monotoneOn _, hζ_meas, fun _ _ ω ↦ by
        dsimp only [ζ]; split_ifs <;> first | exact (hC ω).trans (le_max_left _ _) | simp,
      fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
    · -- Step 2: check that the stopped step process equals `1_{[0, σ]} · 1_{(s, t]} ξ` on `[0, T]`.
      by_cases hu : u ∈ Ioc s b
      · obtain ⟨j₀, hj₀, hju⟩ :=
          exists_lt_mem_Ioc_of_mem_Ioc (τ := p) (n := N) (by simpa only [hp0, hp_end] using hu)
        rw [Finance.simpleHolding_of_mem_Ioc (hp_mono.monotoneOn _) hj₀ hju,
          indicator_of_mem (s := Ioc s t) ⟨hu.1, hu.2.trans (min_le_left t T)⟩]
        have hiff : (p j₀ : WithTop ℝ≥0) < σ ω ↔ (u : WithTop ℝ≥0) ≤ σ ω :=
          ⟨fun h ↦ (WithTop.coe_le_coe.mpr hju.2).trans (clippedDyadicGrid_le_dyadicCeilTime h),
            lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hju.1)⟩
        simp only [ζ, hiff]
      · rw [Finance.simpleHolding_of_notMem_Ioc (hp_mono.monotoneOn _)
            (by simpa only [hp0, hp_end] using hu),
          indicator_of_notMem (fun h : u ∈ Ioc s t ↦ hu ⟨h.1, le_min h.2 huT⟩), ite_self]
    · -- Step 3: telescope the elementary integral via `sum_clippedDyadicGrid_telescope`.
      rw [Finance.simpleGains_def]
      exact sum_clippedDyadicGrid_telescope hst hsT k (τ ω) (ξ ω) (X · ω)
  · -- When `T < s`, both sides vanish identically on `[0, T]`.
    have hTs : T < s := lt_of_not_ge hsT
    refine ⟨0, fun _ ↦ 0, fun _ _ ↦ 0, 0,
      fun _ _ _ _ _ ↦ le_rfl,
      fun _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
      fun u huT ω ↦ by simp only [Finance.simpleHolding_def, Finset.range_zero, sum_empty,
        indicator_of_notMem (fun h : u ∈ Ioc s t ↦ not_lt_of_ge (huT.trans hTs.le) h.1), ite_self],
      fun X ω ↦ ?_⟩
    have hls : (min (T : WithTop ℝ≥0) (σ ω)).untopA ≤ s :=
      (WithTop.untopA_le (min_le_left _ _)).trans hTs.le
    rw [Finance.simpleGains_def, Finset.range_zero, sum_empty, stoppedProcess,
      min_eq_right (hls.trans hst), min_eq_right hls, sub_self, mul_zero]

/-- Stopping any bounded simple holding at the dyadic stopping time `dyadicCeilTime k ∘ τ` at
horizon `T` is realized exactly by another bounded simple holding. -/
private theorem exists_stopped_dyadic
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} {C : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C)
    {σ₀ : Ω → WithTop ℝ≥0} (hσ₀ : IsStoppingTime ℱ σ₀) (k : ℕ) (T : ℝ≥0) :
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (σ₀ ω)
    ∃ (N : ℕ) (p : ℕ → ℝ≥0) (ζ : ℕ → Ω → ℝ) (C' : ℝ),
      MonotoneOn p (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (p j)] (ζ j)) ∧
      (∀ j < N, ∀ ω, ‖ζ j ω‖ ≤ C') ∧
      (∀ u ≤ T, ∀ ω, Finance.simpleHolding p N ζ u ω =
        if (u : WithTop ℝ≥0) ≤ σ ω then Finance.simpleHolding τ n a u ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), Finance.simpleGains p N ζ X T ω =
        stoppedProcess (Finance.simpleGains τ n a X) σ T ω := by
  intro σ
  suffices ∀ m ≤ n, ∃ (N : ℕ) (p : ℕ → ℝ≥0) (ζ : ℕ → Ω → ℝ) (C' : ℝ),
      MonotoneOn p (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (p j)] (ζ j)) ∧
      (∀ j < N, ∀ ω, ‖ζ j ω‖ ≤ C') ∧
      (∀ u ≤ T, ∀ ω, Finance.simpleHolding p N ζ u ω = ∑ i ∈ range m,
        if (u : WithTop ℝ≥0) ≤ σ ω then
          (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ a i ω) u else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), Finance.simpleGains p N ζ X T ω = ∑ i ∈ range m,
        stoppedProcess (fun u ω ↦ a i ω * (X (min (τ (i + 1)) u) ω -
          X (min (τ i) u) ω)) σ T ω by
    obtain ⟨N, p, ζ, C', hp, hζ, hC', hMP, hMI⟩ := this n le_rfl
    exact ⟨N, p, ζ, C', hp, hζ, hC',
      fun u huT ω ↦ by rw [hMP u huT ω, Finance.simpleHolding_def]; split_ifs <;> simp,
      fun X ω ↦ by
        rw [hMI X ω, stoppedProcess, Finance.simpleGains_def]
        exact Finset.sum_congr rfl fun i _ ↦ by simp only [stoppedProcess]⟩
  intro m hm
  induction m with
  | zero =>
    exact ⟨0, fun _ ↦ 0, fun _ _ ↦ 0, 0,
      fun _ _ _ _ _ ↦ le_rfl,
      fun _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
      fun _ _ _ ↦ by simp [Finance.simpleHolding_def],
      fun _ _ ↦ by simp [Finance.simpleGains_def]⟩
  | succ m ih =>
    have hm' : m < n := hm
    obtain ⟨N₁, p₁, ζ₁, C₁, hp₁, hζ₁, hC₁, hMP, hMI⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨N₂, p₂, ζ₂, C₂, hp₂, hζ₂, hC₂, hEP, hEI⟩ := exists_stopped_dyadic_single
      (hτ hm'.le hm' (Nat.le_succ m)) (ha m hm') (hb m hm') hσ₀ k T
    obtain ⟨N, p, ζ, -, hp, hζ, hbound, hhold, hgain⟩ :=
      Finance.exists_simpleHolding_simpleGains_eq_sum ℱ
        ((range N₁).disjSum (range N₂)) (Sum.elim p₁ p₂)
        (Sum.elim (fun j ↦ p₁ (j + 1)) fun j ↦ p₂ (j + 1)) (Sum.elim ζ₁ ζ₂) (by
          rintro (j | j) hj <;>
            simp only [inl_mem_disjSum, inr_mem_disjSum, Finset.mem_range] at hj
          · exact hζ₁ j hj
          · exact hζ₂ j hj)
    refine ⟨N, p, ζ, ∑ _ ∈ range N₁, C₁ + ∑ _ ∈ range N₂, C₂, hp.monotoneOn, hζ,
      fun j hj ω ↦ (hbound j hj ω).trans (by
        rw [sum_disjSum]
        refine add_le_add (sum_le_sum fun i hi ↦ ?_) (sum_le_sum fun i hi ↦ ?_)
        · exact hC₁ i (Finset.mem_range.mp hi) ω
        · exact hC₂ i (Finset.mem_range.mp hi) ω),
      fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
    · rw [hhold, sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, ← Finance.simpleHolding_def]
      rw [hMP u huT ω, hEP u huT ω, Finset.sum_range_succ]
    · rw [hgain, sum_disjSum, Finset.sum_range_succ, ← hMI X ω, ← hEI X ω,
        Finance.simpleGains_def, Finance.simpleGains_def]
      congr 1 <;> refine sum_congr rfl fun j hj ↦ ?_
      · simp [hp₁ (Finset.mem_range.mp hj).le (Finset.mem_range.mp hj) (Nat.le_succ j)]
      · simp [hp₂ (Finset.mem_range.mp hj).le (Finset.mem_range.mp hj) (Nat.le_succ j)]

/-- For a `BrownianIntegrable` integrand against an almost surely continuous filtered pre-Brownian
motion `W`, stopping its Itô integral at any stopping time `τ` agrees almost surely at every
horizon `T` with the L² Brownian integral of the cutoff integrand `1_{[0, τ]} · H`. -/
theorem stoppedProcess_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    stoppedProcess I τ T =ᵐ[P]
      hW.l2Integral T (((hH.ite_le hτ).memLp_predictableMeasure T).toLp
        (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, s, a, C, hs, ha, hb, hKlim, hunif⟩ :=
    hW.exists_seq_simpleHolding_tendstoUniformlyOn hcont hH hI
  -- Step 1: prove the identity for every dyadic approximation `σ k := dyadicCeilTime k ∘ τ`.
  have hdyad (k : ℕ) :
      stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
        hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).toLp
          (Function.uncurry fun t ω ↦
            if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0)) := by
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
    choose N' p' ζ' C' hp' hζ' hC' hK'P hK'I using fun m ↦
      exists_stopped_dyadic (hs m) (ha m) (hb m) hτ k T
    have hlim_ae : TendstoInMeasure P (fun m ↦ Finance.simpleGains (p' m) (N' m) (ζ' m) W T)
        atTop (stoppedProcess I σ T) := tendstoInMeasure_of_tendsto_ae (fun m ↦
      ((Finance.stronglyAdapted_simpleGains (hp' m) (hζ' m) hW.adapted.stronglyAdapted T).mono
        (ℱ.le T)).aestronglyMeasurable) <| hunif.mono fun ω hω ↦ by
      simpa only [hK'I, stoppedProcess] using
        (hω T).tendsto_at (Set.mem_Iic.mpr (WithTop.untopA_le (min_le_left _ _)))
    let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
    have hlim_L2 : Tendsto (fun m ↦ eLpNorm (fun ω ↦
        Finance.simpleGains (p' m) (N' m) (ζ' m) W T ω -
        hW.l2Integral T (((hH.ite_le hσ).memLp_predictableMeasure T).toLp (Function.uncurry Hσ)) ω)
        2 P) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hKlim T) (fun _ ↦ zero_le)
        fun m ↦ by
          rw [hW.eLpNorm_simpleGains_sub_l2Integral (hp' m) (hζ' m)
            (Finance.memLp_of_bound_stronglyMeasurable (hζ' m) (hC' m)) (hH.ite_le hσ) T]
          refine eLpNorm_mono_ae ((((Finance.isStronglyPredictable_simpleHolding (hζ' m)).sub
            (hH.ite_le hσ).isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
            ?_
          filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
            ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2)] with ⟨u, ω⟩ hu
          dsimp only [Hσ]; rw [hK'P m u hu ω]; split_ifs <;> simp
    exact tendstoInMeasure_ae_unique hlim_ae
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hlim_L2)
  -- Step 2: let `k → ∞` using path continuity of `I` on the left and dominated convergence
  -- on the right.
  let Hk (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0
  let Hτ (t : ℝ≥0) (ω : Ω) : ℝ := if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0
  have hLHS : TendstoInMeasure P
      (fun k ↦ stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T) atTop (stoppedProcess I τ T) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (Lp.aestronglyMeasurable _).congr (hdyad k).symm)
      (hI.ae_continuous.mono fun ω hω ↦
        tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt)
  have hRHS_eLp : Tendsto (fun k ↦ eLpNorm
      (Function.uncurry (Hk k) - Function.uncurry Hτ) 2 ((timeMeasure T).prod P)) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun k ↦
        ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_timeMeasure T).aestronglyMeasurable)
      (hH.memLp_timeMeasure T)
      (.of_forall fun k ↦ .of_forall fun p ↦ by
        dsimp only [Hk, Hτ, Function.uncurry]; split_ifs <;> simp) (.of_forall fun p ↦ ?_)
    dsimp only [Hk, Hτ, Function.uncurry]
    by_cases hp : (p.1 : WithTop ℝ≥0) ≤ τ p.2
    · exact tendsto_const_nhds.congr fun k ↦ by
        simp only [hp, hp.trans (le_dyadicCeilTime k (τ p.2)), ite_true]
    · exact tendsto_const_nhds.congr' <|
        ((tendsto_dyadicCeilTime (τ p.2)).eventually (eventually_lt_nhds (lt_of_not_ge hp))).mono
          fun k hk ↦ by simp only [hp, not_le.mpr hk, ite_false]
  exact tendstoInMeasure_ae_unique hLHS <| (tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
    (by norm_num) (hRHS_eLp.congr fun k ↦
      (hW.eLpNorm_l2Integral_sub T (hH.ite_le (hτ.dyadicCeilTime k)).isStronglyPredictable
        (hH.ite_le hτ).isStronglyPredictable
        ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T)
        ((hH.ite_le hτ).memLp_predictableMeasure T)).symm)).congr_left fun k ↦ (hdyad k).symm

/-- **Stopping compatibility for L² Brownian Itô integrals.** Against an almost surely continuous
filtered pre-Brownian motion `W`, stopping an Itô integral of a `BrownianIntegrable` integrand at
any stopping time `τ` produces an Itô integral of the cutoff integrand `1_{[0, τ]} · H`. No usual
filtration conditions are required. -/
theorem isItoIntegral_stoppedProcess_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  obtain ⟨J, hJito, -, -⟩ := (hH.ite_le hτ).exists_isItoIntegral hW hcont
  exact hJito.congr (TauCeti.indist_of_ae_continuous
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess) hJito.ae_continuous fun T ↦
      (hW.stoppedProcess_ae_eq_l2Integral hcont hH hI hτ T).trans
        (hW.ae_eq_l2Integral_of_isItoIntegral (hH.ite_le hτ) hJito T).symm).symm

end TauCeti.Probability.IsFilteredPreBrownianReal
