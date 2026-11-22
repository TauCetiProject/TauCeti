/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.StochasticInterval
public import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Stopping Brownian integrands

The predictable-set restriction lemmas for the expected and pathwise square-energy domains
specialize to `[0,τ]` and `(σ,τ]` for stopping times on a raw filtration. These are
cutoff integrands, zero after the stopping time, not stopped processes retaining their last
value. Neither completeness nor right continuity of the filtration is required.

Along stopping times tending almost surely to infinity, the cutoffs recover an integrand in
expected square-energy norm on every finite horizon. Rounding a stopping time to a dyadic grid
splits its finite-horizon `L²` cutoff into a finite sum of predictable rectangle restrictions
(`TauCeti.BrownianIntegrable.toLp_ite_le_dyadicCeilTime_eq_sum`). These facts allow
approximation and localization of stochastic-integral inputs. The pathwise-domain closure
results impose no moment assumptions. No stochastic integral is constructed here.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

/-- Killing an integrand after a stopping time preserves finite expected square energy.
The value at the stopping time is retained. -/
theorem BrownianIntegrable.ite_le (hH : BrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator hτ.measurableSet_predictable_ge

/-- Killing an integrand after a stopping time preserves finite pathwise square energy.
The value at the stopping time is retained. -/
theorem LocallyBrownianIntegrable.ite_le (hH : LocallyBrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator hτ.measurableSet_predictable_ge

/-- Restriction to `(σ,τ]` preserves finite expected square energy. No ordering of the
stopping times is required. -/
theorem BrownianIntegrable.ite_Ioc (hH : BrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator (hσ.measurableSet_predictable_Ioc hτ)

/-- Restriction to `(σ,τ]` preserves finite pathwise square energy. No ordering of the
stopping times is required. -/
theorem LocallyBrownianIntegrable.ite_Ioc (hH : LocallyBrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator (hσ.measurableSet_predictable_Ioc hτ)

/-- Cutoffs along stopping times tending almost surely to infinity converge on each finite
horizon in expected square-energy norm. Monotonicity of the times is unnecessary. -/
theorem BrownianIntegrable.tendsto_eLpNorm_ite_le_sub
    (hH : BrownianIntegrable ℱ P H) {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime ℱ (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)) (T : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (if (p.1 : WithTop ℝ≥0) ≤ τ n p.2 then H p.1 p.2 else 0) -
        H p.1 p.2) 2
      (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P))
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
    (Eventually.of_forall fun n ↦ ((hH.ite_le (hτ n)).memLp T).aestronglyMeasurable)
    (hH.memLp T)
  · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun p ↦ by
      dsimp only [Function.uncurry]
      split_ifs <;> simp
  · have hprod := (Measure.quasiMeasurePreserving_snd
        (μ := (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))
        (ν := P)).ae hlim
    filter_upwards [hprod] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [hp.eventually (eventually_gt_nhds (WithTop.coe_lt_top p.1))] with n hn
    exact (ite_eq_left hn.le).symm

/-- Every clipped dyadic cell intersected with the event that the dyadic stopping time exceeds
its left endpoint is predictable, including cells beyond the horizon (which are empty). -/
theorem measurableSet_predictable_Ioc_dyadicCeilTime (hτ : IsStoppingTime ℱ τ)
    (m : ℕ) (T : ℝ≥0) (k : ℕ) :
    MeasurableSet[ℱ.predictable]
      (Ioc (min ((k : ℝ≥0) / 2 ^ m) T) (min (((k + 1 : ℕ) : ℝ≥0) / 2 ^ m) T) ×ˢ
        {ω | (((k : ℝ≥0) / 2 ^ m : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m (τ ω)}) := by
  by_cases hk : k < ⌈T * 2 ^ m⌉₊
  · exact measurableSet_predictable_Ioc_prod _ _ (hτ.measurableSet_gt_dyadicCeilTime m hk)
  · have hT : T ≤ (k : ℝ≥0) / 2 ^ m :=
      (le_div_iff₀ (by positivity)).mpr (Nat.ceil_le.mp (le_of_not_gt hk))
    simp [min_eq_right hT]

/-- Rounding a stopping time to the dyadic grid of mesh `2 ^ (-m)` splits the finite-horizon
predictable `L²` class of the cutoff integrand into a finite sum of predictable-cell
restrictions. -/
theorem BrownianIntegrable.toLp_ite_le_dyadicCeilTime_eq_sum [SFinite P]
    (hH : BrownianIntegrable ℱ P H) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (m : ℕ) (T : ℝ≥0) :
    ((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _ =
      ∑ k ∈ Finset.range ⌈T * 2 ^ m⌉₊,
        ((Lp.memLp ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))).indicator
          ((measurableSet_predictable_Ioc_dyadicCeilTime hτ m T k).nullMeasurableSet
            (m0 := ℱ.predictable))).toLp
          ((Ioc (min ((k : ℝ≥0) / 2 ^ m) T) (min (((k + 1 : ℕ) : ℝ≥0) / 2 ^ m) T) ×ˢ
            {ω | (((k : ℝ≥0) / 2 ^ m : ℝ≥0) : WithTop ℝ≥0) <
              dyadicCeilTime m (τ ω)}).indicator
            ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime m (τ ω)
  let d : ℕ → ℝ≥0 := fun k ↦ (k : ℝ≥0) / 2 ^ m
  let t : ℕ → ℝ≥0 := fun k ↦ min (d k) T
  let A : ℕ → Set Ω := fun k ↦ {ω | ((d k : ℝ≥0) : WithTop ℝ≥0) < σ ω}
  let N : ℕ := ⌈T * 2 ^ m⌉₊
  let fH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  have h2pos : (0 : ℝ≥0) < 2 ^ m := by positivity
  let piece (k : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    ((Lp.memLp fH).indicator
      ((measurableSet_predictable_Ioc_dyadicCeilTime hτ m T k).nullMeasurableSet
        (m0 := ℱ.predictable))).toLp
      ((Ioc (t k) (t (k + 1)) ×ˢ A k).indicator fH)
  -- Identify each cell's `Lp` representative with the pointwise indicator of `H`.
  have hterms : ∀ k ∈ Finset.range N, (piece k : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
      (Ioc (t k) (t (k + 1)) ×ˢ A k).indicator (Function.uncurry H) := by
    intro k _
    filter_upwards [((Lp.memLp fH).indicator
      ((measurableSet_predictable_Ioc_dyadicCeilTime hτ m T k).nullMeasurableSet
        (m0 := ℱ.predictable))).coeFn_toLp,
      (hH.memLp_predictableMeasure T).coeFn_toLp] with p hp hHp
    dsimp only [piece, t, d, A, σ, fH] at hp ⊢
    simp only [hp, indicator_apply, hHp]
  -- Evaluate both sides on `(0, T] × Ω`, where a single dyadic cell `k₀ = ⌈s * 2^m⌉₊ - 1`
  -- covers `s`.
  apply Lp.ext
  have hL_ae := ((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).coeFn_toLp
  filter_upwards [hL_ae, ℱ.ae_mem_Ioc_prod_predictableMeasure P T,
    Lp.coeFn_finsetSum (s := Finset.range N) piece, eventuallyEq_sum hterms]
    with ⟨s, ω⟩ hL hsT hsum htms
  rw [hL, hsum, htms]
  simp only [Finset.sum_apply, Function.uncurry_apply_pair]
  let k₀ : ℕ := ⌈s * 2 ^ m⌉₊ - 1
  have hceil_pos : 0 < ⌈s * 2 ^ m⌉₊ := Nat.ceil_pos.mpr (mul_pos hsT.left.left h2pos)
  have hk₀ : k₀ ∈ Finset.range N := Finset.mem_range.mpr <| by
    have : ⌈s * 2 ^ m⌉₊ ≤ N := Nat.ceil_mono (mul_le_mul_of_nonneg_right hsT.left.right h2pos.le)
    omega
  have hsk₀ : s ∈ Ioc (d k₀) (d (k₀ + 1)) :=
    ⟨dyadic_div_lt_of_lt_ceil (Nat.sub_lt hceil_pos zero_lt_one),
      (le_div_iff₀ h2pos).mpr (by
        simpa only [k₀, Nat.sub_add_cancel hceil_pos] using Nat.le_ceil _)⟩
  rw [Finset.sum_eq_single k₀]
  · -- Inside cell `k₀`, `s ≤ dyadicCeilTime m (τ ω)` holds iff `ω ∈ A k₀`.
    have hst : s ∈ Ioc (t k₀) (t (k₀ + 1)) := by
      dsimp only [t]
      exact ⟨(min_dyadic_div_eq_left (Finset.mem_range.mp hk₀)).symm ▸ hsk₀.left,
        le_min hsk₀.right hsT.left.right⟩
    have hiff := coe_le_dyadicCeilTime_iff_gt_dyadic m k₀ hsk₀ (τ ω)
    by_cases hc : (s : WithTop ℝ≥0) ≤ σ ω
    · rw [ite_eq_left hc, indicator_of_mem (mem_prod.mpr ⟨hst, hiff.mp hc⟩),
        Function.uncurry_apply_pair]
    · rw [ite_eq_right hc, indicator_of_notMem (fun h ↦ hc (hiff.mpr (mem_prod.mp h).right))]
  · -- All other cells `k ≠ k₀` are disjoint from `s`.
    intro k hk hne
    refine indicator_of_notMem (f := Function.uncurry H) fun h ↦ ?_
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ((mem_prod.mp h).left.right.trans <| (min_le_left _ _).trans <|
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hlt) h2pos.le).not_gt hsk₀.left
    · have htk : t k = d k := min_dyadic_div_eq_left (Finset.mem_range.mp hk)
      exact (hsk₀.right.trans <| htk ▸
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hlt) h2pos.le).not_gt
          (mem_prod.mp h).left.left
  · exact fun hnot ↦ (hnot hk₀).elim

end TauCeti
