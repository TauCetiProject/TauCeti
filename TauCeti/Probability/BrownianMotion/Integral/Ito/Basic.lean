/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.TimeMeasure
public import Mathlib.Probability.Process.Indistinguishable
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# The Itô integral predicate and uniqueness

`TauCeti.IsItoIntegral ℱ P W H I` characterizes a process `I` as an Itô stochastic integral of a
predictable integrand `H` against an integrator `W`: almost every path of `I` is continuous, and
at each deterministic horizon `t` some sequence of left-measurable finite-grid holdings
approximates `H` in pathwise square energy in probability while its elementary gains converge in
probability to `I t`. Pathwise square errors are measured by lower Lebesgue integrals on `(0, t]`,
so divergent pathwise energies take the value `∞` rather than a Bochner fallback zero. Neither
uniform height bounds on the elementary approximants nor adaptation of `I` are built into the
predicate, allowing explicit pathwise formulas to be verified directly and then compared with
canonical progressive versions.

Any integrand admitting an Itô integral automatically belongs to `LocallyBrownianIntegrable`
(`IsItoIntegral.locallyBrownianIntegrable`), and the predicate is closed under sequential
limits in pathwise square energy and fixed-time probability (`IsItoIntegral.of_seq`). Against a
filtered pre-Brownian motion `W`, every elementary approximation sequence converging in pathwise
square energy has gains converging in probability to `I t`
(`IsItoIntegral.tendstoInMeasure_simpleGains`), without requiring path continuity of `W`.
Consequently, Itô integrals are unique up to indistinguishability (`IsItoIntegral.indist`) and
depend on the integrand only up to `(timeMeasure T).prod P`-almost everywhere equality on finite
horizons (`IsItoIntegral.indist_of_ae_eq_prod`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W B H K I J : ℝ≥0 → Ω → ℝ}

/-- `I` is an Itô stochastic integral of `H` against `W` on `(Ω, ℱ, P)` if `H` is predictable,
`I` has almost surely continuous paths, and at each horizon `t` there exist elementary
predictable holdings whose pathwise square-energy errors on `(0, t]` tend to zero in probability
and whose elementary gains at `t` tend to `I t` in probability. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is literally predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every sample path of the integral process is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At each horizon, elementary predictable holdings approximate the integrand in pathwise
  square energy in probability while their elementary integrals converge in probability to `I t`. -/
  exists_seq_approx : ∀ t : ℝ≥0,
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
      (∀ m, MonotoneOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
      TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ m) (n m) (a m) W t) atTop (I t)

private theorem tendsto_measure_ge_zero_of_ae_le {E E₁ E₂ : ℕ → Ω → ℝ≥0∞}
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun m ↦ P {ω | ε ≤ E₁ m ω}) atTop (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun m ↦ P {ω | ε ≤ E₂ m ω}) atTop (𝓝 0))
    (hle : ∀ m, ∀ᵐ ω ∂P, E m ω ≤ 2 * E₁ m ω + 2 * E₂ m ω)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤ E m ω}) atTop (𝓝 0) := by
  rcases eq_or_ne ε ∞ with rfl | _
  · have hsub (m : ℕ) : {ω | ∞ ≤ E m ω} ≤ᵐ[P]
        {ω | 1 ≤ E₁ m ω} ∪ {ω | 1 ≤ E₂ m ω} := by
      filter_upwards [hle m] with ω hω htop
      by_contra hnot
      simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le] at hnot
      have hlt : E m ω < ∞ := hω.trans_lt (ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top (by norm_num) (hnot.1.trans (by norm_num)),
          ENNReal.mul_lt_top (by norm_num) (hnot.2.trans (by norm_num))⟩)
      exact hlt.not_ge htop
    have hsum : Tendsto (fun m ↦
        P {ω | 1 ≤ E₁ m ω} + P {ω | 1 ≤ E₂ m ω}) atTop (𝓝 0) := by
      simpa using (h₁ 1 one_pos).add (h₂ 1 one_pos)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun m ↦ ?_
    exact (measure_mono_ae (hsub m)).trans (measure_union_le _ _)
  · have hquarter : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
    have hsub (m : ℕ) : {ω | ε ≤ E m ω} ≤ᵐ[P]
        {ω | ε / 4 ≤ E₁ m ω} ∪ {ω | ε / 4 ≤ E₂ m ω} := by
      filter_upwards [hle m] with ω hω hge
      by_contra hnot
      simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le] at hnot
      have hsum : 2 * E₁ m ω + 2 * E₂ m ω < ε := by
        have h22 : (2 : ℝ≥0∞) * 2 = 4 := by norm_num
        have h4 : 2 * (ε / 4) + 2 * (ε / 4) = ε := by
          rw [← two_mul, ← mul_assoc, h22, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
        rw [← h4]
        exact ENNReal.add_lt_add
          (ENNReal.mul_lt_mul_right (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hnot.1)
          (ENNReal.mul_lt_mul_right (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hnot.2)
      exact (hω.trans_lt hsum).not_ge hge
    have hsum : Tendsto (fun m ↦ P {ω | ε / 4 ≤ E₁ m ω} +
        P {ω | ε / 4 ≤ E₂ m ω}) atTop (𝓝 0) := by
      simpa using (h₁ _ hquarter).add (h₂ _ hquarter)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun m ↦ ?_
    exact (measure_mono_ae (hsub m)).trans (measure_union_le _ _)

private theorem lintegral_enorm_sq_simpleHolding_eq
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} {t : ℝ≥0}
    (hτ : MonotoneOn τ (Iic n)) (ht : ∀ j ≤ n, τ j ≤ t) (ω : Ω) :
    ∫⁻ s, ‖Finance.simpleHolding τ n a s ω‖ₑ ^ 2 ∂Probability.timeMeasure t =
      ENNReal.ofReal (Probability.elementaryEnergy τ a n ω) := by
  rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hτ t ω,
    Probability.elementaryEnergy_def, ENNReal.ofReal_sum_of_nonneg fun j hj ↦ ?_]
  · refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.1 hj
    have hsq : ENNReal.ofReal (a j ω ^ 2) = ‖a j ω‖ₑ ^ 2 := by
      rw [← sq_abs, ← Real.norm_eq_abs, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [min_eq_left (ht (j + 1) hj'), ENNReal.ofReal_mul (sq_nonneg _), hsq]
  · have hj' := mem_range.1 hj
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.2 (NNReal.coe_le_coe.2 (hτ hj'.le hj' (Nat.le_succ j))))

private theorem lintegral_enorm_sq_sub_le_two_mul_timeMeasure (t : ℝ≥0) (f g h : ℝ≥0 → ℝ)
    (hf : Measurable (fun s ↦ ‖f s - h s‖ₑ ^ 2)) :
    ∫⁻ s, ‖f s - g s‖ₑ ^ 2 ∂Probability.timeMeasure t ≤
      2 * ∫⁻ s, ‖f s - h s‖ₑ ^ 2 ∂Probability.timeMeasure t +
        2 * ∫⁻ s, ‖g s - h s‖ₑ ^ 2 ∂Probability.timeMeasure t := by
  have hpt (s : ℝ≥0) : ‖f s - g s‖ₑ ^ 2 ≤ 2 * ‖f s - h s‖ₑ ^ 2 + 2 * ‖g s - h s‖ₑ ^ 2 := by
    have hreal := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two_mul (f s) (g s) (h s))
    simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.ofReal_ofNat] at hreal
    simpa only [mul_add] using hreal
  refine (lintegral_mono hpt).trans_eq ?_
  rw [lintegral_add_left (hf.const_mul 2),
    lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

private theorem simpleHolding_clipped_eq {g : ℕ → ℝ≥0} {N : ℕ} {b : ℕ → Ω → ℝ} {s t : ℝ≥0}
    (hs : s ≤ t) (ω : Ω) :
    Finance.simpleHolding (fun j ↦ min (g j) t) N
      (fun j ↦ if g j < t then b j else 0) s ω =
      Finance.simpleHolding g N b s ω := by
  rw [Finance.simpleHolding_def, Finance.simpleHolding_def]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases h : g j < t
  · simp only [h, ↓reduceIte, min_eq_left h.le, indicator_apply, Set.mem_Ioc,
      le_min_iff, hs, and_true]
  · simp [h, Set.mem_Ioc, (hs.trans (not_lt.1 h)).not_gt]

private theorem sum_clipped_mul_sub_eq_simpleGains
    {g : ℕ → ℝ≥0} {N : ℕ} {b : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Iic N)) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (∑ j ∈ range N, (if g j < t then b j else 0) ω *
        (X (min (g (j + 1)) t) ω - X (min (g j) t) ω)) =
      Finance.simpleGains g N b X t ω := by
  rw [Finance.simpleGains_def]
  refine sum_congr rfl fun j hj ↦ ?_
  by_cases h : g j < t
  · simp [h]
  · have hle : t ≤ g j := not_lt.1 h
    have hle' : t ≤ g (j + 1) := hle.trans
      (hg (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j))
    simp [h, min_eq_right hle, min_eq_right hle']

/-- Clip two finite-grid strategies to `[0, t]` and combine their difference on a single
nondecreasing deterministic grid contained in `[0, t]`. -/
private theorem exists_clipped_diff_grid (t : ℝ≥0)
    {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁))
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (hτ₂ : MonotoneOn τ₂ (Iic n₂))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j)) :
    ∃ (N : ℕ) (grid : ℕ → ℝ≥0) (height : ℕ → Ω → ℝ),
      MonotoneOn grid (Iic N) ∧ (∀ j ≤ N, grid j ≤ t) ∧
      (∀ j < N, StronglyMeasurable[ℱ (grid j)] (height j)) ∧
      (∀ s ≤ t, ∀ ω, Finance.simpleHolding grid N height s ω =
        Finance.simpleHolding τ₁ n₁ a₁ s ω - Finance.simpleHolding τ₂ n₂ a₂ s ω) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) ω,
        (∑ j ∈ range N, height j ω * (X (grid (j + 1)) ω - X (grid j) ω)) =
          Finance.simpleGains τ₁ n₁ a₁ X t ω -
            Finance.simpleGains τ₂ n₂ a₂ X t ω := by
  let κ := Fin n₁ ⊕ Fin n₂
  let l : κ → ℝ≥0 := Sum.elim (fun i ↦ min (τ₁ i) t) (fun i ↦ min (τ₂ i) t)
  let u : κ → ℝ≥0 :=
    Sum.elim (fun i ↦ min (τ₁ (i + 1)) t) (fun i ↦ min (τ₂ (i + 1)) t)
  let c : κ → Ω → ℝ := Sum.elim
    (fun i ↦ if τ₁ i < t then a₁ i else 0)
    (fun i ↦ if τ₂ i < t then (-a₂) i else 0)
  have hc : ∀ k ∈ (Finset.univ : Finset κ), StronglyMeasurable[ℱ (l k)] (c k) := by
    rintro (i | i) _ <;> dsimp only [c, Sum.elim_inl, Sum.elim_inr] <;> split_ifs with h
    · have hl : l (Sum.inl i) = τ₁ i := min_eq_left h.le
      exact hl ▸ ha₁ i i.2
    · exact stronglyMeasurable_zero
    · have hl : l (Sum.inr i) = τ₂ i := min_eq_left h.le
      exact hl ▸ (ha₂ i i.2).neg
    · exact stronglyMeasurable_zero
  obtain ⟨N, g, b, -, hg, hb, -, hhold, hgains⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u c hc
  let grid (j : ℕ) : ℝ≥0 := min (g j) t
  let height (j : ℕ) : Ω → ℝ := if g j < t then b j else 0
  have hlu (k : κ) : l k ≤ u k := by
    rcases k with i | i
    · exact min_le_min_right t (hτ₁ i.2.le i.2 (Nat.le_succ i))
    · exact min_le_min_right t (hτ₂ i.2.le i.2 (Nat.le_succ i))
  have hut (k : κ) : u k ≤ t := by rcases k with i | i <;> exact min_le_right _ _
  refine ⟨N, grid, height, fun i hi j hj hij ↦ min_le_min_right t (hg.monotoneOn hi hj hij),
    fun _ _ ↦ min_le_right _ _, fun j hj ↦ ?_, fun s hs ω ↦ ?_, fun X ω ↦ ?_⟩
  · dsimp only [height]
    split_ifs with h
    · have hg_eq : grid j = g j := min_eq_left h.le
      exact hg_eq ▸ hb j hj
    · exact stronglyMeasurable_zero
  · rw [simpleHolding_clipped_eq hs ω, hhold, Fintype.sum_sum_type]
    dsimp only [l, u, c, Sum.elim_inl, Sum.elim_inr]
    have h₁ := simpleHolding_clipped_eq (g := τ₁) (N := n₁) (b := a₁) hs ω
    have h₂ := simpleHolding_clipped_eq (g := τ₂) (N := n₂) (b := -a₂) hs ω
    have hneg := Finance.simpleHolding_smul τ₂ n₂ (-1 : ℝ) a₂ s ω
    simp only [neg_one_smul, neg_one_mul] at hneg
    rw [Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range] at h₁ h₂
    rw [h₁, h₂, hneg, sub_eq_add_neg]
  · rw [sum_clipped_mul_sub_eq_simpleGains hg.monotoneOn X t ω, hgains, Fintype.sum_sum_type]
    simp only [hlu, ↓reduceIte, min_eq_left (hut _), min_eq_left ((hlu _).trans (hut _))]
    dsimp only [l, u, c, Sum.elim_inl, Sum.elim_inr]
    have hneg := Finance.simpleGains_smul τ₂ n₂ (-1 : ℝ) a₂ X t ω
    simp only [neg_one_smul, neg_one_mul] at hneg
    rw [sub_eq_add_neg, ← hneg, ← sum_clipped_mul_sub_eq_simpleGains hτ₁ X t ω,
      ← sum_clipped_mul_sub_eq_simpleGains (b := -a₂) hτ₂ X t ω,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]

namespace IsItoIntegral

/-- Any integrand admitting an Itô integral has locally finite pathwise square energy. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun k ↦ ?_⟩
  rw [← NNReal.coe_natCast k, NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
  obtain ⟨n, τ, a, -, -, hE, -⟩ := hI.exists_seq_approx k
  let E (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
      ∂Probability.timeMeasure k
  have hnull : P (⋂ m, {ω | (1 : ℝ≥0∞) ≤ E m ω}) = 0 :=
    le_antisymm (ge_of_tendsto' (hE 1 one_pos) fun m ↦ measure_mono (iInter_subset _ m))
      zero_le
  have hex : ∀ᵐ ω ∂P, ∃ m, E m ω < 1 := by
    rw [ae_iff]
    convert hnull using 2
    ext ω
    simp
  have hmH : StronglyMeasurable (Function.uncurry H) :=
    hI.isStronglyPredictable.mono ℱ.predictable_le_prod
  filter_upwards [hex] with ω ⟨m, hm⟩
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω) 2
      (Probability.timeMeasure k) := by
    simp only [Finance.simpleHolding_def]
    exact memLp_finsetSum _ fun j _ ↦
      (memLp_const (a m j ω)).indicator measurableSet_Ioc.nullMeasurableSet
  have hsub : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω) 2
      (Probability.timeMeasure k) := by
    have hsm : AEStronglyMeasurable
        (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω)
        (Probability.timeMeasure k) :=
      hL.aestronglyMeasurable.sub
        (hmH.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    exact hsm.memLp_two_iff_lintegral_enorm_sq_lt_top.2 (hm.trans_le le_top)
  simpa only [Pi.sub_def, sub_sub_cancel] using hL.sub hsub

/-- Every Itô integral against an integrator with almost-everywhere strongly measurable marginals
is almost-everywhere strongly measurable at each horizon, without assuming adaptation of `I`. -/
theorem aestronglyMeasurable (hW : ∀ s, AEStronglyMeasurable (W s) P)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    AEStronglyMeasurable (I t) P := by
  obtain ⟨n, g, a, _, ha, _, hG⟩ := hI.exists_seq_approx t
  refine hG.aestronglyMeasurable fun m ↦ ?_
  have hdef : Finance.simpleGains (g m) (n m) (a m) W t =
      fun ω ↦ ∑ j ∈ range (n m),
        a m j ω * (W (min (g m (j + 1)) t) ω - W (min (g m j) t) ω) :=
    funext (Finance.simpleGains_def _ _ _ W t)
  rw [hdef]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j hj ↦
    ((ha m j (mem_range.1 hj)).mono (ℱ.le _)).aestronglyMeasurable.mul ((hW _).sub (hW _))

/-- The zero process is an Itô integral of the zero integrand. -/
theorem zero : IsItoIntegral ℱ P W 0 0 := by
  refine ⟨stronglyMeasurable_zero, .of_forall fun _ ↦ continuous_const, fun t ↦ ?_⟩
  refine ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, fun _ ↦ monotoneOn_const,
    fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · simp [Finance.simpleHolding_def, hε.ne']
  · simp [Finance.simpleGains_def, hε.ne']

/-- Indistinguishable replacements preserve `IsItoIntegral`. -/
theorem of_indist (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hc hω
    exact hc.congr hω
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, ha, hE, hG.congr_right (hIJ.ae_eq_eval t)⟩

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ t, W t =ᵐ[P] B t) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, hE, hG.congr_left fun m ↦ ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ j ∈ range (n m + 1), W (min (τ m j) t) ω = B (min (τ m j) t) ω :=
      (ae_ball_iff (Finset.countable_toSet _)).2 fun j _ ↦ hWB _
    filter_upwards [hall] with ω hω
    exact Finance.simpleGains_congr_price ω fun j hj ↦ hω j (mem_range.2 (Nat.lt_succ_of_le hj))

/-- Replacing the integrand by a predictable representative that agrees almost everywhere in time
on almost every path preserves `IsItoIntegral`. -/
theorem congr_ae (hI : IsItoIntegral ℱ P W H I) (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ K s ω)) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hE ε hε).congr' ?_, hG⟩
    refine .of_forall fun m ↦ measure_congr ?_
    filter_upwards [hHK t] with ω hω
    have heq : (∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - K s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      refine lintegral_congr_ae ?_
      filter_upwards [hω] with s hs
      rw [hs]
    simp [heq]

/-- The elementary gains of a left-measurable simple holding form an Itô integral of that holding
whenever the integrator has almost surely continuous paths. -/
theorem simpleGains {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := by
    filter_upwards [hW] with ω hω
    simp only [Finance.simpleGains_def]
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
      ((hω.comp (continuous_const.min continuous_id)).sub
        (hω.comp (continuous_const.min continuous_id)))
  exists_seq_approx t := by
    refine ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha,
      fun ε hε ↦ by simp [hε.ne'], fun ε hε ↦ by simp [hε.ne']⟩

/-- Scaling an integrand scales its Itô integral. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hH0 : (fun t ω ↦ (0 : ℝ) * H t ω) = 0 := by ext; simp
    have hI0 : (fun t ω ↦ (0 : ℝ) * I t ω) = 0 := by ext; simp
    rw [hH0, hI0]
    exact zero
  refine ⟨hI.isStronglyPredictable.const_mul c,
    hI.ae_continuous.mono fun ω hω ↦ continuous_const.mul hω, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_seq_approx t
  refine ⟨n, τ, fun m ↦ c • a m, hτ, fun m j hj ↦ (ha m j hj).const_smul c, fun ε hε ↦ ?_, ?_⟩
  · have hc0 : ‖c‖ₑ ^ 2 ≠ 0 := pow_ne_zero 2 (eNorm_ne_zero.2 hc)
    have hctop : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
    have hdiv : 0 < ε / ‖c‖ₑ ^ 2 := ENNReal.div_pos hε.ne' hctop
    refine (hE _ hdiv).congr' (.of_forall fun m ↦ ?_)
    congr 1
    ext ω
    simp only [mem_ofPred_eq, Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ hctop, ENNReal.div_le_iff_le_mul (.inl hc0) (.inl hctop),
      mul_comm]
  · have hsmul : (fun m ω ↦ Finance.simpleGains (τ m) (n m) (c • a m) W t ω) =
        fun m ω ↦ c * Finance.simpleGains (τ m) (n m) (a m) W t ω := by
      ext m ω
      exact Finance.simpleGains_smul (τ m) (n m) c (a m) W t ω
    rw [hsmul]
    exact tendstoInMeasure_iff_norm.2 fun ε hε ↦ by
      have hcpos : 0 < |c| := abs_pos.2 hc
      have h := (tendstoInMeasure_iff_norm.1 hG) (ε / |c|) (div_pos hε hcpos)
      refine h.congr' (.of_forall fun m ↦ ?_)
      congr 1
      ext ω
      simp only [mem_ofPred_eq, ← mul_sub, norm_mul, Real.norm_eq_abs, div_le_iff₀' hcpos]

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W (-H) (-I) := by
  simpa only [neg_one_mul, Pi.neg_def] using hI.const_mul (-1)

/-- The sum of two Itô integrals is an Itô integral of the sum of their integrands. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H + K) (I + J) := by
  refine ⟨hI.isStronglyPredictable.add hJ.isStronglyPredictable, ?_, fun t ↦ ?_⟩
  · filter_upwards [hI.ae_continuous, hJ.ae_continuous] with ω hIω hJω
    exact hIω.add hJω
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hG₁⟩ := hI.exists_seq_approx t
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hJ.exists_seq_approx t
  have href (m : ℕ) := exists_clipped_diff_grid (ℱ := ℱ) (a₂ := -(a₂ m)) t (hτ₁ m) (ha₁ m)
    (hτ₂ m) (fun j hj ↦ (ha₂ m j hj).neg)
  choose N grid height hgrid hgrid_le hheight hhold hgains using href
  refine ⟨N, grid, height, hgrid, hheight, fun ε hε ↦ ?_, ?_⟩
  · have hle (m : ℕ) (ω : Ω) :
        ∫⁻ s, ‖Finance.simpleHolding (grid m) (N m) (height m) s ω - (H + K) s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t ≤
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t +
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      have hm₁ : Measurable (fun s ↦
          ‖Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω‖ₑ ^ 2) :=
        (((Finance.isStronglyPredictable_simpleHolding (ha₁ m)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
          |>.comp measurable_prodMk_right
      have heq : (∫⁻ s, ‖Finance.simpleHolding (grid m) (N m) (height m) s ω - (H + K) s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t) =
          ∫⁻ s, ‖(Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω) -
            (K s ω - Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
        refine lintegral_congr_ae ?_
        filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
        have hneg := Finance.simpleHolding_smul (τ₂ m) (n₂ m) (-1 : ℝ) (a₂ m) s ω
        simp only [neg_one_smul, neg_one_mul] at hneg
        rw [hhold m s hs.2 ω, hneg]
        simp only [Pi.add_apply]
        ring_nf
      rw [heq]
      have hbound := lintegral_enorm_sq_sub_le_two_mul_timeMeasure t
        (fun s ↦ Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω)
        (fun s ↦ K s ω - Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)
        (fun _ ↦ 0) (by simpa only [sub_zero] using hm₁)
      simpa only [sub_zero, eNorm_sub_rev (K _ ω)] using hbound
    exact tendsto_measure_ge_zero_of_ae_le hE₁ hE₂ (fun m ↦ .of_forall (hle m)) hε
  · refine (hG₁.add hG₂).congr_left fun m ↦ .of_forall fun ω ↦ ?_
    have hsum := Finance.simpleGains_apply_eq_sum (a := height m) (hgrid m) le_rfl W ω
    have hge := Finance.simpleGains_of_ge (a := height m) (hgrid m) (hgrid_le m (N m) le_rfl) W ω
    have hneg := Finance.simpleGains_smul (τ₂ m) (n₂ m) (-1 : ℝ) (a₂ m) W t ω
    simp only [neg_one_smul, neg_one_mul] at hneg
    rw [hge, hsum, hgains m W ω, hneg, sub_neg_eq_add]

/-- The difference of two Itô integrals is an Itô integral of the difference of their
integrands. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-- **Sequential closure of the Itô integral.** If a sequence of Itô integrals `(H_seq k, U_seq k)`
approximates a predictable integrand `H` in pathwise square energy in probability on every finite
horizon and `U_seq k t` converges in probability to `I t` at each horizon for an almost surely
continuous process `I`, then `I` is an Itô integral of `H`. -/
theorem of_seq {H_seq : ℕ → ℝ≥0 → Ω → ℝ} {U_seq : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    (hI : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hU : ∀ k, IsItoIntegral ℱ P W (H_seq k) (U_seq k))
    (hE : ∀ t : ℝ≥0, ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖H_seq k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hG : ∀ t : ℝ≥0, TendstoInMeasure P (fun k ↦ U_seq k t) atTop (I t)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hI, fun t ↦ ?_⟩
  let δ (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ k
  have hδ_pos (k : ℕ) : 0 < δ k := ENNReal.pow_pos (by simp) k
  have hδ_lim : Tendsto δ atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hstep (k : ℕ) : ∃ (N : ℕ) (grid : ℕ → ℝ≥0) (height : ℕ → Ω → ℝ),
      MonotoneOn grid (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (grid j)] (height j)) ∧
      P {ω | δ k ≤ ∫⁻ s, ‖Finance.simpleHolding grid N height s ω - H_seq k s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t} ≤ δ k ∧
      P {ω | (2⁻¹ ^ k : ℝ) ≤ ‖Finance.simpleGains grid N height W t ω - U_seq k t ω‖} ≤ δ k := by
    obtain ⟨n, τ, a, hτ, ha, hEk, hGk⟩ := (hU k).exists_seq_approx t
    have hev₁ := (hEk (δ k) (hδ_pos k)).eventually (eventually_lt_nhds (hδ_pos k))
    have hev₂ := ((tendstoInMeasure_iff_norm.1 hGk) (2⁻¹ ^ k) (by positivity)).eventually
      (eventually_lt_nhds (hδ_pos k))
    obtain ⟨m, hm₁, hm₂⟩ := (hev₁.and hev₂).exists
    exact ⟨n m, τ m, a m, hτ m, ha m, hm₁.le, hm₂.le⟩
  choose N grid height hgrid hheight hE_diag hG_diag using hstep
  have hE₁ (ε : ℝ≥0∞) (hε : 0 < ε) : Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (grid k) (N k) (height k) s ω - H_seq k s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ_lim
      (.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hδ_lim.eventually (eventually_lt_nhds hε)] with k hk
    exact (measure_mono fun ω hω ↦ hk.le.trans hω).trans (hE_diag k)
  refine ⟨N, grid, height, hgrid, hheight, fun ε hε ↦ ?_, ?_⟩
  · refine tendsto_measure_ge_zero_of_ae_le hE₁ (hE t) (fun k ↦ .of_forall fun ω ↦ ?_) hε
    have hbound := lintegral_enorm_sq_sub_le_two_mul_timeMeasure t
      (fun s ↦ Finance.simpleHolding (grid k) (N k) (height k) s ω)
      (fun s ↦ H s ω) (fun s ↦ H_seq k s ω)
      ((((Finance.isStronglyPredictable_simpleHolding (hheight k)).sub
        (hU k).isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
        |>.comp measurable_prodMk_right)
    simpa only [eNorm_sub_rev (H _ ω)] using hbound
  · have hG₁ : TendstoInMeasure P
        (fun k ω ↦ Finance.simpleGains (grid k) (N k) (height k) W t ω - U_seq k t ω)
        atTop (fun _ ↦ 0) := by
      refine tendstoInMeasure_of_tendsto_measure_rate_lt_dist
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num) :
          Tendsto (fun k : ℕ ↦ (2⁻¹ ^ k : ℝ)) atTop (𝓝 0)) ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ_lim
        (fun _ ↦ zero_le) fun k ↦ ?_
      exact (measure_mono fun ω hω ↦ by
        rw [mem_ofPred_eq, dist_zero_right] at hω
        exact hω.le).trans (hG_diag k)
    simpa only [sub_add_cancel, zero_add] using hG₁.add (hG t)

/-- Against a filtered pre-Brownian motion, **every** sequence of left-measurable simple holdings
whose pathwise square-energy error on `(0, t]` tends to zero in probability has elementary gains
at `t` converging in probability to `I t`. Path continuity of `W` is not needed. -/
theorem tendstoInMeasure_simpleGains (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ m, MonotoneOn (τ m) (Iic (n m)))
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ m) (n m) (a m) W t) atTop (I t) := by
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hI.exists_seq_approx t
  have href (m : ℕ) := exists_clipped_diff_grid (ℱ := ℱ) t (hτ m) (ha m) (hτ₂ m) (ha₂ m)
  choose N grid height hgrid hgrid_le hheight hhold hgains using href
  have henergy : TendstoInMeasure P
      (fun m ↦ Probability.elementaryEnergy (grid m) (height m) (N m)) atTop (fun _ ↦ 0) := by
    have hle (m : ℕ) (ω : Ω) :
        ENNReal.ofReal (Probability.elementaryEnergy (grid m) (height m) (N m) ω) ≤
          2 * ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t +
          2 * ∫⁻ s, ‖Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t := by
      rw [← lintegral_enorm_sq_simpleHolding_eq (hgrid m) (hgrid_le m) ω]
      have heq : (∫⁻ s, ‖Finance.simpleHolding (grid m) (N m) (height m) s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t) =
          ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω -
            Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t := by
        refine lintegral_congr_ae ?_
        filter_upwards [Probability.ae_mem_Ioc_timeMeasure t] with s hs
        rw [hhold m s hs.2 ω]
      rw [heq]
      exact lintegral_enorm_sq_sub_le_two_mul_timeMeasure t
        (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω)
        (fun s ↦ Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)
        (fun s ↦ H s ω)
        ((((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
          |>.comp measurable_prodMk_right)
    refine tendstoInMeasure_iff_norm.2 fun δ hδ ↦ ?_
    have htail := tendsto_measure_ge_zero_of_ae_le hE hE₂ (fun m ↦ .of_forall (hle m))
      (ENNReal.ofReal_pos.2 hδ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω hω ↦ ?_
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (Probability.elementaryEnergy_nonneg (hgrid m) ω)] at hω ⊢
    exact ENNReal.ofReal_le_ofReal hω
  have hdiff := (hW.tendstoInMeasure_sum_mul_sub_of_energy hgrid hheight henergy).congr_left
    fun m ↦ .of_forall (hgains m W)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hG₂

/-- Every Itô integral against a filtered pre-Brownian motion vanishes almost surely at time
zero. -/
theorem eval_zero_ae_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  have h0 : TendstoInMeasure P
      (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ _ ↦ 0) W 0) atTop (I 0) := by
    refine hI.tendstoInMeasure_simpleGains hW (fun _ ↦ monotoneOn_const)
      (fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim) fun ε hε ↦ ?_
    simp [Probability.timeMeasure_zero, hε.ne']
  have hconst : TendstoInMeasure P
      (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ _ ↦ 0) W 0) atTop (0 : Ω → ℝ) :=
    fun ε hε ↦ by simp [Finance.simpleGains_def, hε.ne']
  exact tendstoInMeasure_ae_unique h0 hconst

/-- **Uniqueness of the Itô integral.** Against a filtered pre-Brownian motion, any two Itô
integrals of the same integrand are indistinguishable. -/
theorem indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J := by
  have hmod (t : ℝ≥0) : I t =ᵐ[P] J t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hJ.exists_seq_approx t
    exact tendstoInMeasure_ae_unique (hI.tendstoInMeasure_simpleGains hW hτ ha hE) hG
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ℝ≥0
  filter_upwards [hI.ae_continuous, hJ.ae_continuous, (ae_ball_iff hDc).2 fun q _ ↦ hmod q]
    with ω hIω hJω hDω t
  exact EqOn.closure hDω hIω hJω (hDd t)

/-- Two Itô integrals whose integrands agree almost everywhere in time on almost every path are
indistinguishable. -/
theorem indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ K s ω)) :
    I ≡ᵐ[P] J :=
  (hI.congr_ae hJ.isStronglyPredictable hHK).indist hW hJ

/-- **Product-almost-everywhere congruence of Itô integrals.** Against a filtered pre-Brownian
motion, Itô integrals of integrands agreeing `(timeMeasure T).prod P`-almost everywhere on every
finite horizon are indistinguishable. -/
theorem indist_of_ae_eq_prod (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry K) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine hI.indist_of_ae_eq hW hJ fun T ↦ ?_
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := Probability.timeMeasure T))
    |>.quasiMeasurePreserving.ae_eq_comp (hHK T)
  exact Measure.ae_ae_of_ae_prod hswap

end IsItoIntegral

end TauCeti
