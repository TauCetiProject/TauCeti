/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Recurrence
public import TauCeti.Probability.MarkovChain.ReturnGaps
public import TauCeti.Probability.Renewal.StrongLaw

/-!
# Long-run occupation frequencies of a Markov chain

Let `X` be the coordinate process on path space `ℕ → α` under the path law `markovChainLaw ν κ`.
For a state `y`, the number of visits to `y` at the times `1, …, n` is

`V_y(n) = visitCount (fun k => X (k + 1)) y n`,

and `m_y = κ.meanReturnTime y` is the mean first return time of the chain started at `y`. Write
`r_y = (m_y⁻¹).toReal`, with the inverse taken in `ℝ≥0∞`, so that `r_y = 0` when `m_y = ∞`. This
file identifies the long-run occupation frequency of `y` as `r_y`:

* started at `y`, `V_y(n) / n → r_y` almost surely
  (`ProbabilityTheory.Kernel.ae_tendsto_visitCount_div_markovChainLaw_dirac`);
* from any finite initial law, `V_y(n) / n` converges almost surely to `r_y` on the event that the
  chain ever enters `y`, and to zero off that event
  (`MeasureTheory.Measure.ae_tendsto_visitCount_div_markovChainLaw`);
* the mean occupation frequency converges to `ℙ(H_y < ∞) * r_y`, where `H_y` is the first
  entrance time to `y` (`MeasureTheory.Measure.tendsto_integral_visitCount_div_markovChainLaw`).

The state space is countable with measurable singletons; no recurrence, irreducibility or
finite-mean hypothesis is made. At a recurrent state the successive return gaps are independent
with the law of the first return time, and `V_y(n)` is exactly the renewal count of these gaps at
time `n` (`TauCeti.Probability.renewalCountNat_returnGap`), so the renewal law of large numbers
applies; it covers infinite mean through the truncated strong law. At a transient state the
visits are almost surely finite and `m_y = ∞`, so both sides vanish. A general initial law reduces
to a start at `y` by the strong Markov property at the first entrance, since occupation
frequencies forget a finite initial segment of the path
(`TauCeti.Probability.tendsto_visitCount_div_of_tendsto_comp_add`).

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.10, Theorem 1.10.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω α : Type*} {X : ℕ → Ω → α} {a : α} {ω : Ω}

/-- **Visits as renewals.** For a path that starts at `a` and visits `a` infinitely often, the
number of visits to `a` at the times `1, …, n` is the renewal count at time `n` of the successive
return gaps. -/
theorem renewalCountNat_returnGap (hinf : {n | X n ω = a}.Infinite) (h0 : X 0 ω = a) (n : ℕ) :
    renewalCountNat (fun k ω => (returnGap X a k ω : ℝ≥0)) n ω =
      visitCount (fun k => X (k + 1) ω) a n := by
  set T : ℕ → Ω → ℝ≥0 := fun k ω => (returnGap X a k ω : ℝ≥0)
  have harr (m : ℕ) : arrival T m ω = ((∑ i ∈ Finset.range m, returnGap X a i ω : ℕ) : ℝ≥0) := by
    simp [T, arrival_def]
  -- Every gap is at least one, so the arrivals do not accumulate.
  have hω : Tendsto (fun m => arrival T m ω) atTop atTop := by
    refine tendsto_atTop_mono (fun m => ?_) (tendsto_natCast_atTop_atTop (R := ℝ≥0))
    rw [harr, Nat.cast_le]
    calc m = ∑ _i ∈ Finset.range m, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        returnGap_pos (exists_visitCount_of_infinite hinf (i + 1))
  have hcount : visitCount (fun k => X k ω) a (n + 1) =
      visitCount (fun k => X (k + 1) ω) a n + 1 := by
    rw [add_comm n 1, visitCount_add, visitCount_succ_of_eq h0, visitCount_zero, add_comm]
    simp only [add_comm 1]
  refine eq_of_forall_le_iff fun m => ?_
  have h := successiveVisit_le_iff (X := X) (a := a) (k := m) (ω := ω) (n := n)
  rw [successiveVisit_eq_sum_returnGap (exists_visitCount_of_infinite hinf m) h0, hcount,
    Nat.lt_succ_iff] at h
  rw [le_renewalCountNat_iff hω, harr, Nat.cast_le, ← h]
  norm_cast

/-- **Occupation frequencies forget a finite initial segment.** If the sequence delayed by `N`
spends asymptotic proportion `r` of its time at `a`, so does the original sequence. -/
theorem tendsto_visitCount_div_of_tendsto_comp_add {x : ℕ → α} {r : ℝ} (N : ℕ)
    (h : Tendsto (fun n : ℕ => (visitCount (fun k => x (k + N)) a n : ℝ) / n) atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => (visitCount x a n : ℝ) / n) atTop (𝓝 r) := by
  -- Up to time `n + N` there are the visits before `N` and those of the delayed sequence; neither
  -- this constant nor the delay changes the limit.
  have hlim : Tendsto (fun n : ℕ => ((visitCount x a N : ℝ) / n +
      (visitCount (fun k => x (k + N)) a n : ℝ) / n) * ((n : ℝ) / (n + N)))
      atTop (𝓝 ((0 + r) * 1)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat _).add h).mul (tendsto_natCast_div_add_atTop _)
  rw [zero_add, mul_one] at hlim
  refine (tendsto_add_atTop_iff_nat N).1 (hlim.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [add_comm n N, visitCount_add, Nat.cast_add, Nat.cast_add]
  simp only [add_comm N]
  field_simp
  ring

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ] {y : α}

/-- At a recurrent state, the mean of a return gap is the mean return time. -/
theorem IsRecurrent.lintegral_returnGap [Countable α] (hy : κ.IsRecurrent y) (k : ℕ) :
    ∫⁻ x, (returnGap (fun n (x : ℕ → α) => x n) y k x : ℝ≥0∞)
        ∂markovChainLaw (Measure.dirac y) κ = κ.meanReturnTime y := by
  have hlaw := (HasLaw.id (μ := markovChainLaw (Measure.dirac y) κ))
    |>.natCast_returnGap_map_hittingAfter (isRecurrent_iff.mp hy) k
  have hT : Measurable (hittingAfter (fun n (x : ℕ → α) => x n) {y} 1) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton y)).measurable'
  have hf : Measurable fun t : WithTop ℕ => ENat.toENNReal t := Measurable.of_discrete
  rw [meanReturnTime_def, ← MeasureTheory.lintegral_map hf hT,
    ← hlaw.lintegral_comp hf.aemeasurable]
  exact lintegral_congr fun x => (ENat.toENNReal_coe _).symm

/-- **Occupation frequency at a recurrent state.** Started at a recurrent state `y`, the
proportion of the times `1, …, n` spent at `y` converges almost surely to the inverse mean
return time. -/
private theorem IsRecurrent.ae_tendsto_visitCount_div [Countable α] (hy : κ.IsRecurrent y) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  set P := markovChainLaw (Measure.dirac y) κ
  set T : ℕ → (ℕ → α) → ℝ≥0 := fun k x => (returnGap (fun n (x : ℕ → α) => x n) y k x : ℝ≥0)
  have ha := isRecurrent_iff.mp hy
  have hcast : Measurable fun n : ℕ => (n : ℝ≥0) := Measurable.of_discrete
  have hlaw := κ.hasLaw_returnGap ha
  have hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (T i) (T j) P := fun i j hij =>
    ((κ.iIndepFun_returnGap ha).indepFun hij).comp hcast hcast
  have hid (k : ℕ) : IdentDistrib (T k) (T 0) P P := ((hlaw k).identDistrib (hlaw 0)).comp hcast
  have hinf := κ.ae_infinite_setOf_eq_markovChainLaw_dirac ha
  have h0 := markovChainLaw_dirac_ae_apply_zero κ y
  -- The first gap is a return time, hence positive.
  have hzero : P {x | T 0 x = 0} < 1 := by
    have hnull : P {x | T 0 x = 0} = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hinf] with x hx
      simpa [T] using (returnGap_pos (X := fun n (x : ℕ → α) => x n) (ω := x)
        (exists_visitCount_of_infinite hx 1)).ne'
    simp [hnull]
  have hmean : ∫⁻ x, (T 0 x : ℝ≥0∞) ∂P = κ.meanReturnTime y := by
    simpa [T] using hy.lintegral_returnGap κ 0
  filter_upwards [ae_tendsto_renewalCountNat_div hindep hid hzero, hinf, h0] with x hlim hx hx0
  rw [hmean] at hlim
  refine (hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))).congr fun n => ?_
  have hV : renewalCountNat T n x = visitCount (fun k => x (k + 1)) y n :=
    renewalCountNat_returnGap (X := fun n (x : ℕ → α) => x n) hx hx0 n
  simp only [Function.comp_apply, NNReal.coe_natCast, hV]

/-- **Long-run occupation frequency, started at the state.** Started at `y`,
the proportion `V_y(n) / n` of the times `1, …, n` spent at `y` converges almost surely to
`r_y = (m_y⁻¹).toReal`, where `m_y` is the mean return time. In particular the limit is zero when
`y` is transient or null recurrent. -/
theorem ae_tendsto_visitCount_div_markovChainLaw_dirac [Countable α] (y : α) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  by_cases hy : κ.IsRecurrent y
  · exact hy.ae_tendsto_visitCount_div κ
  -- A transient state has infinite mean return time and is visited only finitely often.
  replace hy : κ.IsTransient y := isTransient_iff.mpr hy
  rw [hy.meanReturnTime_eq_top, ENNReal.inv_top, ENNReal.toReal_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero (Measure.dirac y) κ
      (isTransient_iff_return_probability_lt_one.mp hy))] with x hx
  have hfin : (Set.ofPred fun k => x (k + 1) = y).Finite :=
    (Set.not_infinite.1 hx).preimage (fun _ _ _ _ h => Nat.succ_injective h)
  classical
  refine squeeze_zero (fun n => by positivity) (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (hfin.toFinset.card : ℝ))
  gcongr
  rw [visitCount_eq_count]
  exact_mod_cast Nat.count_le_card hfin n

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

/-- **Long-run occupation frequencies.** From any finite initial law, the
proportion `V_y(n) / n` of the times `1, …, n` spent at `y` converges almost surely to
`r_y = (m_y⁻¹).toReal` on the event that the chain enters `y`, and to zero off that event. -/
theorem ae_tendsto_visitCount_div_markovChainLaw [IsFiniteMeasure ν] (y : α) :
    ∀ᵐ x ∂markovChainLaw ν κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop
        (𝓝 ({x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 0 x ≠ ⊤}.indicator
          (fun _ => (κ.meanReturnTime y)⁻¹.toReal) x)) := by
  set τ := hittingAfter (fun n (x : ℕ → α) => x n) {y} 0
  set θ := stoppedValue (fun n => (shift α)^[n]) τ
  set r := (κ.meanReturnTime y)⁻¹.toReal
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ :=
    Filtration.adapted_piLE.isStoppingTime_hittingAfter (measurableSet_singleton y)
  have hθ : Measurable θ :=
    measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hτ.measurable'
  have hS : MeasurableSet (Set.univ ∩ {x | τ x ≠ ⊤}) :=
    MeasurableSet.univ.inter ((measurableSet_singleton ⊤).preimage hτ.measurable').compl
  have hy : ∀ x ∈ Set.univ ∩ {x | τ x ≠ ⊤}, stoppedValue (fun n (x : ℕ → α) => x n) τ x = y :=
    fun x hx => hittingAfter_mem_set_of_ne_top hx.2
  -- By the strong Markov property at the first entrance, the path seen from there is a chain
  -- started at `y`, so its occupation frequency converges to `r`.
  have hlaw := markovChainLaw_restrict_map_stoppedValue_shift_iterate_eq_smul ν κ hτ
    MeasurableSet.univ hy
  have hfuture : ∀ᵐ x ∂(markovChainLaw ν κ).restrict (Set.univ ∩ {x | τ x ≠ ⊤}),
      Tendsto (fun n : ℕ => (visitCount (fun k => θ x (k + 1)) y n : ℝ) / n) atTop (𝓝 r) := by
    refine ae_of_ae_map (p := fun z => Tendsto
      (fun n : ℕ => (visitCount (fun k => z (k + 1)) y n : ℝ) / n) atTop (𝓝 r))
      hθ.aemeasurable ?_
    rw [hlaw]
    exact ae_smul_measure (κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y) _
  filter_upwards [(ae_restrict_iff' hS).1 hfuture] with x hx
  by_cases hτx : τ x = ⊤
  · -- A path that never enters `y` has no visits.
    have hne : ∀ k, x (k + 1) ≠ y := fun k => hittingAfter_eq_top_iff.1 hτx (k + 1) (by omega)
    simp only [Set.indicator_of_notMem (s := {x | τ x ≠ ⊤}) (a := x) (not_not.2 hτx),
      visitCount_eq_zero_of_forall_ne fun k _ => hne k, CharP.cast_eq_zero, zero_div,
      tendsto_const_nhds]
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hτx
  have hθx : θ x = (shift α)^[N] x := by
    simp only [θ, stoppedValue, ← hN, WithTop.untopD_coe]
  have hlim := hx ⟨trivial, hτx⟩
  rw [hθx] at hlim
  simp only [Set.indicator_of_mem (s := {x | τ x ≠ ⊤}) (a := x) hτx]
  -- The path seen from the entrance time `N` has the same occupation frequency.
  refine tendsto_visitCount_div_of_tendsto_comp_add N (hlim.congr fun n => ?_)
  simp only [shift_iterate_apply]
  exact congrArg (fun z : ℕ → α => (visitCount z y n : ℝ) / n)
    (funext fun k => congrArg x (by omega))

/-- **Mean occupation frequencies.** From any finite initial law, the mean proportion of the times
`1, …, n` spent at `y` converges to `ℙ(H_y < ∞) * r_y`, where `H_y` is the first entrance time to
`y` and `r_y = (m_y⁻¹).toReal`. -/
theorem tendsto_integral_visitCount_div_markovChainLaw [IsFiniteMeasure ν] (y : α) :
    Tendsto (fun n : ℕ => ∫ x, (visitCount (fun k => x (k + 1)) y n : ℝ) / n
        ∂markovChainLaw ν κ) atTop
      (𝓝 ((markovChainLaw ν κ).real {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 0 x ≠ ⊤} *
        (κ.meanReturnTime y)⁻¹.toReal)) := by
  have hE : MeasurableSet {x : ℕ → α | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} :=
    ((measurableSet_singleton ⊤).preimage
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton y)).measurable').compl
  rw [← smul_eq_mul, ← integral_indicator_const _ hE]
  -- The frequencies lie in `[0, 1]`, so bounded convergence applies.
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
    (integrable_const 1) (fun n => ?_) (ae_tendsto_visitCount_div_markovChainLaw ν κ y)
  · have hV := measurable_visitCount_comp (P := fun (x : ℕ → α) k => x (k + 1)) y n
      (measurableSet_singleton y) fun i _ => measurable_pi_apply (i + 1)
    exact ((Measurable.of_discrete (f := fun m : ℕ => (m : ℝ))).comp hV).div_const _
      |>.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg n)
    classical
    rw [visitCount_eq_count]
    exact_mod_cast Nat.count_le _

end MeasureTheory.Measure
