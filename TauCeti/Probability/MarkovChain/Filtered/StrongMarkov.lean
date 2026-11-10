/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Probability.MarkovChain.Filtered.Path
public import TauCeti.Probability.Process.StoppedValue
public import TauCeti.MeasureTheory.Integral.Bind

/-!
# Filtration-relative strong Markov laws for the whole future

For a countable-state process satisfying `IsMarkovChain ℱ X κ μ`, the future path
at an `ℱ`-stopping time, conditional on the stopped sigma-algebra, has the law of
the chain started at the stopped state. The future includes that state as its
zeroth coordinate. We give restricted path laws, event identities and conditional
expectations of integrable Banach-valued path tests, with bounded real specializations.

Every assertion at a possibly infinite stopping time is restricted to its finite-time
event. Thus the arbitrary stopped values on nontermination do not enter the laws.
The almost-surely finite specialization removes this restriction. The filtration is
the one in the Markov hypothesis: it need not be the natural history, and no claim
is made for arbitrary enlargements. Only finiteness of the sample measure is needed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Theorem 1.4.2.

The decomposition into stopping-time slices follows the canonical-path proof in
`MeasureTheory.Measure.markovChainLaw_restrict_map_stoppedValue_shift_iterate`;
here the deterministic input is the filtration-relative future-path law. The integrable-test
argument follows `MeasureTheory.Measure.condExp_stoppedValue_shift_iterate_markovChainLaw`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set

namespace TauCeti.Probability.IsMarkovChain

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S]
  [Countable S] [Nonempty S] [MeasurableSingletonClass S]
  {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}
  [IsFiniteMeasure μ] [IsMarkovKernel κ] {τ : Ω → WithTop ℕ}

/-- On any stopped-history event, restricted to finite stopping, the entire future
has the path law with initial measure given by the stopped state on that event.
Neither boundedness nor almost-sure finiteness of the stopping time is required. -/
theorem map_stoppedValue_processShift_restrict (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue (processShift X) τ) =
      markovChainLaw ((μ.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue X τ)) κ := by
  have hθ := measurable_stoppedValue_of_countable
    (fun n => measurable_processShift (fun _ => h.adapted.measurable) (m := n)) hτ.measurable'
  have hY := (h.adapted.measurable_stoppedValue hτ).mono hτ.measurableSpace_le le_rfl
  let E (n : ℕ) := A ∩ {ω | τ ω = WithTop.some n}
  have hEn (n : ℕ) : MeasurableSet[ℱ n] (E n) :=
    (hτ.measurableSet_inter_eq_iff A n).1 (hA.inter (hτ.measurableSet_eq_of_countable' n))
  have hE (n : ℕ) : MeasurableSet (E n) := ℱ.le n _ (hEn n)
  have hU : A ∩ {ω | τ ω ≠ ⊤} = ⋃ n, E n := by
    ext ω
    cases heq : τ ω <;> simp [E, heq]
  have hd : Pairwise (Function.onFun Disjoint E) := fun m n hmn =>
    disjoint_left.2 fun ω hm hn => hmn (WithTop.coe_injective (hm.2.symm.trans hn.2))
  rw [hU, Measure.restrict_iUnion hd hE, Measure.map_sum hθ.aemeasurable,
    Measure.map_sum hY.aemeasurable, Measure.markovChainLaw_eq_comp,
    Measure.bind_sum _ _ κ.markovChainKernel.aemeasurable]
  congr 1
  funext n
  have hτn : ∀ᵐ ω ∂μ.restrict (E n), τ ω = WithTop.some n :=
    ae_restrict_of_forall_mem (hE n) fun ω hω => hω.2
  have hθn : (μ.restrict (E n)).map (stoppedValue (processShift X) τ) =
      (μ.restrict (E n)).map (processShift X n) :=
    Measure.map_congr (hτn.mono fun ω hω => by
      simp only [stoppedValue, hω, WithTop.untopA, WithTop.untopD_coe])
  have hYn : (μ.restrict (E n)).map (stoppedValue X τ) =
      (μ.restrict (E n)).map (X n) :=
    Measure.map_congr (hτn.mono fun ω hω => by
      simp only [stoppedValue, hω, WithTop.untopA, WithTop.untopD_coe])
  rw [hθn, hYn, ← Measure.markovChainLaw_eq_comp]
  exact h.map_processShift_restrict n (hEn n)

/-- The joint event identity for stopped information and a measurable whole-future
path event. Both sides ignore nontermination. -/
theorem measure_inter_stoppedValue_processShift_preimage (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    μ (A ∩ {ω | τ ω ≠ ⊤} ∩ stoppedValue (processShift X) τ ⁻¹' B) =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, κ.markovChainKernel (stoppedValue X τ ω) B ∂μ := by
  have hθ := measurable_stoppedValue_of_countable
    (fun n => measurable_processShift (fun _ => h.adapted.measurable) (m := n)) hτ.measurable'
  have hY := (h.adapted.measurable_stoppedValue hτ).mono hτ.measurableSpace_le le_rfl
  have heq := congrArg (fun ν : Measure (ℕ → S) => ν B)
    (h.map_stoppedValue_processShift_restrict hτ hA)
  rw [Measure.map_apply hθ hB, Measure.restrict_apply (hθ hB),
    Measure.markovChainLaw_eq_comp, Measure.bind_apply hB κ.markovChainKernel.aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) hY] at heq
  simpa only [inter_comm] using heq

/-- At a possibly infinite stopping time, the conditional expectation of an integrable
Banach-valued whole-future test is its integral against the path-law kernel at the
stopped state, with both sides masked by the finite-time event. Integrability is
required only for the future-path law on that event. -/
theorem condExp_stoppedValue_processShift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : IsMarkovChain ℱ X κ μ) (hτ : IsStoppingTime ℱ τ) {f : (ℕ → S) → E}
    (hf : Integrable f (markovChainLaw
      ((μ.restrict {ω | τ ω ≠ ⊤}).map (stoppedValue X τ)) κ)) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => f (stoppedValue (processShift X) τ ω))
        | hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => ∫ w, f w ∂κ.markovChainKernel (stoppedValue X τ ω)) := by
  let T := {ω | τ ω ≠ ⊤}
  let θ := stoppedValue (processShift X) τ
  let Y := stoppedValue X τ
  let g : S → E := fun z => ∫ w, f w ∂κ.markovChainKernel z
  have hθ : Measurable θ := measurable_stoppedValue_of_countable
    (fun n => measurable_processShift (fun _ => h.adapted.measurable) (m := n)) hτ.measurable'
  have hYτ := h.adapted.measurable_stoppedValue hτ
  have hY := hYτ.mono hτ.measurableSpace_le le_rfl
  have hSτ : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    (hτ.measurable (measurableSet_singleton ⊤)).compl
  have hS : MeasurableSet {ω | τ ω ≠ ⊤} := hτ.measurableSpace_le _ hSτ
  -- The future law on a stopped event is dominated by its law on all finite stopping.
  have hlaw (A) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (μ.restrict (A ∩ T)).map θ = markovChainLaw ((μ.restrict (A ∩ T)).map Y) κ :=
    h.map_stoppedValue_processShift_restrict hτ hA
  have hfT : (μ.restrict T).map θ = markovChainLaw ((μ.restrict T).map Y) κ := by
    simpa using hlaw univ MeasurableSet.univ
  have hfA (A) (hA : MeasurableSet[hτ.measurableSpace] A) :
      Integrable f (markovChainLaw ((μ.restrict (A ∩ T)).map Y) κ) := by
    rw [← hlaw A hA]
    refine hf.mono_measure ?_
    rw [← hfT]
    exact Measure.map_mono (Measure.restrict_mono inter_subset_right le_rfl) hθ
  -- Mixture integration transfers integrability to the conditional path-law integral.
  have hbind {ν : Measure S} (hν : Integrable f (markovChainLaw ν κ)) :
      Integrable g ν ∧ ∫ w, f w ∂markovChainLaw ν κ = ∫ z, g z ∂ν := by
    rw [Measure.markovChainLaw_eq_comp] at hν ⊢
    exact ⟨Measure.integrable_integral_bind κ.markovChainKernel.measurable hν,
      Measure.integral_bind κ.markovChainKernel.measurable.aemeasurable hν⟩
  have hgT : Integrable g ((μ.restrict T).map Y) := (hbind hf).1
  have hfi : Integrable (T.indicator fun ω => f (θ ω)) μ := by
    rw [integrable_indicator_iff hS]
    rw [← hfT] at hf
    exact (integrable_map_measure hf.1 hθ.aemeasurable).1 hf
  have hgi : Integrable (T.indicator fun ω => g (Y ω)) μ := by
    rw [integrable_indicator_iff hS]
    exact (integrable_map_measure hgT.1 hY.aemeasurable).1 hgT
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hfi
    (fun _ _ _ => hgi.integrableOn) (fun A hA _ => ?_) ?_).symm
  · rw [setIntegral_indicator hS, setIntegral_indicator hS,
      ← integral_map hY.aemeasurable (hbind (hfA A hA)).1.1,
      ← (hbind (hfA A hA)).2, ← hlaw A hA,
      integral_map hθ.aemeasurable (by rw [hlaw A hA]; exact (hfA A hA).1)]
  · -- Choose a stopped-measurable version on finite stopping, then extend it by zero.
    have hgm : AEStronglyMeasurable[hτ.measurableSpace] (fun ω => g (Y ω)) (μ.restrict T) :=
      (hgT.1.comp_ae_measurable' hY.aemeasurable).mono (measurable_iff_comap_le.1 hYτ)
    refine ⟨T.indicator (hgm.mk _), hgm.stronglyMeasurable_mk.indicator hSτ, ?_⟩
    filter_upwards [(ae_restrict_iff' hS).1 hgm.ae_eq_mk] with ω hω
    by_cases hωT : ω ∈ T
    · simp [indicator_of_mem hωT, hω hωT]
    · simp [indicator_of_notMem hωT]

/-- The masked whole-future conditional expectation for a bounded measurable real test. -/
theorem condExp_stoppedValue_processShift_of_bounded (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) {f : (ℕ → S) → ℝ} (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => f (stoppedValue (processShift X) τ ω))
        | hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => ∫ w, f w ∂κ.markovChainKernel (stoppedValue X τ ω)) := by
  have : IsFiniteMeasure (markovChainLaw
      ((μ.restrict {ω | τ ω ≠ ⊤}).map (stoppedValue X τ)) κ) := by
    rw [Measure.markovChainLaw_eq_comp]
    infer_instance
  obtain ⟨C, hC⟩ := hb
  exact h.condExp_stoppedValue_processShift hτ
    ⟨hf.aestronglyMeasurable, .of_bounded (Eventually.of_forall hC)⟩

/-- Conditional probabilities of measurable whole-future events at a stopping time,
relative to its stopped sigma-algebra. The conditional probability is zero on
nontermination. -/
theorem condExp_indicator_stoppedValue_processShift (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    μ[({ω | τ ω ≠ ⊤} ∩ stoppedValue (processShift X) τ ⁻¹' B).indicator (fun _ => (1 : ℝ))
        | hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => (κ.markovChainKernel (stoppedValue X τ ω)).real B) := by
  have hb : ∃ C : ℝ, ∀ w, ‖B.indicator (fun _ => (1 : ℝ)) w‖ ≤ C :=
    ⟨1, fun w => by by_cases hw : w ∈ B <;> simp [hw]⟩
  simpa only [← Set.indicator_comp_right, Function.comp_def, Set.indicator_indicator,
    integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one] using
    h.condExp_stoppedValue_processShift_of_bounded hτ (measurable_const.indicator hB) hb

/-- For an almost surely finite stopping time, the whole-future law on a stopped-history
event needs no finite-time restriction. -/
theorem map_stoppedValue_processShift_restrict_of_ae_ne_top (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (stoppedValue (processShift X) τ) =
      markovChainLaw ((μ.restrict A).map (stoppedValue X τ)) κ := by
  have heq : μ.restrict (A ∩ {ω | τ ω ≠ ⊤}) = μ.restrict A :=
    Measure.restrict_congr_set (inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.2 hfin))
  simpa only [heq] using h.map_stoppedValue_processShift_restrict hτ hA

/-- For an almost surely finite stopping time, the unmasked conditional expectation
of an integrable Banach-valued test is the path-law integral at the stopped state. -/
theorem condExp_stoppedValue_processShift_of_ae_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : IsMarkovChain ℱ X κ μ) (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {f : (ℕ → S) → E} (hf : Integrable f (markovChainLaw (μ.map (stoppedValue X τ)) κ)) :
    μ[fun ω => f (stoppedValue (processShift X) τ ω) | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∫ w, f w ∂κ.markovChainKernel (stoppedValue X τ ω) := by
  have hT : μ.restrict {ω | τ ω ≠ ⊤} = μ := Measure.restrict_eq_self_of_ae_mem hfin
  have hind (g : Ω → E) : {ω | τ ω ≠ ⊤}.indicator g =ᵐ[μ] g :=
    hfin.mono fun ω hω => indicator_of_mem hω g
  rw [← hT] at hf
  exact (condExp_congr_ae (hind _)).symm.trans
    ((h.condExp_stoppedValue_processShift hτ hf).trans (hind _))

/-- For an almost surely finite stopping time, the unmasked bounded real-test
conditional expectation is the path-law integral at the stopped state. -/
theorem condExp_stoppedValue_processShift_of_ae_ne_top_of_bounded
    (h : IsMarkovChain ℱ X κ μ) (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {f : (ℕ → S) → ℝ} (hf : Measurable f) (hb : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) :
    μ[fun ω => f (stoppedValue (processShift X) τ ω) | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∫ w, f w ∂κ.markovChainKernel (stoppedValue X τ ω) := by
  have : IsFiniteMeasure (markovChainLaw (μ.map (stoppedValue X τ)) κ) := by
    rw [Measure.markovChainLaw_eq_comp]
    infer_instance
  obtain ⟨C, hC⟩ := hb
  exact h.condExp_stoppedValue_processShift_of_ae_ne_top hτ hfin
    ⟨hf.aestronglyMeasurable, .of_bounded (Eventually.of_forall hC)⟩

end TauCeti.Probability.IsMarkovChain
