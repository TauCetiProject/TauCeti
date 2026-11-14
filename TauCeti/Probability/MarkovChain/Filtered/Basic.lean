/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# Markov chains relative to a filtration

`IsMarkovChain ℱ X κ μ` states the one-step Markov property with respect to the specified
filtration `ℱ`, including measurable adaptation. Its test functions are bounded measurable
real functions. The initial distribution is separate from this property.

The multi-step conditional law is expressed using powers of the same transition kernel.
The property descends to a smaller filtration to which the process is still adapted;
it makes no assertion about enlarging the filtration. On any state space the one-step
property for the history filtration is equivalent to finite-prefix recursion.
Together with an initial law, it characterizes the Markov-chain path law for Mathlib's
natural filtration. The coordinate process supplies a canonical realization.

The history-filtration characterization needs neither a topology nor countability of the state
space; its forward direction, `TauCeti.Probability.IsMarkovChain.map_prefix_succ_eq_compProd`,
holds for any filtration. The natural-filtration corollary uses a metrizable Borel topology on
the state space only to form Mathlib's natural filtration.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.1.
-/

public section

open MeasureTheory ProbabilityTheory Filter

namespace TauCeti.Probability

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S]

/-- A measurably adapted process is a homogeneous Markov chain relative to `ℱ` if the
conditional expectation of each bounded measurable real function of the next state is its
integral against the transition kernel at the current state. The initial law is not specified. -/
structure IsMarkovChain (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure Ω) : Prop where
  adapted : Adapted ℱ X
  condExp_eq : ∀ (n : ℕ) (f : S → ℝ), Measurable f →
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
    μ[fun ω => f (X (n + 1) ω) | ℱ n] =ᵐ[μ] fun ω => ∫ y, f y ∂κ (X n ω)

namespace IsMarkovChain

variable {ℱ 𝒢 : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}
  [IsMarkovKernel κ]

/-- The measure of a Markov chain is finite. This supplies the finite-measure hypothesis of the
conditional-expectation results about `IsMarkovChain ℱ X κ μ`, which therefore do not assume it. -/
theorem isFiniteMeasure (h : IsMarkovChain ℱ X κ μ) : IsFiniteMeasure μ := by
  -- The conditional expectation of the constant `1` is integrable, and it is almost everywhere
  -- the integral of `1` against the Markov kernel, that is, `1` itself.
  have hc := h.condExp_eq 0 (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  exact (integrable_const_iff_isFiniteMeasure (c := (1 : ℝ)) one_ne_zero).1
    (by simpa using integrable_condExp.congr hc)

/-- The multi-step conditional law of a chain relative to its given filtration. This includes
zero steps, when adaptation makes the tested current state measurable for the conditioning. -/
theorem condExp_add (h : IsMarkovChain ℱ X κ μ) (n k : ℕ) {f : S → ℝ}
    (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    μ[fun ω => f (X (n + k) ω) | ℱ n] =ᵐ[μ]
      fun ω => ∫ y, f y ∂(κ ^ k) (X n ω) := by
  have := h.isFiniteMeasure
  obtain ⟨C, hC⟩ := hb
  induction k generalizing f with
  | zero =>
      simp only [Nat.add_zero, pow_zero, Kernel.one_def, Kernel.id_apply,
        integral_dirac' _ _ hf.stronglyMeasurable]
      exact (condExp_of_stronglyMeasurable (μ := μ) (ℱ.le n)
        (hf.comp (h.adapted n)).stronglyMeasurable
        ⟨(hf.comp h.adapted.measurable).aestronglyMeasurable,
          .of_bounded (Eventually.of_forall fun ω => hC (X n ω))⟩).eventuallyEq
  | succ k ih =>
      let g : S → ℝ := fun x => ∫ y, f y ∂κ x
      have hg : Measurable g := hf.stronglyMeasurable.integral_kernel.measurable
      have hgC : ∀ x, ‖g x‖ ≤ C := fun x => by
        simpa using norm_integral_le_of_norm_le_const
          (μ := κ x) (Eventually.of_forall hC)
      have hstep := h.condExp_eq (n + k) f hf ⟨C, hC⟩
      have htower := condExp_condExp_of_le (μ := μ) (f := fun ω => f (X (n + k + 1) ω))
        (ℱ.mono (Nat.le_add_right n k)) (ℱ.le (n + k))
      have hind := ih hg hgC
      have hi (ν : Measure S) [IsFiniteMeasure ν] : Integrable f ν :=
        ⟨hf.aestronglyMeasurable, .of_bounded (Eventually.of_forall hC)⟩
      have heq : ∀ x, (∫ y, g y ∂(κ ^ k) x) = ∫ y, f y ∂(κ ^ (k + 1)) x := by
        intro x
        -- Use the public composition form of kernel powers rather than monoid multiplication.
        rw [Nat.add_comm k 1, Kernel.pow_add, pow_one, Kernel.integral_comp (hi _)]
      simpa only [Nat.add_assoc, heq] using
        htower.symm.trans ((condExp_congr_ae hstep).trans hind)

/-- The event form of the multi-step conditional law, including measurable sets that are not
singletons. -/
theorem condExp_indicator_add (h : IsMarkovChain ℱ X κ μ) (n k : ℕ)
    {A : Set S} (hA : MeasurableSet A) :
    μ[(X (n + k) ⁻¹' A).indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      fun ω => ((κ ^ k) (X n ω)).real A := by
  have hb : ∃ C : ℝ, ∀ x : S, ‖A.indicator (fun _ => (1 : ℝ)) x‖ ≤ C :=
    ⟨1, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩
  simpa only [← Set.indicator_comp_right, Function.comp_def,
    integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one] using
    h.condExp_add n k (measurable_const.indicator hA) hb

/-- A Markov chain remains Markov for a smaller filtration as long as it remains adapted.
This direction does not require independence from any additional information. -/
theorem mono (h : IsMarkovChain ℱ X κ μ) (hle : 𝒢 ≤ ℱ) (hX : Adapted 𝒢 X) :
    IsMarkovChain 𝒢 X κ μ := by
  have := h.isFiniteMeasure
  refine ⟨hX, fun n f hf hb => ?_⟩
  obtain ⟨C, hC⟩ := hb
  have hg : StronglyMeasurable[𝒢 n] (fun ω => ∫ y, f y ∂κ (X n ω)) :=
    hf.stronglyMeasurable.integral_kernel.comp_measurable (hX n)
  have hgi : Integrable (fun ω => ∫ y, f y ∂κ (X n ω)) μ := by
    refine ⟨hg.mono (𝒢.le n) |>.aestronglyMeasurable, .of_bounded (C := C) ?_⟩
    exact Eventually.of_forall fun ω => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := κ (X n ω)) (Eventually.of_forall hC)
  exact (condExp_condExp_of_le (hle n) (ℱ.le n)).symm.trans
    ((condExp_congr_ae (h.condExp_eq n f hf ⟨C, hC⟩)).trans
      (condExp_of_stronglyMeasurable (𝒢.le n) hg hgi).eventuallyEq)

end IsMarkovChain

/-- The coordinate process under the Markov-chain path law is Markov relative to its history
filtration. No topology or countability assumption on the state space is needed. -/
theorem isMarkovChain_markovChainLaw (ν : Measure S) [IsFiniteMeasure ν]
    (κ : Kernel S S) [IsMarkovKernel κ] :
    IsMarkovChain Filtration.piLE (fun n (x : ℕ → S) => x n) κ (markovChainLaw ν κ) := by
  refine ⟨Filtration.adapted_piLE, fun n f hf hb => ?_⟩
  obtain ⟨C, hC⟩ := hb
  have htest : Integrable (fun x : ℕ → S => f (x 1))
      (markovChainLaw ((κ ^ n : Kernel S S) ∘ₘ ν) κ) :=
    ⟨(hf.comp (measurable_pi_apply 1)).aestronglyMeasurable,
      .of_bounded (Eventually.of_forall fun x => hC (x 1))⟩
  have h := Measure.condExp_shift_iterate_markovChainLaw ν κ n htest
  have heq (x : S) : (∫ y : ℕ → S, f (y 1) ∂markovChainLaw (Measure.dirac x) κ) =
      ∫ y, f y ∂κ x := by
    rw [← integral_map (measurable_pi_apply 1).aemeasurable hf.aestronglyMeasurable,
      Measure.markovChainLaw_map_eval]
    rw [pow_one, Measure.dirac_bind κ.measurable]
  simpa only [shift_iterate_apply, Nat.add_comm 1 n, heq] using h

section History

variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}
  [IsMarkovKernel κ]

/-- **The Markov property gives the finite-prefix recursion.** For a chain relative to any
filtration, the joint law of the prefix `(X 0, …, X n)` and the next state `X (n + 1)` is the
prefix law followed by one `κ`-step out of the last coordinate. -/
theorem IsMarkovChain.map_prefix_succ_eq_compProd (h : IsMarkovChain ℱ X κ μ) (n : ℕ) :
    μ.map (fun ω => ((fun i : Fin (n + 1) => X i ω), X (n + 1) ω)) =
      prefixLaw μ X (n + 1) ⊗ₘ κ.comap
        (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _) := by
  have := h.isFiniteMeasure
  have hX : ∀ n, Measurable (X n) := fun _ => h.adapted.measurable
  have hpre : Measurable fun ω (i : Fin (n + 1)) => X i ω := measurable_pi_iff.2 fun i => hX i
  have : IsFiniteMeasure (prefixLaw μ X (n + 1)) := by
    rw [prefixLaw_def, blockLaw_def]
    infer_instance
  refine Measure.ext_prod fun {A C} hA hC => ?_
  rw [prefixLaw_compProd_apply_prod (κ := κ) hX n hA hC,
    Measure.map_apply (hpre.prodMk (hX (n + 1))) (hA.prod hC), Set.mk_preimage_prod]
  set s := (fun ω (i : Fin (n + 1)) => X i ω) ⁻¹' A
  -- The prefix event is known at time `n`.
  have hs : MeasurableSet[ℱ n] s :=
    (@Measurable.of_eval _ _ _ (ℱ n) _ _ fun i : Fin (n + 1) =>
      (h.adapted i).mono (ℱ.mono (Fin.is_le i)) le_rfl) hA
  have hfin : ∫⁻ ω in s, κ (X n ω) C ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top μ s) ?_
    calc ∫⁻ ω in s, κ (X n ω) C ∂μ ≤ ∫⁻ _ in s, 1 ∂μ := lintegral_mono fun _ => prob_le_one
      _ = μ s := setLIntegral_one s
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin).1 ?_
  -- Integrate the one-step conditional law of the event `X (n + 1) ∈ C` over the prefix event.
  have hc := h.condExp_indicator_add n 1 hC
  simp only [pow_one] at hc
  calc (μ (s ∩ X (n + 1) ⁻¹' C)).toReal
      = ∫ ω in s, (X (n + 1) ⁻¹' C).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        rw [integral_indicator_const _ ((hX (n + 1)) hC), smul_eq_mul, mul_one,
          measureReal_restrict_apply ((hX (n + 1)) hC), Set.inter_comm, measureReal_def]
    _ = ∫ ω in s, μ[(X (n + 1) ⁻¹' C).indicator (fun _ => (1 : ℝ)) | ℱ n] ω ∂μ :=
        (setIntegral_condExp (ℱ.le n)
          ((integrable_const (1 : ℝ)).indicator ((hX (n + 1)) hC)) hs).symm
    _ = ∫ ω in s, (κ (X n ω) C).toReal ∂μ :=
        setIntegral_congr_ae (ℱ.le n s hs) (hc.mono fun _ hω _ => hω)
    _ = (∫⁻ ω in s, κ (X n ω) C ∂μ).toReal :=
        integral_toReal ((κ.measurable_coe hC).comp (hX n)).aemeasurable
          (Eventually.of_forall fun _ => measure_lt_top _ _)

/-- The finite-prefix recursion gives the Markov property for the history filtration. -/
private theorem isMarkovChain_of_prefix_recursion [IsFiniteMeasure μ]
    (hℱ : ∀ n, ℱ n = MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance)
    (h : ∀ n, μ.map (fun ω => ((fun i : Fin (n + 1) => X i ω), X (n + 1) ω)) =
        prefixLaw μ X (n + 1) ⊗ₘ κ.comap
          (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _)) :
    IsMarkovChain ℱ X κ μ := by
  have hadapt := Filtration.adapted_of_eq_comap_prefix hℱ
  have hX : ∀ n, Measurable (X n) := fun _ => hadapt.measurable
  refine ⟨hadapt, fun n f hf hb => ?_⟩
  obtain ⟨C, hC⟩ := hb
  have hpre : Measurable fun ω (i : Fin (n + 1)) => X i ω := measurable_pi_iff.2 fun i => hX i
  have hg : StronglyMeasurable[ℱ n] (fun ω => ∫ y, f y ∂κ (X n ω)) :=
    hf.stronglyMeasurable.integral_kernel.comp_measurable (hadapt n)
  have hgi : Integrable (fun ω => ∫ y, f y ∂κ (X n ω)) μ :=
    ⟨(hg.mono (ℱ.le n)).aestronglyMeasurable, .of_bounded (C := C)
      (Eventually.of_forall fun ω => by
        simpa using norm_integral_le_of_norm_le_const
          (μ := κ (X n ω)) (Eventually.of_forall hC))⟩
  have : IsFiniteMeasure (prefixLaw μ X (n + 1)) := by
    rw [prefixLaw_def, blockLaw_def]
    infer_instance
  have hfi (ν : Measure ((Fin (n + 1) → S) × S)) [IsFiniteMeasure ν] :
      Integrable (fun p => f p.2) ν :=
    ⟨(hf.comp measurable_snd).aestronglyMeasurable,
      .of_bounded (Eventually.of_forall fun p => hC p.2)⟩
  -- Both sides have the same integral over each prefix event `{(X 0, …, X n) ∈ A}`.
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le n)
    ⟨(hf.comp (hX (n + 1))).aestronglyMeasurable,
      .of_bounded (Eventually.of_forall fun ω => hC (X (n + 1) ω))⟩
    (fun _ _ _ => hgi.integrableOn) (fun s hs _ => ?_) hg.aestronglyMeasurable).symm
  rw [hℱ n] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  calc ∫ ω in (fun ω (i : Fin (n + 1)) => X i ω) ⁻¹' A, ∫ y, f y ∂κ (X n ω) ∂μ
      = ∫ w in A, ∫ y, f y ∂κ (w (Fin.last n)) ∂prefixLaw μ X (n + 1) := by
        rw [prefixLaw_def, blockLaw_def,
          setIntegral_map (f := fun w : Fin (n + 1) → S => ∫ y, f y ∂κ (w (Fin.last n))) hA
            (hf.stronglyMeasurable.integral_kernel.comp_measurable
              (measurable_pi_apply _)).aestronglyMeasurable hpre.aemeasurable]
        rfl
    _ = ∫ p in A ×ˢ Set.univ, f p.2 ∂(prefixLaw μ X (n + 1) ⊗ₘ κ.comap
          (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _)) := by
        rw [Measure.setIntegral_compProd hA MeasurableSet.univ (hfi _).integrableOn]
        simp only [Measure.restrict_univ, Kernel.comap_apply]
    _ = ∫ ω in (fun ω (i : Fin (n + 1)) => X i ω) ⁻¹' A, f (X (n + 1) ω) ∂μ := by
        rw [← h n, setIntegral_map (f := fun p : (Fin (n + 1) → S) × S => f p.2)
          (hA.prod MeasurableSet.univ)
          (hf.comp measurable_snd).aestronglyMeasurable (hpre.prodMk (hX (n + 1))).aemeasurable,
          Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]

/-- On any state space, the filtration-relative test-function property for the history filtration
is equivalent to the finite-prefix recursion. The hypothesis `hℱ` identifies the information
through time `n` with that generated by `X 0, …, X n`. -/
theorem isMarkovChain_iff_prefix_recursion [IsFiniteMeasure μ]
    (hℱ : ∀ n, ℱ n = MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance) :
    IsMarkovChain ℱ X κ μ ↔
      ∀ n, μ.map (fun ω => ((fun i : Fin (n + 1) => X i ω), X (n + 1) ω)) =
        prefixLaw μ X (n + 1) ⊗ₘ κ.comap
          (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _) :=
  ⟨fun h n => h.map_prefix_succ_eq_compProd n, isMarkovChain_of_prefix_recursion hℱ⟩

/-- A process has the Markov-chain path law exactly when it has the specified initial law
and is a Markov chain relative to Mathlib's natural filtration. The state-space topology
is used only to form that filtration; no topology on the sample space is required. -/
theorem hasLaw_markovChainLaw_iff_isMarkovChain_natural
    [TopologicalSpace S] [TopologicalSpace.MetrizableSpace S] [BorelSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] (hX : ∀ n, StronglyMeasurable (X n)) :
    HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ ↔
      μ.map (X 0) = ν ∧ IsMarkovChain (Filtration.natural X hX) X κ μ := by
  have hlaw := hasLaw_markovChainLaw_iff (μ := μ) ν κ (fun n => (hX n).measurable.aemeasurable)
  refine ⟨fun h => ?_, fun h => hlaw.2 ⟨h.1, fun n => h.2.map_prefix_succ_eq_compProd n⟩⟩
  have := h.isFiniteMeasure
  exact ⟨(hlaw.1 h).1, isMarkovChain_of_prefix_recursion
    (Filtration.natural_eq_comap_prefix X hX) (hlaw.1 h).2⟩

end History

end TauCeti.Probability
