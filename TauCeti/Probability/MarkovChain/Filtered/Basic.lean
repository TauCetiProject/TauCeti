/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Kernel.Composition.Power
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Markov chains relative to a filtration

`IsMarkovChain ℱ X κ μ` states the one-step Markov property with respect to the specified
filtration `ℱ`, including measurable adaptation. Its test functions are bounded measurable
real functions. The initial distribution is separate from this property.

The multi-step conditional law is expressed using powers of the same transition kernel.
The property descends to a smaller filtration to which the process is still adapted;
it makes no assertion about enlarging the filtration. On a countable state space the
one-step property for the history filtration is equivalent to finite-prefix recursion.
Together with an initial law, it characterizes the Markov-chain path law for Mathlib's
natural filtration. The coordinate process supplies a canonical realization.

The general history-filtration characterization needs no topology. For the natural-filtration
corollary, a countable state space with measurable singletons can carry the discrete topology:
Mathlib supplies its Borel compatibility and turns measurable coordinates into strongly
measurable ones.

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
  -- Conditioning the constant function `1` is only consistent with its integral against a Markov
  -- kernel when `μ` is finite (or zero).
  by_contra hμ
  have hint : ¬ Integrable (fun _ : Ω => (1 : ℝ)) μ := fun hi =>
    hμ ((integrable_const_iff.1 hi).resolve_left one_ne_zero)
  have hc := h.condExp_eq 0 (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  rw [condExp_of_not_integrable hint] at hc
  have hzero : μ = 0 := by
    have : ∀ᵐ _ ∂μ, False := by
      filter_upwards [hc] with ω hω
      simp at hω
    simpa using this
  exact hμ (hzero ▸ inferInstance)

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

variable [Countable S] [Nonempty S] [MeasurableSingletonClass S]
  {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}
  [IsFiniteMeasure μ] [IsMarkovKernel κ]

/-- The Markov property for the history filtration gives the finite-prefix recursion. -/
private theorem prefix_recursion_of_isMarkovChain (h : IsMarkovChain ℱ X κ μ)
    (hℱ : ∀ n, ℱ n = MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance)
    (n : ℕ) :
    μ.map (fun ω => ((fun i : Fin (n + 1) => X i ω), X (n + 1) ω)) =
        prefixLaw μ X (n + 1) ⊗ₘ κ.comap
          (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _) := by
  have hadapt := Filtration.adapted_of_eq_comap_prefix hℱ
  have hX : ∀ n, Measurable (X n) := fun _ => hadapt.measurable
  have hpre (n : ℕ) : Measurable (fun ω (i : Fin (n + 1)) => X i ω) :=
    Measurable.of_eval fun i => hX i
  -- Singleton indicators identify the conditional transition measure on the countable space.
  let Y : Ω → (Fin (n + 1) → S) := fun ω i => X i ω
  let K := κ.comap (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _)
  have heq : condDistrib (X (n + 1)) Y μ =ᵐ[μ.map Y] K := by
    have heach (y : S) :
        (fun w => (condDistrib (X (n + 1)) Y μ w).real {y}) =ᵐ[μ.map Y]
          fun w => (K w).real {y} := by
      have hb : ∃ C : ℝ, ∀ z : S, ‖({y} : Set S).indicator (fun _ => (1 : ℝ)) z‖ ≤ C :=
        ⟨1, fun z => by by_cases hz : z ∈ ({y} : Set S) <;> simp [hz]⟩
      have hc := h.condExp_eq n _ (measurable_const.indicator (measurableSet_singleton y)) hb
      simp only [hℱ n, integral_indicator_const (1 : ℝ) (measurableSet_singleton y),
        smul_eq_mul, mul_one] at hc
      have hd := condExp_ae_eq_integral_condDistrib (hpre n) (hX (n + 1)).aemeasurable
        (measurable_const.indicator (measurableSet_singleton y)).stronglyMeasurable
        ((integrable_const (μ := μ) (1 : ℝ)).indicator ((hX (n + 1)) (measurableSet_singleton y)))
      simp only [integral_indicator_const (1 : ℝ) (measurableSet_singleton y),
        smul_eq_mul, mul_one] at hd
      have hm : MeasurableSet {w | (condDistrib (X (n + 1)) Y μ w).real {y} =
          (K w).real {y}} :=
        measurableSet_eq_fun
          ((Kernel.measurable_coe _ (measurableSet_singleton y)).ennreal_toReal)
          ((Kernel.measurable_coe _ (measurableSet_singleton y)).ennreal_toReal)
      apply (ae_map_iff (hpre n).aemeasurable hm).2
      filter_upwards [hd, hc] with ω hdω hcω
      simpa only [Y, K, Kernel.comap_apply, Fin.val_last] using hdω.symm.trans hcω
    filter_upwards [ae_all_iff.2 heach] with w hw
    apply Measure.ext_of_singleton
    intro y
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (hw y)
  simpa only [prefixLaw_def, blockLaw_def] using
    (condDistrib_ae_eq_iff_measure_eq_compProd (hpre n).aemeasurable
      (hX (n + 1)).aemeasurable K).1 heq

/-- The finite-prefix recursion gives the Markov property for the history filtration. -/
private theorem isMarkovChain_of_prefix_recursion
    (hℱ : ∀ n, ℱ n = MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance)
    (h : ∀ n, μ.map (fun ω => ((fun i : Fin (n + 1) => X i ω), X (n + 1) ω)) =
        prefixLaw μ X (n + 1) ⊗ₘ κ.comap
          (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _)) :
    IsMarkovChain ℱ X κ μ := by
  have hadapt := Filtration.adapted_of_eq_comap_prefix hℱ
  have hX : ∀ n, Measurable (X n) := fun _ => hadapt.measurable
  have hpre (n : ℕ) : Measurable (fun ω (i : Fin (n + 1)) => X i ω) :=
    Measurable.of_eval fun i => hX i
  -- Prefix recursion identifies the conditional distribution, which integrates every test.
  refine ⟨hadapt, fun n f hf hb => ?_⟩
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable (fun ω => f (X (n + 1) ω)) μ :=
    ⟨(hf.comp (hX (n + 1))).aestronglyMeasurable,
      .of_bounded (Eventually.of_forall fun ω => hC (X (n + 1) ω))⟩
  rw [hℱ n]
  have hd := condExp_ae_eq_integral_condDistrib (hpre n) (hX (n + 1)).aemeasurable
    hf.stronglyMeasurable hi
  have heq := condDistrib_ae_eq_of_measure_eq_compProd (hpre n).aemeasurable
    (hX (n + 1)).aemeasurable
    (by simpa only [prefixLaw_def, blockLaw_def] using h n)
  filter_upwards [hd, ae_of_ae_map (hpre n).aemeasurable heq] with ω hω hκ
  simpa only [hκ, Kernel.comap_apply, Fin.val_last] using hω

omit [Nonempty S] in
/-- On a countable state space, the filtration-relative test-function property for the
history filtration is equivalent to the finite-prefix recursion. The hypothesis `hℱ`
identifies the information through time `n` with that generated by `X 0, …, X n`. -/
theorem isMarkovChain_iff_prefix_recursion
    (hℱ : ∀ n, ℱ n = MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance) :
    IsMarkovChain ℱ X κ μ ↔
      ∀ n, μ.map (fun ω => ((fun i : Fin (n + 1) => X i ω), X (n + 1) ω)) =
        prefixLaw μ X (n + 1) ⊗ₘ κ.comap
          (fun w : Fin (n + 1) → S => w (Fin.last n)) (measurable_pi_apply _) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · -- The sample space is empty, so both sides hold trivially.
    have : IsEmpty Ω := ⟨fun ω => hS.false (X 0 ω)⟩
    exact ⟨fun _ n => Measure.ext fun s _ => by simp [Set.eq_empty_of_isEmpty s],
      fun _ => ⟨fun n s _ => by
        rw [Set.eq_empty_of_isEmpty (X n ⁻¹' s)]
        exact @MeasurableSet.empty _ (ℱ n), fun n f _ _ => by
        rw [Subsingleton.elim μ 0, ae_zero]
        exact Filter.eventually_bot⟩⟩
  · exact ⟨fun h n => prefix_recursion_of_isMarkovChain h hℱ n,
      isMarkovChain_of_prefix_recursion hℱ⟩

omit [Nonempty S] [IsFiniteMeasure μ] in
/-- A process has the Markov-chain path law exactly when it has the specified initial law
and is a Markov chain relative to Mathlib's natural filtration. The state-space topology
is used only to form that filtration; no topology on the sample space is required. -/
theorem hasLaw_markovChainLaw_iff_isMarkovChain_natural
    [TopologicalSpace S] [TopologicalSpace.MetrizableSpace S] [BorelSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] (hX : ∀ n, StronglyMeasurable (X n)) :
    HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ ↔
      μ.map (X 0) = ν ∧ IsMarkovChain (Filtration.natural X hX) X κ μ := by
  have key : IsFiniteMeasure μ → (HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ ↔
      μ.map (X 0) = ν ∧ IsMarkovChain (Filtration.natural X hX) X κ μ) := fun _ => by
    rw [hasLaw_markovChainLaw_iff ν κ (fun n => (hX n).measurable.aemeasurable),
      isMarkovChain_iff_prefix_recursion
        (Filtration.natural_eq_comap_prefix X hX)]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hfin : IsFiniteMeasure μ := h.isFiniteMeasure
    exact (key hfin).1 h
  · exact (key h.2.isFiniteMeasure).2 h

end History

end TauCeti.Probability
