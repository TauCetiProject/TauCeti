/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Process.StoppedValue

/-!
# Strong Markov laws for arbitrary realizations

A measurable process with path law `markovChainLaw ν κ` satisfies the strong Markov law at
stopping times of its own history filtration. On a stopped-history event `A`, restricted to
finite stopping times, the shifted process has the chain law started from the distribution
of the stopped state on that same event. The almost surely finite version drops the restriction.

The main theorem allows any filtration contained in the coordinate history. This containment
is essential: equality of path laws alone does not give the Markov property for an arbitrary
enlargement of the history. The natural-filtration specialization uses Mathlib's
`Filtration.natural`; only that specialization needs a topology on the state space, and no
topology on the sample space is used. The main theorem works on arbitrary measurable spaces.

These results transfer the canonical fixed-time law by decomposing a stopping time into its
time slices. They use the same first-state convention for the shifted path: its coordinate zero
is the state at the stopping time, not the next state. No value chosen at an infinite stopping
time affects the restricted assertion.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Theorem 1.4.2.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer, 2002,
  Proposition 8.9.
-/

public section

open MeasureTheory TauCeti.Probability TopologicalSpace

namespace ProbabilityTheory.HasLaw

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {P : Measure Ω} {ν : Measure α} [IsFiniteMeasure ν]
  {κ : Kernel α α} [IsMarkovKernel κ] {X : ℕ → Ω → α}

/-- **Strong Markov law on an arbitrary sample space.** If the filtration is contained in the
coordinate history, the future on `A ∩ {τ < ∞}` has the chain law started from the stopped-state
law on that event. No adaptation, topology or countability assumption on the state space is
needed for this law identity. It does not assert the property for enlarged filtrations. -/
theorem markovChainLaw_restrict_map_stoppedValue_processShift
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hXm : ∀ n, Measurable (X n)) {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    (hℱ : ∀ n, ℱ n ≤ MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue (processShift X) τ) =
      markovChainLaw ((P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue X τ)) κ := by
  have hθ : Measurable (stoppedValue (processShift X) τ) :=
    measurable_stoppedValue_of_countable (fun n => by fun_prop) hτ.measurable'
  have hY : Measurable (stoppedValue X τ) :=
    measurable_stoppedValue_of_countable hXm hτ.measurable'
  let E : ℕ → Set Ω := fun n => A ∩ {ω | τ ω = WithTop.some n}
  have hEn : ∀ n, MeasurableSet[ℱ n] (E n) := fun n =>
    (hτ.measurableSet_inter_eq_iff A n).1 (hA.inter (hτ.measurableSet_eq_of_countable' n))
  have hE : ∀ n, MeasurableSet (E n) := fun n => ℱ.le n _ (hEn n)
  have hU : A ∩ {ω | τ ω ≠ ⊤} = ⋃ n, E n := by
    ext ω
    cases h : τ ω <;> simp [E, h]
  have hd : Pairwise (Function.onFun Disjoint E) := fun m n hmn =>
    Set.disjoint_left.2 fun ω hm hn => hmn (WithTop.coe_injective (hm.2.symm.trans hn.2))
  -- Split both the future law and its initial measure over the disjoint time slices.
  rw [hU, Measure.restrict_iUnion hd hE, Measure.map_sum hθ.aemeasurable,
    Measure.map_sum hY.aemeasurable, Measure.markovChainLaw_eq_comp,
    Measure.bind_sum _ _ κ.markovChainKernel.measurable.aemeasurable]
  congr 1
  funext n
  have hτn : ∀ᵐ ω ∂P.restrict (E n), τ ω = WithTop.some n :=
    ae_restrict_of_forall_mem (hE n) fun ω hω => hω.2
  have hθn : (P.restrict (E n)).map (stoppedValue (processShift X) τ) =
      (P.restrict (E n)).map (processShift X n) :=
    Measure.map_congr (hτn.mono fun ω hω => by
      simp only [stoppedValue, hω, WithTop.untopD_coe])
  have hYn : (P.restrict (E n)).map (stoppedValue X τ) = (P.restrict (E n)).map (X n) :=
    Measure.map_congr (hτn.mono fun ω hω => by
      simp only [stoppedValue, hω, WithTop.untopD_coe])
  -- On the slice `τ = n`, its stopped-history event belongs to the time-`n` history.
  rw [hθn, hYn, ← Measure.markovChainLaw_eq_comp]
  exact hX.markovChainLaw_restrict_map_processShift hXm n (hℱ n _ (hEn n))

/-- **Strong Markov event identity on an arbitrary sample space.** Conditional on a
stopped-history event and a finite stopping time, future events are evaluated by the chain law
started at the stopped state. -/
theorem markovChainLaw_inter_preimage_stoppedValue_processShift
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hXm : ∀ n, Measurable (X n)) {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    (hℱ : ∀ n, ℱ n ≤ MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) {B : Set (ℕ → α)}
    (hB : MeasurableSet B) :
    P (A ∩ {ω | τ ω ≠ ⊤} ∩ stoppedValue (processShift X) τ ⁻¹' B) =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤},
        markovChainLaw (Measure.dirac (stoppedValue X τ ω)) κ B ∂P := by
  have hθ : Measurable (stoppedValue (processShift X) τ) :=
    measurable_stoppedValue_of_countable (fun n => by fun_prop) hτ.measurable'
  have hY : Measurable (stoppedValue X τ) :=
    measurable_stoppedValue_of_countable hXm hτ.measurable'
  rw [Set.inter_comm, ← Measure.restrict_apply (hB.preimage hθ),
    ← Measure.map_apply hθ hB,
    hX.markovChainLaw_restrict_map_stoppedValue_processShift hXm hℱ hτ hA,
    Measure.markovChainLaw_eq_comp, Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hB) hY]
  simp

/-- **Strong Markov law at an almost surely finite stopping time.** On a stopped-history event,
the shifted process is a chain started from the law of its stopped state on that event. -/
theorem markovChainLaw_restrict_map_stoppedValue_processShift_of_ae_ne_top
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hXm : ∀ n, Measurable (X n)) {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    (hℱ : ∀ n, ℱ n ≤ MeasurableSpace.comap
      (fun ω (i : Fin (n + 1)) => X i ω) inferInstance)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (stoppedValue (processShift X) τ) =
      markovChainLaw ((P.restrict A).map (stoppedValue X τ)) κ := by
  have heq : P.restrict (A ∩ {ω | τ ω ≠ ⊤}) = P.restrict A :=
    Measure.restrict_congr_set (inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.2 hfin))
  simpa only [heq] using
    hX.markovChainLaw_restrict_map_stoppedValue_processShift hXm hℱ hτ hA

/-- A process with a Markov-chain path law satisfies the strong Markov law at stopping times
of Mathlib's natural filtration. The topology here is used only to form that filtration. -/
theorem markovChainLaw_restrict_map_stoppedValue_processShift_natural
    [TopologicalSpace α] [MetrizableSpace α] [BorelSpace α]
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hXm : ∀ n, StronglyMeasurable (X n)) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.natural X hXm) τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue (processShift X) τ) =
      markovChainLaw ((P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue X τ)) κ := by
  refine hX.markovChainLaw_restrict_map_stoppedValue_processShift
    (fun n => (hXm n).measurable) (fun n => ?_) hτ hA
  rw [Filtration.natural_eq_comap]
  -- The history indexed by `Iic n` is a measurable reindexing of the finite prefix.
  rintro s ⟨B, hB, rfl⟩
  let r : (Fin (n + 1) → α) → (Set.Iic n → α) :=
    fun v j => v ⟨j.1, Nat.lt_succ_of_le j.2⟩
  exact ⟨r ⁻¹' B, hB.preimage (by fun_prop), rfl⟩

end ProbabilityTheory.HasLaw
