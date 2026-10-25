/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.TransitionCount
public import TauCeti.Probability.ConditionalProbability
public import TauCeti.Probability.Process.MarkovChain
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
-- Non-public: null-measurability of a prefix event is used only inside a proof.
import TauCeti.Probability.Process.Cylinder

/-!
# Mixtures of Markov chains

A process `X : ℕ → Ω → α` on a countable state space is a **mixture of Markov chains** when its
finite-path `μ`-masses are integrals of Markov-chain path masses against `μ`: there is a measurable
initial-law witness `ν : Ω → ProbabilityMeasure α` and a measurable transition-matrix witness
`κ : Ω → α → ProbabilityMeasure α` with

```text
prefixLaw μ X (n + 1) {w} = ∫⁻ ω, ν ω {w 0} * ∏ i, κ ω (w i.castSucc) {w i.succ} ∂μ
```

for every finite path `w`. `MixedMarkovChainWith μ X ν κ` names the pair of witnesses, and
`MixedMarkovChain μ X` is the existential wrapper.

⚠ This is a property of the **unconditional** finite path laws only. It says nothing about the
joint law of `(ν, κ, X)`, so it is not a conditional-independence statement, and the witnesses are
not asserted to be unique. The conditional strengthening — conditionally on `(ν, κ)` the process is
a Markov chain with that initial law and that transition matrix — is deliberately not what is
defined here.

Since a Markov-chain path mass is an initial weight times a product of transition weights, the
initial state together with the transition counts of a path is sufficient for its `μ`-mass
(`MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral_prod_pow`); this is the mechanism behind
the Markov exchangeability of such mixtures, developed in
`TauCeti.Probability.Exchangeability.MixedMarkovChain` together with the Diaconis–Freedman
representation theorem whose conclusion this class is.

The class is closed under **gluing along a countable partition**
(`mixedMarkovChainWith_of_forall_cond`): if the process is a mixture of Markov chains under each
conditional measure `μ[|f ⁻¹' {b}]` on a fibre of positive mass of a random variable `f` with
countably many values, then it is one under `μ`, with the witnesses on the fibre of `ω` read off at
`ω`. This follows from the law of total probability over the fibres
(`ProbabilityTheory.sum_meas_smul_cond_fiber_of_countable`), since a fibre of mass zero contributes
nothing to the finite path masses. The case `f = X 0` passes from representations of a process
started at each fixed state to one with a random initial state.

## Main definitions

* `TauCeti.Probability.MixedMarkovChainWith`: the mixture identity with named witnesses.
* `TauCeti.Probability.MixedMarkovChain`: its existential wrapper.

## Main results

* `TauCeti.Probability.MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral_prod_pow`: the
  initial state and transition counts of a path are sufficient for its `μ`-mass.
* `TauCeti.Probability.mixedMarkovChainWith_const_of_prefixLaw_singleton_eq`: a single Markov chain
  is the degenerate mixture.
* `TauCeti.Probability.markovChainLaw_mixedMarkovChainWith`: the homogeneous Markov chain of an
  initial law and a transition kernel is the degenerate mixture with those constant witnesses.
  This makes the class non-vacuous at an arbitrary transition kernel, rather than only at the
  hypothesis that some product form of the finite path laws holds.
* `TauCeti.Probability.mixedMarkovChainWith_of_forall_cond` and
  `TauCeti.Probability.mixedMarkovChain_of_forall_cond`: a process that is a mixture of Markov
  chains conditionally on each positive-mass value of a countably-valued random variable is a
  mixture of Markov chains.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **A mixture of Markov chains** with specified mixing witnesses `ν` and `κ`: the `μ`-mass of a
finite path is the integral against `μ` of its Markov-chain path mass built from `ν ω` and `κ ω`.
The countability and measurable-singleton conjuncts restrict this singleton-mass formulation to
discrete state spaces, matching `MarkovExchangeable`, where it is non-vacuous and determines the
finite path laws. Bundled alongside, as in `MarkovExchangeable`, are the regularity conjuncts the
mixture identity is stated against: the process is coordinatewise a.e. measurable, and both
witnesses are measurable (`ν`, and each row `ω ↦ κ ω a`). -/
def MixedMarkovChainWith (μ : Measure Ω) (X : ℕ → Ω → α)
    (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α) : Prop :=
  Countable α ∧ MeasurableSingletonClass α ∧ (∀ i, AEMeasurable (X i) μ) ∧
    Measurable ν ∧ (∀ a, Measurable fun ω => κ ω a) ∧
      ∀ (n : ℕ) (w : Fin (n + 1) → α),
        prefixLaw μ X (n + 1) {w} =
          ∫⁻ ω, (ν ω : Measure α) {w 0} *
            ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ

/-- Constructor from discrete-state instances, coordinatewise a.e. measurability, measurability of
the two witnesses, and the mixture identity for finite paths. -/
theorem MixedMarkovChainWith.intro [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    {κ : Ω → α → ProbabilityMeasure α}
    (hX : ∀ i, AEMeasurable (X i) μ) (hν : Measurable ν) (hκ : ∀ a, Measurable fun ω => κ ω a)
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → α),
      prefixLaw μ X (n + 1) {w} =
        ∫⁻ ω, (ν ω : Measure α) {w 0} *
          ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ) :
    MixedMarkovChainWith μ X ν κ :=
  ⟨inferInstance, inferInstance, hX, hν, hκ, h⟩

/-- The state space of a mixture of Markov chains is countable. -/
theorem MixedMarkovChainWith.countable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : Countable α :=
  h.1

/-- Singletons in the state space of a mixture of Markov chains are measurable. -/
theorem MixedMarkovChainWith.measurableSingletonClass {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : MeasurableSingletonClass α :=
  h.2.1

/-- Every coordinate of a mixture of Markov chains is a.e. measurable. -/
theorem MixedMarkovChainWith.aemeasurable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) (i : ℕ) : AEMeasurable (X i) μ :=
  h.2.2.1 i

/-- The initial-law witness of a mixture of Markov chains is measurable. -/
@[grind →]
theorem MixedMarkovChainWith.measurable_initialLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : Measurable ν :=
  h.2.2.2.1

/-- Each row of the transition-matrix witness of a mixture of Markov chains is measurable. -/
theorem MixedMarkovChainWith.measurable_transitionMatrix {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) (a : α) : Measurable fun ω => κ ω a :=
  h.2.2.2.2.1 a

/-- The defining mixture identity: the `μ`-mass of a finite path is the integral of its
Markov-chain path masses against `μ`. -/
@[grind =>]
theorem MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) (n : ℕ) (w : Fin (n + 1) → α) :
    prefixLaw μ X (n + 1) {w} =
      ∫⁻ ω, (ν ω : Measure α) {w 0} *
        ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ :=
  h.2.2.2.2.2 n w

/-- Simp normal form for `MixedMarkovChainWith`. -/
@[simp]
theorem mixedMarkovChainWith_iff [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    {κ : Ω → α → ProbabilityMeasure α} :
    MixedMarkovChainWith μ X ν κ ↔
      (∀ i, AEMeasurable (X i) μ) ∧ Measurable ν ∧ (∀ a, Measurable fun ω => κ ω a) ∧
        ∀ (n : ℕ) (w : Fin (n + 1) → α),
          prefixLaw μ X (n + 1) {w} =
            ∫⁻ ω, (ν ω : Measure α) {w 0} *
              ∏ i : Fin n, (κ ω (w i.castSucc) : Measure α) {w i.succ} ∂μ :=
  ⟨fun h => ⟨h.aemeasurable, h.measurable_initialLaw, h.measurable_transitionMatrix,
      h.prefixLaw_singleton_eq_lintegral⟩,
    fun h => MixedMarkovChainWith.intro h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-- **A mixture of Markov chains**: existence of initial-law and transition-matrix witnesses
representing the finite path laws by integration against `μ`. -/
def MixedMarkovChain (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
    MixedMarkovChainWith μ X ν κ

/-- Constructor from a named pair of witnesses. -/
theorem MixedMarkovChain.of_witnesses {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : MixedMarkovChain μ X :=
  ⟨ν, κ, h⟩

/-- A mixture of Markov chains has initial-law and transition-matrix witnesses. -/
theorem MixedMarkovChain.exists_witnesses {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) :
    ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
      MixedMarkovChainWith μ X ν κ :=
  h

/-- Simp normal form for the existential wrapper `MixedMarkovChain`. -/
@[simp]
theorem mixedMarkovChain_iff {μ : Measure Ω} {X : ℕ → Ω → α} :
    MixedMarkovChain μ X ↔
      ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
        MixedMarkovChainWith μ X ν κ :=
  Iff.rfl

/-- The state space of a mixture of Markov chains is countable. -/
theorem MixedMarkovChain.countable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) : Countable α := by
  obtain ⟨_, _, h⟩ := h
  exact h.countable

/-- Singletons in the state space of a mixture of Markov chains are measurable. -/
theorem MixedMarkovChain.measurableSingletonClass {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) : MeasurableSingletonClass α := by
  obtain ⟨_, _, h⟩ := h
  exact h.measurableSingletonClass

/-- Every coordinate of a mixture of Markov chains is a.e. measurable. -/
theorem MixedMarkovChain.aemeasurable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) (i : ℕ) : AEMeasurable (X i) μ := by
  obtain ⟨_, _, h⟩ := h
  exact h.aemeasurable i

/-- **The initial state together with the transition counts of a path is sufficient for its
`μ`-mass.** Rewriting the mixture identity through `TauCeti.prod_transitionCount` replaces the
transition-product factor by a product of powers indexed by the transition counts; the index set
`S` only has to contain the letters of the path. -/
theorem MixedMarkovChainWith.prefixLaw_singleton_eq_lintegral_prod_pow {μ : Measure Ω}
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) {n : ℕ} (w : Fin (n + 1) → α) {S : Finset α}
    (hS : ∀ i, w i ∈ S) :
    prefixLaw μ X (n + 1) {w} =
      ∫⁻ ω, (ν ω : Measure α) {w 0} *
        ∏ ab ∈ S ×ˢ S, (κ ω ab.1 : Measure α) {ab.2} ^ transitionCount w ab.1 ab.2 ∂μ := by
  rw [h.prefixLaw_singleton_eq_lintegral n w]
  refine lintegral_congr fun ω => ?_
  rw [prod_transitionCount w (fun i : Fin n => ⟨hS i.castSucc, hS i.succ⟩)
    fun a b => (κ ω a : Measure α) {b}]

/-- **A Markov chain is the degenerate mixture of Markov chains.** The hypothesis is the defining
product form of the finite-dimensional laws of a Markov chain with initial law `p₀` and transition
matrix `p`; the mixing witnesses are constant. -/
theorem mixedMarkovChainWith_const_of_prefixLaw_singleton_eq
    [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (p₀ : ProbabilityMeasure α) (p : α → ProbabilityMeasure α)
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → α),
      prefixLaw μ X (n + 1) {w} =
        (p₀ : Measure α) {w 0} * ∏ i : Fin n, (p (w i.castSucc) : Measure α) {w i.succ}) :
    MixedMarkovChainWith μ X (fun _ => p₀) fun _ => p :=
  MixedMarkovChainWith.intro hX measurable_const (fun _ => measurable_const) fun n w => by
    rw [h n w, lintegral_const, measure_univ, mul_one]

section MarkovChain

open ProbabilityTheory

variable (ν : Measure α) [IsProbabilityMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ]

/-- **A homogeneous Markov chain is the degenerate mixture of Markov chains** at its own initial
law and transition kernel: the two witnesses are the constant ones. This is the source of genuine
`MixedMarkovChain` processes at an arbitrary transition kernel. -/
theorem markovChainLaw_mixedMarkovChainWith [Countable α] [MeasurableSingletonClass α] :
    MixedMarkovChainWith (markovChainLaw ν κ) (fun i x => x i)
      (fun _ => (⟨ν, inferInstance⟩ : ProbabilityMeasure α))
      fun _ a => (⟨κ a, inferInstance⟩ : ProbabilityMeasure α) :=
  mixedMarkovChainWith_const_of_prefixLaw_singleton_eq
    (fun i => (measurable_pi_apply i).aemeasurable) ⟨ν, inferInstance⟩
    (fun a => ⟨κ a, inferInstance⟩) (MeasureTheory.Measure.markovChainLaw_prefixLaw_singleton ν κ)

/-- **A homogeneous Markov chain is a mixture of Markov chains**, existential form. -/
theorem markovChainLaw_mixedMarkovChain [Countable α] [MeasurableSingletonClass α] :
    MixedMarkovChain (markovChainLaw ν κ) fun i x => x i :=
  MixedMarkovChain.of_witnesses (markovChainLaw_mixedMarkovChainWith ν κ)

end MarkovChain

section Cond

open ProbabilityTheory

variable {β : Type*} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
  {μ : Measure Ω} {X : ℕ → Ω → α} {f : Ω → β}

/-- **Gluing mixtures of Markov chains along a countable partition**, witness form. If, on every
fibre `f ⁻¹' {b}` of positive mass of a random variable `f` with countably many values, the process
is a mixture of Markov chains under the conditional measure with witnesses `ν b` and `κ b`, then it
is a mixture of Markov chains under `μ` itself, with the witnesses read off on the fibre of `ω`. The
witnesses on the null fibres are only required to be measurable. -/
theorem mixedMarkovChainWith_of_forall_cond [Countable α] [MeasurableSingletonClass α]
    [IsFiniteMeasure μ] (hf : Measurable f)
    {ν : β → Ω → ProbabilityMeasure α} {κ : β → Ω → α → ProbabilityMeasure α}
    (hν : ∀ b, Measurable (ν b)) (hκ : ∀ b a, Measurable fun ω => κ b ω a)
    (h : ∀ b, μ (f ⁻¹' {b}) ≠ 0 → MixedMarkovChainWith (μ[|f ⁻¹' {b}]) X (ν b) (κ b)) :
    MixedMarkovChainWith μ X (fun ω => ν (f ω) ω) fun ω => κ (f ω) ω := by
  have hfib : ∀ b, MeasurableSet (f ⁻¹' {b}) := fun b => hf (measurableSet_singleton b)
  -- the law of total probability over the fibres of `f`
  have hμ := sum_meas_smul_cond_fiber_of_countable hf μ
  -- coordinatewise a.e. measurability under `μ` is inherited from the positive-mass fibres
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => by
    rw [← hμ, aemeasurable_sum_measure_iff]
    intro b
    by_cases hb : μ (f ⁻¹' {b}) = 0
    · simp [hb]
    · exact (aemeasurable_smul_measure_iff hb).2 ((h b hb).aemeasurable i)
  have hpair : Measurable fun ω => (f ω, ω) := hf.prodMk measurable_id
  refine MixedMarkovChainWith.intro hX ?_ ?_ fun n w => ?_
  · exact (measurable_from_prod_countable_right (f := fun p : β × Ω => ν p.1 p.2) hν).comp hpair
  · exact fun a => (measurable_from_prod_countable_right (f := fun p : β × Ω => κ p.1 p.2 a)
      fun b => hκ b a).comp hpair
  -- the Markov-chain path mass built from the glued witnesses
  set G : Ω → ℝ≥0∞ := fun ω => (ν (f ω) ω : Measure α) {w 0} *
    ∏ i : Fin n, (κ (f ω) ω (w i.castSucc) : Measure α) {w i.succ} with hG
  -- on the fibre over `b`, the glued witnesses are the witnesses of that fibre
  have hG_ae : ∀ b, G =ᵐ[μ[|f ⁻¹' {b}]] fun ω => (ν b ω : Measure α) {w 0} *
      ∏ i : Fin n, (κ b ω (w i.castSucc) : Measure α) {w i.succ} := fun b => by
    filter_upwards [ae_cond_mem (hfib b)] with ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp only [hG, hω]
  -- the prefix event is the block cylinder of the singletons `{w i}`
  have hA : NullMeasurableSet {ω | ∀ i : Fin (n + 1), X i.val ω = w i} μ := by
    have hcyl : {ω | ∀ i : Fin (n + 1), X i.val ω = w i} =
        blockCylinder X (fun i : Fin (n + 1) => i.val) fun i => {w i} :=
      Set.ext fun ω => by simp
    rw [hcyl]
    exact nullMeasurableSet_blockCylinder (fun i => hX i.val) fun i => measurableSet_singleton (w i)
  calc prefixLaw μ X (n + 1) {w}
      = μ {ω | ∀ i : Fin (n + 1), X i.val ω = w i} := prefixLaw_singleton_eq_measure hX w
    _ = (Measure.sum fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}])
        {ω | ∀ i : Fin (n + 1), X i.val ω = w i} := by rw [hμ]
    _ = ∑' b, μ (f ⁻¹' {b}) * μ[|f ⁻¹' {b}] {ω | ∀ i : Fin (n + 1), X i.val ω = w i} := by
        rw [Measure.sum_apply₀ _ (hμ.symm ▸ hA)]
        simp only [Measure.smul_apply, smul_eq_mul]
    _ = ∑' b, μ (f ⁻¹' {b}) * ∫⁻ ω, G ω ∂μ[|f ⁻¹' {b}] := by
        refine tsum_congr fun b => ?_
        by_cases hb : μ (f ⁻¹' {b}) = 0
        · simp [hb]
        · rw [lintegral_congr_ae (hG_ae b), ← (h b hb).prefixLaw_singleton_eq_lintegral,
            prefixLaw_singleton_eq_measure fun i => (hX i).mono_ac cond_absolutelyContinuous]
    _ = ∫⁻ ω, G ω ∂μ := by
        conv_rhs => rw [← hμ]
        rw [lintegral_sum_measure]
        exact tsum_congr fun b => by rw [lintegral_smul_measure, smul_eq_mul]

/-- **Gluing mixtures of Markov chains along a countable partition**, existential form. A process
that is a mixture of Markov chains conditionally on each positive-mass value of a random variable
with countably many values is a mixture of Markov chains. The measure is assumed nonzero, so that
at least one fibre carries positive mass. -/
theorem mixedMarkovChain_of_forall_cond [IsFiniteMeasure μ] [NeZero μ] (hf : Measurable f)
    (h : ∀ b, μ (f ⁻¹' {b}) ≠ 0 → MixedMarkovChain (μ[|f ⁻¹' {b}]) X) :
    MixedMarkovChain μ X := by
  -- some fibre has positive mass
  obtain ⟨b₀, hb₀⟩ : ∃ b, μ (f ⁻¹' {b}) ≠ 0 := by
    by_contra hcon
    refine (NeZero.ne μ) (Measure.measure_univ_eq_zero.1 ?_)
    rw [← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton β, Set.preimage_iUnion]
    exact measure_iUnion_null fun b => of_not_not fun hb => hcon ⟨b, hb⟩
  obtain ⟨ν₀, κ₀, h₀⟩ := h b₀ hb₀
  have := h₀.countable
  have := h₀.measurableSingletonClass
  -- its witnesses serve on the null fibres, where the mixture identity is not needed
  have key : ∀ b, ∃ (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α),
      Measurable ν ∧ (∀ a, Measurable fun ω => κ ω a) ∧
        (μ (f ⁻¹' {b}) ≠ 0 → MixedMarkovChainWith (μ[|f ⁻¹' {b}]) X ν κ) := fun b => by
    by_cases hb : μ (f ⁻¹' {b}) = 0
    · exact ⟨ν₀, κ₀, h₀.measurable_initialLaw, h₀.measurable_transitionMatrix,
        fun hb' => (hb' hb).elim⟩
    · obtain ⟨ν, κ, hνκ⟩ := h b hb
      exact ⟨ν, κ, hνκ.measurable_initialLaw, hνκ.measurable_transitionMatrix, fun _ => hνκ⟩
  choose ν κ hν hκ hνκ using key
  exact ⟨_, _, mixedMarkovChainWith_of_forall_cond hf hν hκ hνκ⟩

end Cond

end Probability

end TauCeti

end

end
