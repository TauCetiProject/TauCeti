/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass.Invariance
public import TauCeti.Probability.MarkovChain.ClosedClass
public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.Occupation
import TauCeti.MeasureTheory.Integral.Lebesgue.Dirac
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Null recurrence, recurrence trichotomy, and finite closed communicating classes

A state `x` of a Markov kernel `κ` is **null recurrent**
(`ProbabilityTheory.Kernel.IsNullRecurrent`) when it is recurrent (`κ.IsRecurrent x`) and has
infinite extended mean positive return time (`κ.meanReturnTime x = ∞`). Because transient states
already have `κ.meanReturnTime x = ∞` (`IsTransient.meanReturnTime_eq_top`), positive recurrence
needs only `κ.meanReturnTime x < ∞`, whereas null recurrence splits off the infinite-mean half of
recurrence. Every state of any Markov kernel therefore satisfies the mutually exclusive trichotomy
`κ.IsTransient x ∨ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x`, with neither countability nor
measurable singletons required on the state space.

Restricting a Markov kernel to a measurable closed set preserves positive recurrence and null
recurrence of every state in the set, again without measurable singletons, and deterministic and
constant-Dirac kernels have no null recurrent states on any measurable space. When singletons are
measurable, null recurrence is inherited along reachability and is constant on communicating
classes, giving the global trichotomy of counting-measure-irreducible chains: either all states are
transient, all states are positive recurrent, or all states are null recurrent.

At a null recurrent state `x`, the cycle occupation measure `κ.cycleOccupation x` has infinite total
mass (`Kernel.cycleOccupation_univ_eq_top_of_not_isPositiveRecurrent`) and fails to be finite
(`Kernel.not_isFiniteMeasure_cycleOccupation_of_not_isPositiveRecurrent`), and the invariant-measure
vanishing theorems for non-positive-recurrent states in `TauCeti.Probability.MarkovChain.Invariant`
apply via `IsNullRecurrent.not_isPositiveRecurrent`.

On countable state spaces with measurable singletons, the occupation strong law in
`TauCeti.Probability.MarkovChain.Occupation` characterizes positive recurrence and yields
vanishing long-run visit fractions at non-positive-recurrent states; combining this with
recurrence characterizes null recurrence via vanishing expected (or almost-sure) limiting visit
fraction starting from the state.

Finally, restricting to a finite closed communicating class transfers finite irreducible positive
recurrence to arbitrary ambient state spaces with measurable singletons: every state in a finite
closed communicating class is positive recurrent, and `κ` admits a unique invariant probability
measure concentrated on that class. On a countable state space every recurrent state with a finite
communicating class is positive recurrent and every null recurrent state has an infinite
communicating class; on a finite state space recurrence and positive recurrence coincide
unconditionally, no state is null recurrent, and almost every trajectory eventually enters and
remains in the closed communicating class of a positive recurrent state.

## Main definitions and statements

* `ProbabilityTheory.Kernel.IsNullRecurrent`: `κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞`.
* `ProbabilityTheory.Kernel.isTransient_or_isPositiveRecurrent_or_isNullRecurrent`: state-level
  recurrence trichotomy.
* `ProbabilityTheory.Kernel.isPositiveRecurrent_subtype_iff` and
  `ProbabilityTheory.Kernel.isNullRecurrent_subtype_iff`: invariance under restriction to a closed
  measurable set.
* `ProbabilityTheory.Kernel.not_isNullRecurrent_deterministic` and
  `ProbabilityTheory.Kernel.not_isNullRecurrent_const_dirac`: non-null-recurrence of deterministic
  and constant-Dirac kernels on any measurable space.
* `ProbabilityTheory.Kernel.IsNullRecurrent.of_reaches` and
  `ProbabilityTheory.Kernel.Communicates.isNullRecurrent_iff`: class property of null recurrence.
* `Kernel.forall_isTransient_or_forall_isPositiveRecurrent_or_forall_isNullRecurrent`:
  global recurrence trichotomy for counting-measure-irreducible chains.
* `Kernel.isNullRecurrent_iff_isRecurrent_and_tendsto_integral_visitCount_div_zero` and
  `Kernel.isNullRecurrent_iff_isRecurrent_and_ae_tendsto_visitCount_div_zero`:
  expected and almost-sure occupation-frequency characterizations of null recurrence.
* `Kernel.IsClosedSet.isPositiveRecurrent_of_finite_communicatingClass`,
  `Kernel.IsClosedSet.existsUnique_invariant_probability_communicatingClass_of_isPositiveRecurrent`,
  `Kernel.IsClosedSet.existsUnique_invariant_probability_of_finite_communicatingClass`,
  `Kernel.IsRecurrent.isPositiveRecurrent_of_finite_communicatingClass`,
  `Kernel.isRecurrent_iff_isPositiveRecurrent_of_finite`, and
  `Kernel.not_isNullRecurrent_of_finite`: finite closed communicating classes and finite state
  spaces.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.5, 1.7, and 1.10.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer (2002), Theorem 8.6.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TauCeti TauCeti.Probability
open scoped ENNReal Topology

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ] {x y : S}

/-! ### Null recurrence and the state recurrence trichotomy -/

/-- A state is null recurrent if it returns almost surely but its extended mean
positive return time is infinite. -/
def IsNullRecurrent (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : Prop :=
  κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞

/-- The defining characterization of null recurrence. -/
theorem isNullRecurrent_iff :
    κ.IsNullRecurrent x ↔ κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞ := Iff.rfl

/-- Congruence in the kernel argument of `Kernel.IsNullRecurrent`. -/
theorem isNullRecurrent_congr {η : Kernel S S} [IsMarkovKernel η] (h : κ = η) (x : S) :
    κ.IsNullRecurrent x ↔ η.IsNullRecurrent x := by
  subst h
  rfl

/-- Null recurrence is recurrence without positive recurrence. The recurrence condition
cannot be omitted: transient states also have infinite mean return time. -/
theorem isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent :
    κ.IsNullRecurrent x ↔ κ.IsRecurrent x ∧ ¬ κ.IsPositiveRecurrent x := by
  simp [isNullRecurrent_iff, isPositiveRecurrent_iff, lt_top_iff_ne_top]

/-- Every null recurrent state is recurrent. -/
theorem IsNullRecurrent.isRecurrent (hx : κ.IsNullRecurrent x) : κ.IsRecurrent x :=
  hx.1

/-- A null recurrent state has infinite extended mean positive return time. -/
theorem IsNullRecurrent.meanReturnTime_eq_top (hx : κ.IsNullRecurrent x) :
    κ.meanReturnTime x = ∞ := hx.2

/-- A null recurrent state is not positive recurrent. -/
theorem IsNullRecurrent.not_isPositiveRecurrent (hx : κ.IsNullRecurrent x) :
    ¬ κ.IsPositiveRecurrent x :=
  (isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent.mp hx).2

/-- A null recurrent state is not transient. -/
theorem IsNullRecurrent.not_isTransient (hx : κ.IsNullRecurrent x) : ¬ κ.IsTransient x := by
  rw [isTransient_iff, not_not]
  exact hx.isRecurrent

/-- A positive recurrent state is not null recurrent. -/
theorem IsPositiveRecurrent.not_isNullRecurrent (hx : κ.IsPositiveRecurrent x) :
    ¬ κ.IsNullRecurrent x :=
  fun h => h.not_isPositiveRecurrent hx

/-- A transient state is not null recurrent. -/
theorem IsTransient.not_isNullRecurrent (hx : κ.IsTransient x) : ¬ κ.IsNullRecurrent x :=
  fun h => h.not_isTransient hx

/-- Every recurrent state is either positive recurrent or null recurrent. -/
theorem IsRecurrent.isPositiveRecurrent_or_isNullRecurrent (hx : κ.IsRecurrent x) :
    κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x := by
  by_cases hpos : κ.IsPositiveRecurrent x
  · exact Or.inl hpos
  · exact Or.inr (isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent.mpr ⟨hx, hpos⟩)

/-- Recurrence splits into the positive and null cases. -/
theorem isRecurrent_iff_isPositiveRecurrent_or_isNullRecurrent :
    κ.IsRecurrent x ↔ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x :=
  ⟨IsRecurrent.isPositiveRecurrent_or_isNullRecurrent,
    fun h => h.elim IsPositiveRecurrent.isRecurrent IsNullRecurrent.isRecurrent⟩

/-- **State recurrence trichotomy.** Every state of a Markov kernel is transient, positive
recurrent, or null recurrent. -/
theorem isTransient_or_isPositiveRecurrent_or_isNullRecurrent (κ : Kernel S S)
    [IsMarkovKernel κ] (x : S) :
    κ.IsTransient x ∨ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x := by
  by_cases hx : κ.IsRecurrent x
  · exact Or.inr hx.isPositiveRecurrent_or_isNullRecurrent
  · exact Or.inl (isTransient_iff.mpr hx)

/-- A state fails to be positive recurrent if and only if it is transient or null recurrent. -/
theorem not_isPositiveRecurrent_iff :
    ¬ κ.IsPositiveRecurrent x ↔ κ.IsTransient x ∨ κ.IsNullRecurrent x := by
  constructor
  · intro hnot
    rcases κ.isTransient_or_isPositiveRecurrent_or_isNullRecurrent x with ht | hp | hn
    · exact Or.inl ht
    · exact absurd hp hnot
    · exact Or.inr hn
  · rintro (ht | hn)
    · exact ht.not_isPositiveRecurrent
    · exact hn.not_isPositiveRecurrent

/-- A state fails to be null recurrent if and only if it is transient or positive recurrent. -/
theorem not_isNullRecurrent_iff :
    ¬ κ.IsNullRecurrent x ↔ κ.IsTransient x ∨ κ.IsPositiveRecurrent x := by
  constructor
  · intro hnot
    rcases κ.isTransient_or_isPositiveRecurrent_or_isNullRecurrent x with ht | hp | hn
    · exact Or.inl ht
    · exact Or.inr hp
    · exact absurd hn hnot
  · rintro (ht | hp)
    · exact ht.not_isNullRecurrent
    · exact hp.not_isNullRecurrent

/-- The extended mean return time of `x` is infinite if and only if `x` is transient or null
recurrent. -/
theorem meanReturnTime_eq_top_iff :
    κ.meanReturnTime x = ∞ ↔ κ.IsTransient x ∨ κ.IsNullRecurrent x := by
  rw [← not_lt_top_iff, ← isPositiveRecurrent_iff, not_isPositiveRecurrent_iff]

/-! ### Restriction to a closed set and singleton-free properties -/

/-- Restriction to a closed set preserves and reflects positive recurrence. -/
@[simp]
theorem isPositiveRecurrent_subtype_iff {s : Set S} (hs : MeasurableSet s)
    [IsMarkovKernel (κ.subtype hs)] (x : s) :
    (κ.subtype hs).IsPositiveRecurrent x ↔ κ.IsPositiveRecurrent x.val := by
  simp only [isPositiveRecurrent_iff, meanReturnTime_subtype]

/-- Restriction to a closed set preserves and reflects null recurrence. -/
@[simp]
theorem isNullRecurrent_subtype_iff {s : Set S} (hs : MeasurableSet s)
    [IsMarkovKernel (κ.subtype hs)] (x : s) :
    (κ.subtype hs).IsNullRecurrent x ↔ κ.IsNullRecurrent x.val := by
  simp only [isNullRecurrent_iff, isRecurrent_subtype_iff, meanReturnTime_subtype]

/-- A deterministic kernel has no null recurrent states on any measurable space. -/
@[simp]
theorem not_isNullRecurrent_deterministic {f : S → S} (hf : Measurable f) (x : S) :
    ¬ (deterministic f hf).IsNullRecurrent x := by
  -- If `x` is recurrent under `f`, some positive iterate `f^[k] x` shares its Dirac measure with
  -- `x`; pushing that equality forward along `Function.update w₀ k` bounds the mean return time by
  -- `k`.
  rintro ⟨hrec, hmean⟩
  let w₀ : ℕ → S := fun n => f^[n] x
  have hex : ∃ k : ℕ, 1 ≤ k ∧ (Measure.dirac (w₀ k) : Measure S) = Measure.dirac x := by
    have hne : (deterministic f hf).returnLengths x ≠ ∅ :=
      period_eq_zero_iff.not.mp hrec.period_pos.ne'
    obtain ⟨k, hk⟩ := Set.ne_empty_iff_nonempty.mp hne
    rw [mem_returnLengths] at hk
    obtain ⟨hk_pos, hpos⟩ := hk
    rw [deterministic_pow, deterministic_apply] at hpos
    exact ⟨k, hk_pos, Measure.eq_dirac_of_measure_singleton_eq_one
      (Measure.dirac_apply_eq_zero_or_one.resolve_left hpos.ne')⟩
  obtain ⟨k, hk, hdirac_k⟩ := hex
  let w' : ℕ → S := Function.update w₀ k x
  have hdirac : (Measure.dirac w₀ : Measure (ℕ → S)) = Measure.dirac w' := by
    calc
      (Measure.dirac w₀ : Measure (ℕ → S))
        = Measure.dirac (Function.update w₀ k (w₀ k)) := by rw [Function.update_eq_self]
      _ = (Measure.dirac (w₀ k)).map (Function.update w₀ k) :=
          (Measure.map_dirac' (measurable_update w₀) (w₀ k)).symm
      _ = (Measure.dirac x).map (Function.update w₀ k) := by rw [hdirac_k]
      _ = Measure.dirac w' := Measure.map_dirac' (measurable_update w₀) x
  have hlt : (deterministic f hf).meanReturnTime x ≤ (k : ℝ≥0∞) := by
    rw [meanReturnTime_def, markovChainLaw_dirac_deterministic, hdirac]
    exact (lintegral_dirac_le w' _).trans
      (ENat.toENNReal_mono (hittingAfter_le_of_mem hk (by simp [w'])))
  exact (hlt.trans_lt (ENNReal.natCast_lt_top k)).ne hmean

/-- Under `const S (Measure.dirac a)`, no state is null recurrent on any measurable space. -/
@[simp]
theorem not_isNullRecurrent_const_dirac (a x : S) :
    ¬ (const S (Measure.dirac a)).IsNullRecurrent x := by
  rw [isNullRecurrent_congr (const_dirac_eq_deterministic a)]
  exact not_isNullRecurrent_deterministic measurable_const x

/-! ### Class properties and invariant measures -/

section MeasurableSingleton

variable [MeasurableSingletonClass S]

/-- Communicating states are null recurrent together. -/
theorem Communicates.isNullRecurrent_iff (hxy : κ.Communicates x y) :
    κ.IsNullRecurrent x ↔ κ.IsNullRecurrent y := by
  simp only [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    hxy.isRecurrent_iff, hxy.isPositiveRecurrent_iff]

/-- Every state reachable from a null recurrent state is null recurrent. -/
theorem IsNullRecurrent.of_reaches (hx : κ.IsNullRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsNullRecurrent y :=
  (Communicates.isNullRecurrent_iff
    ((communicates_def x y).mpr ⟨hxy, hx.isRecurrent.reaches_of_reaches hxy⟩)).mp hx

/-- Null recurrence of a counting-measure-irreducible chain does not depend on the state. -/
theorem isNullRecurrent_iff_isNullRecurrent [IsIrreducible Measure.count κ] (x y : S) :
    κ.IsNullRecurrent x ↔ κ.IsNullRecurrent y :=
  Communicates.isNullRecurrent_iff (isIrreducible_count_iff_forall_communicates.mp ‹_› x y)

/-- **Global recurrence trichotomy for irreducible Markov chains.** In a
counting-measure-irreducible Markov chain, either every state is transient, every state is positive
recurrent, or every state is null recurrent. -/
theorem forall_isTransient_or_forall_isPositiveRecurrent_or_forall_isNullRecurrent
    (κ : Kernel S S) [IsMarkovKernel κ] [IsIrreducible Measure.count κ] :
    (∀ x, κ.IsTransient x) ∨ (∀ x, κ.IsPositiveRecurrent x) ∨ (∀ x, κ.IsNullRecurrent x) := by
  rcases isEmpty_or_nonempty S with hEmpty | hne
  · exact Or.inl fun x => hEmpty.elim x
  · obtain ⟨x₀⟩ := hne
    rcases κ.isTransient_or_isPositiveRecurrent_or_isNullRecurrent x₀ with ht | hp | hn
    · exact Or.inl fun x => (isTransient_iff_isTransient x₀ x).mp ht
    · exact Or.inr (Or.inl fun x => (isPositiveRecurrent_iff_isPositiveRecurrent x₀ x).mp hp)
    · exact Or.inr (Or.inr fun x => (isNullRecurrent_iff_isNullRecurrent x₀ x).mp hn)

end MeasurableSingleton

/-! ### Countable state spaces: occupation-frequency characterizations -/

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- **Expected occupation characterization of null recurrence.** A state `y` is null recurrent if
and only if it is recurrent and its expected positive-time visit fraction starting from `y` tends
to zero. -/
theorem isNullRecurrent_iff_isRecurrent_and_tendsto_integral_visitCount_div_zero :
    κ.IsNullRecurrent y ↔
      κ.IsRecurrent y ∧
        Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
          ∂markovChainLaw (Measure.dirac y) κ) atTop (𝓝 0) := by
  rw [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    ← inv_meanReturnTime_toReal_eq_zero_iff]
  refine and_congr_right fun _ => ⟨fun h0 => ?_, fun hlim =>
    tendsto_nhds_unique (κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y) hlim⟩
  simpa only [h0] using κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y

/-- **Almost-sure occupation characterization of null recurrence.** A state `y` is null recurrent if
and only if it is recurrent and its positive-time visit fraction starting from `y` tends to zero
almost surely. -/
theorem isNullRecurrent_iff_isRecurrent_and_ae_tendsto_visitCount_div_zero :
    κ.IsNullRecurrent y ↔
      κ.IsRecurrent y ∧
        ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ,
          Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) y n : ℝ) / n) atTop (𝓝 0) := by
  rw [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    ← inv_meanReturnTime_toReal_eq_zero_iff]
  refine and_congr_right fun _ => ⟨fun h0 => ?_, fun hae => ?_⟩
  · simpa only [h0] using κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y
  · obtain ⟨ω, hω₁, hω₂⟩ := ((κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y).and hae).exists
    exact tendsto_nhds_unique hω₁ hω₂

end Countable

/-! ### Finite closed communicating classes and finite state spaces -/

section FiniteClass

variable [MeasurableSingletonClass S]

/-- **Every finite closed communicating class is positive recurrent.** If the communicating class
of `x` is closed under `κ` and finite, then every state in `κ.communicatingClass x` is positive
recurrent. No countability assumption on the ambient state space is required. -/
theorem IsClosedSet.isPositiveRecurrent_of_finite_communicatingClass
    (hclosed : κ.IsClosedSet (κ.communicatingClass x))
    (hfin : (κ.communicatingClass x).Finite) (hy : y ∈ κ.communicatingClass x) :
    κ.IsPositiveRecurrent y := by
  have hs : MeasurableSet (κ.communicatingClass x) := hfin.measurableSet
  have : Finite (κ.communicatingClass x) := hfin.to_subtype
  have : IsMarkovKernel (κ.subtype hs) := (isMarkovKernel_subtype_iff_isClosedSet hs).mpr hclosed
  have : IsIrreducible Measure.count (κ.subtype hs) :=
    hclosed.isIrreducible_subtype_communicatingClass hs
  exact (isPositiveRecurrent_subtype_iff hs ⟨y, hy⟩).mp
    ((κ.subtype hs).isPositiveRecurrent_of_finite ⟨y, hy⟩)

/-- **Existence and uniqueness of the stationary law on a positive recurrent closed communicating
class.** If `κ.communicatingClass x` is measurable and closed and `x` is positive recurrent, then
`κ` admits a unique invariant probability measure concentrated on `κ.communicatingClass x`. -/
theorem IsClosedSet.existsUnique_invariant_probability_communicatingClass_of_isPositiveRecurrent
    (hclosed : κ.IsClosedSet (κ.communicatingClass x))
    (hs : MeasurableSet (κ.communicatingClass x)) (hx : κ.IsPositiveRecurrent x) :
    ∃! π : Measure S,
      IsProbabilityMeasure π ∧ κ.Invariant π ∧ π (κ.communicatingClass x)ᶜ = 0 := by
  have : IsMarkovKernel (κ.subtype hs) := (isMarkovKernel_subtype_iff_isClosedSet hs).mpr hclosed
  have : IsIrreducible Measure.count (κ.subtype hs) :=
    hclosed.isIrreducible_subtype_communicatingClass hs
  let x_s : κ.communicatingClass x := ⟨x, mem_communicatingClass_self x⟩
  have hx_s : (κ.subtype hs).IsPositiveRecurrent x_s :=
    (isPositiveRecurrent_subtype_iff hs x_s).mpr hx
  exact (existsUnique_invariant_probability_subtype_iff κ hs hclosed).mp
    hx_s.existsUnique_invariant_probability

/-- **Existence and uniqueness of the stationary law on a finite closed communicating class.**
If `κ.communicatingClass x` is closed and finite, then `κ` admits a unique invariant probability
measure concentrated on `κ.communicatingClass x`. -/
theorem IsClosedSet.existsUnique_invariant_probability_of_finite_communicatingClass
    (hclosed : κ.IsClosedSet (κ.communicatingClass x))
    (hfin : (κ.communicatingClass x).Finite) :
    ∃! π : Measure S,
      IsProbabilityMeasure π ∧ κ.Invariant π ∧ π (κ.communicatingClass x)ᶜ = 0 :=
  hclosed.existsUnique_invariant_probability_communicatingClass_of_isPositiveRecurrent
    hfin.measurableSet
    (hclosed.isPositiveRecurrent_of_finite_communicatingClass hfin
      (mem_communicatingClass_self x))

/-- On a countable state space, a recurrent state with a finite communicating class
is positive recurrent. -/
theorem IsRecurrent.isPositiveRecurrent_of_finite_communicatingClass [Countable S]
    (hx : κ.IsRecurrent x) (hfinite : (κ.communicatingClass x).Finite) :
    κ.IsPositiveRecurrent x :=
  hx.isClosedSet_communicatingClass.isPositiveRecurrent_of_finite_communicatingClass
    hfinite (mem_communicatingClass_self x)

/-- On a countable state space, a null recurrent state has an infinite communicating class. -/
theorem IsNullRecurrent.infinite_communicatingClass [Countable S] (hx : κ.IsNullRecurrent x) :
    (κ.communicatingClass x).Infinite := by
  intro hfinite
  exact hx.not_isPositiveRecurrent
    (hx.isRecurrent.isPositiveRecurrent_of_finite_communicatingClass hfinite)

/-- On a finite state space with measurable singletons, every recurrent state is positive
recurrent, with no irreducibility hypothesis on `κ`. -/
theorem IsRecurrent.isPositiveRecurrent_of_finite [Finite S] (hx : κ.IsRecurrent x) :
    κ.IsPositiveRecurrent x :=
  hx.isPositiveRecurrent_of_finite_communicatingClass (Set.toFinite _)

/-- On a finite state space, a state is recurrent exactly when it is positive recurrent;
no irreducibility assumption is needed. -/
theorem isRecurrent_iff_isPositiveRecurrent_of_finite [Finite S] :
    κ.IsRecurrent x ↔ κ.IsPositiveRecurrent x :=
  ⟨IsRecurrent.isPositiveRecurrent_of_finite, IsPositiveRecurrent.isRecurrent⟩

/-- No state of a finite state space is null recurrent. -/
@[simp]
theorem not_isNullRecurrent_of_finite [Finite S] : ¬ κ.IsNullRecurrent x :=
  fun hx => hx.infinite_communicatingClass (Set.toFinite _)

/-- Almost every path of a finite-state Markov chain eventually enters and remains in the closed
communicating class of a positive recurrent state. -/
theorem ae_exists_isPositiveRecurrent_and_forall_mem_communicatingClass [Finite S]
    (κ : Kernel S S) [IsMarkovKernel κ] (ν : Measure S) :
    ∀ᵐ w ∂markovChainLaw ν κ, ∃ n,
      κ.IsPositiveRecurrent (w n) ∧ κ.IsClosedSet (κ.communicatingClass (w n)) ∧
        ∀ m, n ≤ m → w m ∈ κ.communicatingClass (w n) := by
  filter_upwards [κ.ae_exists_forall_mem_isClosedSet_communicatingClass ν] with w ⟨n, hclosed, hm⟩
  exact ⟨n, hclosed.isPositiveRecurrent_of_finite_communicatingClass (Set.toFinite _)
    (mem_communicatingClass_self _), hclosed, hm⟩

end FiniteClass

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

section Finite

variable {S Ω : Type*} [MeasurableSpace S] [Finite S] [MeasurableSingletonClass S]
  [MeasurableSpace Ω] {κ : Kernel S S} [IsMarkovKernel κ]
  {ν : Measure S} {μ : Measure Ω} {X : ℕ → Ω → S}

/-- Almost every path of any realization of a finite-state Markov chain eventually enters and
remains in the closed communicating class of a positive recurrent state. -/
theorem ae_exists_isPositiveRecurrent_and_forall_mem_communicatingClass
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) :
    ∀ᵐ ω ∂μ, ∃ n,
      κ.IsPositiveRecurrent (X n ω) ∧ κ.IsClosedSet (κ.communicatingClass (X n ω)) ∧
        ∀ m, n ≤ m → X m ω ∈ κ.communicatingClass (X n ω) := by
  have hae := κ.ae_exists_isPositiveRecurrent_and_forall_mem_communicatingClass ν
  rw [← h.map_eq] at hae
  exact ae_of_ae_map h.aemeasurable hae

end Finite

end ProbabilityTheory.HasLaw
