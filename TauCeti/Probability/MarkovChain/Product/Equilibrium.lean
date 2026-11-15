/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Equilibrium
public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.Stationary

/-!
# Recurrence, stationary laws, and equilibrium of independent product chains

Let `κ : Kernel α α` and `η : Kernel β β` be Markov transition kernels and write `κ ∥ₖ η` for their
independent parallel composition on `α × β`.

* **Coordinate path laws and stationarity.** Pushing `markovChainLaw ρ (κ ∥ₖ η)` forward along
  either coordinate projection yields the coordinate Markov chain started from the corresponding
  marginal of `ρ` (`Measure.markovChainLaw_parallelComp_map_fst`,
  `Measure.markovChainLaw_parallelComp_map_snd`), without independence of `ρ` or countability of
  the state spaces. For nonzero finite initial measures `μ` and `ν`, the product path law
  `markovChainLaw (μ.prod ν) (κ ∥ₖ η)` is shift-invariant if and only if `μ` is `κ`-invariant and
  `ν` is `η`-invariant (`Measure.measurePreserving_shift_markovChainLaw_prod_iff_of_ne_zero`).
* **Unconditional return-time bounds and positive recurrence.** Without any irreducibility,
  aperiodicity, or countability assumptions, coordinate projection bounds each marginal mean return
  time by the joint mean return time (`meanReturnTime_le_parallelComp_left`,
  `meanReturnTime_le_parallelComp_right`), while superharmonicity of the product of cycle
  occupation measures yields `(κ ∥ₖ η).cycleOccupation z ≤ (κ.cycleOccupation z.1).prod
  (η.cycleOccupation z.2)` (`cycleOccupation_parallelComp_le`) and
  `(κ ∥ₖ η).meanReturnTime z ≤ κ.meanReturnTime z.1 * η.meanReturnTime z.2`
  (`meanReturnTime_parallelComp_le`) at every state `z`. Consequently, `z` is positive recurrent for
  `κ ∥ₖ η` if and only if `z.1` is positive recurrent for `κ` and `z.2` is positive recurrent for
  `η` (`isPositiveRecurrent_parallelComp_iff`).
* **Irreducibility and exact product factorization.** Counting-measure irreducibility of `κ ∥ₖ η`
  projects to each coordinate on nonempty factor spaces (`isIrreducible_of_parallelComp_left`,
  `isIrreducible_of_parallelComp_right`), and conversely holds whenever `κ` and `η` are
  counting-measure irreducible and at least one factor is aperiodic
  (`IsAperiodic.isIrreducible_parallelComp_left`, `IsAperiodic.isIrreducible_parallelComp_right`).
  When `κ ∥ₖ η` is irreducible, every invariant probability measure `ρ` factors as
  `ρ = ρ.fst.prod ρ.snd` (`Invariant.eq_fst_prod_snd_of_parallelComp`), the cycle occupation
  measure at any recurrent state `z` factors as `(κ.cycleOccupation z.1).prod (η.cycleOccupation
  z.2)` (`IsRecurrent.cycleOccupation_parallelComp`), and the mean return time satisfies the exact
  product identity `(κ ∥ₖ η).meanReturnTime z = κ.meanReturnTime z.1 * η.meanReturnTime z.2`
  (`meanReturnTime_parallelComp`). When both factors are irreducible and aperiodic, any joint
  initial probability law on `α × β` converges in total variation to the product equilibrium law
  `π₁.prod π₂` (`Invariant.tendsto_tvDist_parallelComp_pow_comp`,
  `IsPositiveRecurrent.tendsto_tvDist_parallelComp_pow_comp`), with sample-space realization
  transfers under `ProbabilityTheory.HasLaw`.
* **Sharpness of irreducibility.** For deterministic parallel products, the mean return time on
  periodic points is the least common multiple of the coordinate minimal periods
  (`meanReturnTime_deterministic_parallelComp_deterministic`). Two copies of the deterministic flip
  chain `deterministic (! ·)` on `Bool` are individually irreducible and positive recurrent with
  mean return time `2`, yet their parallel product is reducible
  (`not_isIrreducible_parallelComp_deterministic_not`), has mean return time `2 < 2 * 2`
  (`meanReturnTime_parallelComp_deterministic_not_lt`), and admits a correlated diagonal invariant
  probability measure distinct from the product of its marginals
  (`exists_invariant_probability_parallelComp_deterministic_not_ne_prod`).

## Main statements

* `MeasureTheory.Measure.markovChainLaw_parallelComp_map_fst`,
  `MeasureTheory.Measure.markovChainLaw_parallelComp_map_snd`,
  `MeasureTheory.Measure.measurePreserving_shift_markovChainLaw_prod_iff`: coordinate projections
  and shift-stationarity characterization of product path laws.
* `ProbabilityTheory.Kernel.cycleOccupation_parallelComp_le`,
  `ProbabilityTheory.Kernel.meanReturnTime_parallelComp_le`,
  `ProbabilityTheory.Kernel.isPositiveRecurrent_parallelComp_iff`: unconditional cycle-occupation
  bound, mean-return-time inequalities, and characterization of positive recurrence on `κ ∥ₖ η`.
* `ProbabilityTheory.Kernel.IsAperiodic.isIrreducible_parallelComp_left`,
  `ProbabilityTheory.Kernel.IsAperiodic.isIrreducible_parallelComp_right`: one-sided aperiodicity
  suffices for irreducibility of `κ ∥ₖ η`.
* `ProbabilityTheory.Kernel.Invariant.eq_fst_prod_snd_of_parallelComp`,
  `ProbabilityTheory.Kernel.IsRecurrent.cycleOccupation_parallelComp`,
  `ProbabilityTheory.Kernel.meanReturnTime_parallelComp`: exact factorization of invariant
  probabilities, cycle occupation measures, and mean return times on irreducible product chains.
* `ProbabilityTheory.Kernel.Invariant.tendsto_tvDist_parallelComp_pow_comp`,
  `ProbabilityTheory.Kernel.IsPositiveRecurrent.tendsto_tvDist_parallelComp_pow_comp`,
  `ProbabilityTheory.HasLaw.tendsto_tvDist_prodMk_of_invariant`,
  `ProbabilityTheory.HasLaw.tendsto_tvDist_prodMk_of_isPositiveRecurrent`: total-variation
  convergence of irreducible aperiodic product chains and independent realizations.
* `ProbabilityTheory.Kernel.not_isIrreducible_parallelComp_deterministic_not`,
  `ProbabilityTheory.Kernel.meanReturnTime_parallelComp_deterministic_not_lt`,
  `ProbabilityTheory.Kernel.exists_invariant_probability_parallelComp_deterministic_not_ne_prod`:
  concrete two-cycle witnesses showing that irreducibility of both factors does not imply
  irreducibility, product mean return times, or coordinate independence of invariant probabilities
  on `κ ∥ₖ η`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.7–1.8.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer (2002), Chapter 8.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti.Probability
open scoped ENNReal Topology

/-! ### Coordinate projections and stationary product path laws -/

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The first coordinate of a chain driven by `κ ∥ₖ η` from any finite initial joint law `ρ` has
path law `markovChainLaw ρ.fst κ`. Neither independence of `ρ` nor countability is required. -/
@[simp]
theorem markovChainLaw_parallelComp_map_fst (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (markovChainLaw ρ (κ ∥ₖ η)).map (fun ω n => (ω n).1) = markovChainLaw ρ.fst κ :=
  markovChainLaw_map_comp ρ (κ ∥ₖ η) κ measurable_fst fun p => by
    simp [Kernel.parallelComp_apply]

/-- The second coordinate of a chain driven by `κ ∥ₖ η` from any finite initial joint law `ρ` has
path law `markovChainLaw ρ.snd η`. Neither independence of `ρ` nor countability is required. -/
@[simp]
theorem markovChainLaw_parallelComp_map_snd (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    (markovChainLaw ρ (κ ∥ₖ η)).map (fun ω n => (ω n).2) = markovChainLaw ρ.snd η :=
  markovChainLaw_map_comp ρ (κ ∥ₖ η) η measurable_snd fun p => by
    simp [Kernel.parallelComp_apply]

/-- For nonzero finite initial measures `μ` and `ν`, the independent product path law
`markovChainLaw (μ.prod ν) (κ ∥ₖ η)` is shift-invariant if and only if `μ` is `κ`-invariant and
`ν` is `η`-invariant. -/
theorem measurePreserving_shift_markovChainLaw_prod_iff_of_ne_zero
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    MeasurePreserving (shift (α × β))
        (markovChainLaw (μ.prod ν) (κ ∥ₖ η)) (markovChainLaw (μ.prod ν) (κ ∥ₖ η)) ↔
      κ.Invariant μ ∧ η.Invariant ν := by
  rw [measurePreserving_shift_markovChainLaw_iff,
    Kernel.invariant_parallelComp_prod_iff_of_ne_zero hμ hν]

/-- For initial probability measures `μ` and `ν`, the independent product path law
`markovChainLaw (μ.prod ν) (κ ∥ₖ η)` is shift-invariant if and only if both `μ` and `ν` are
invariant for their coordinate kernels. -/
theorem measurePreserving_shift_markovChainLaw_prod_iff
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    MeasurePreserving (shift (α × β))
        (markovChainLaw (μ.prod ν) (κ ∥ₖ η)) (markovChainLaw (μ.prod ν) (κ ∥ₖ η)) ↔
      κ.Invariant μ ∧ η.Invariant ν :=
  measurePreserving_shift_markovChainLaw_prod_iff_of_ne_zero
    (IsProbabilityMeasure.ne_zero μ) (IsProbabilityMeasure.ne_zero ν) κ η

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

/-- Every time shift of a pair of independent stationary Markov chains on an arbitrary measurable
sample space has the stationary product path law `markovChainLaw (μ.prod ν) (κ ∥ₖ η)`. Finiteness
of `μ` follows from `[IsFiniteMeasure ν]` through the shared law `P`. -/
theorem processShift_prodMk_markovChainLaw
    {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
    [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {P : Measure Ω} {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {X : ℕ → Ω → α} {Y : ℕ → Ω → β}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw μ κ) P)
    (hY : HasLaw (fun ω n => Y n ω) (markovChainLaw ν η) P)
    (hindep : IndepFun (fun ω n => X n ω) (fun ω n => Y n ω) P)
    (hμ : κ.Invariant μ) (hν : η.Invariant ν) (m : ℕ) :
    HasLaw (processShift (fun n ω => (X n ω, Y n ω)) m)
      (markovChainLaw (μ.prod ν) (κ ∥ₖ η)) P := by
  have : IsFiniteMeasure P := hY.isFiniteMeasure
  have : IsFiniteMeasure (markovChainLaw μ κ) := hX.isFiniteMeasure_iff.mp inferInstance
  have : IsFiniteMeasure μ := by
    rw [← markovChainLaw_map_eval_zero μ κ]
    infer_instance
  exact (hX.prodMk_markovChainLaw hY hindep).processShift_markovChainLaw (hμ.parallelComp hν) m

end ProbabilityTheory.HasLaw

/-! ### Unconditional return-time bounds and positive recurrence for parallel products -/

namespace ProbabilityTheory.Kernel

section CoordinateBounds

private theorem hittingAfter_fst_le {α β : Type*} (z : α × β) (k : ℕ) (w : ℕ → α × β) :
    hittingAfter (fun n (u : ℕ → α) => u n) {z.1} k (fun n => (w n).1) ≤
      hittingAfter (fun n w => w n) {z} k w := by
  induction h : hittingAfter (fun n w => w n) {z} k w using WithTop.recTopCoe with
  | top => exact le_top
  | coe i =>
    obtain ⟨j, hj, hwj⟩ := hittingAfter_le_iff.mp h.le
    exact hittingAfter_le_iff.mpr ⟨j, hj, congrArg Prod.fst hwj⟩

private theorem hittingAfter_snd_le {α β : Type*} (z : α × β) (k : ℕ) (w : ℕ → α × β) :
    hittingAfter (fun n (u : ℕ → β) => u n) {z.2} k (fun n => (w n).2) ≤
      hittingAfter (fun n w => w n) {z} k w := by
  induction h : hittingAfter (fun n w => w n) {z} k w using WithTop.recTopCoe with
  | top => exact le_top
  | coe i =>
    obtain ⟨j, hj, hwj⟩ := hittingAfter_le_iff.mp h.le
    exact hittingAfter_le_iff.mpr ⟨j, hj, congrArg Prod.snd hwj⟩

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The cycle occupation measure at any state of a Markov kernel is s-finite, as a countable sum
of pushforwards of restricted probability laws. -/
instance instSFiniteCycleOccupation (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    SFinite (κ.cycleOccupation x) := by
  rw [cycleOccupation_def]
  infer_instance

/-- Recurrence of `z` under `κ ∥ₖ η` implies recurrence of `z.1` under `κ`. Only measurable
singletons on the first coordinate space are needed. -/
theorem IsRecurrent.of_parallelComp_left [MeasurableSingletonClass α]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsRecurrent z) :
    κ.IsRecurrent z.1 := by
  have hE : MeasurableSet {u : ℕ → α | hittingAfter (fun n u => u n) {z.1} 1 u ≠ ⊤} :=
    measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton z.1) 1
  have hmap : markovChainLaw (Measure.dirac z.1) κ =
      (markovChainLaw (Measure.dirac z) (κ ∥ₖ η)).map (fun w n => (w n).1) := by
    rw [Measure.markovChainLaw_parallelComp_map_fst, Measure.fst,
      Measure.map_dirac' measurable_fst]
  rw [isRecurrent_iff, hmap, Measure.map_apply (by fun_prop) hE]
  refine le_antisymm prob_le_one ?_
  rw [← isRecurrent_iff.mp hz]
  exact measure_mono fun w hw => ne_top_of_le_ne_top hw (hittingAfter_fst_le z 1 w)

/-- Recurrence of `z` under `κ ∥ₖ η` implies recurrence of `z.2` under `η`. Only measurable
singletons on the second coordinate space are needed. -/
theorem IsRecurrent.of_parallelComp_right [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsRecurrent z) :
    η.IsRecurrent z.2 := by
  have hE : MeasurableSet {u : ℕ → β | hittingAfter (fun n u => u n) {z.2} 1 u ≠ ⊤} :=
    measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton z.2) 1
  have hmap : markovChainLaw (Measure.dirac z.2) η =
      (markovChainLaw (Measure.dirac z) (κ ∥ₖ η)).map (fun w n => (w n).2) := by
    rw [Measure.markovChainLaw_parallelComp_map_snd, Measure.snd,
      Measure.map_dirac' measurable_snd]
  rw [isRecurrent_iff, hmap, Measure.map_apply (by fun_prop) hE]
  refine le_antisymm prob_le_one ?_
  rw [← isRecurrent_iff.mp hz]
  exact measure_mono fun w hw => ne_top_of_le_ne_top hw (hittingAfter_snd_le z 1 w)

/-- If `x` is transient under `κ`, then `(x, y)` is transient under `κ ∥ₖ η` for every `y`. -/
theorem IsTransient.parallelComp_left [MeasurableSingletonClass α]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {x : α} (hx : κ.IsTransient x) (y : β) :
    (κ ∥ₖ η).IsTransient (x, y) :=
  isTransient_iff.mpr fun hrec => isTransient_iff.mp hx hrec.of_parallelComp_left

/-- If `y` is transient under `η`, then `(x, y)` is transient under `κ ∥ₖ η` for every `x`. -/
theorem IsTransient.parallelComp_right [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    (x : α) {y : β} (hy : η.IsTransient y) :
    (κ ∥ₖ η).IsTransient (x, y) :=
  isTransient_iff.mpr fun hrec => isTransient_iff.mp hy hrec.of_parallelComp_right

/-- Returning to `z` requires returning to `z.1`, so the first-coordinate mean return time never
exceeds the joint mean return time. -/
theorem meanReturnTime_le_parallelComp_left [MeasurableSingletonClass α]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    κ.meanReturnTime z.1 ≤ (κ ∥ₖ η).meanReturnTime z := by
  have hτ : Measurable fun u : ℕ → α =>
      ENat.toENNReal (hittingAfter (fun n u => u n) {z.1} 1 u) :=
    Measurable.of_discrete.comp
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton z.1)).measurable'
  have hmap : markovChainLaw (Measure.dirac z.1) κ =
      (markovChainLaw (Measure.dirac z) (κ ∥ₖ η)).map (fun w n => (w n).1) := by
    rw [Measure.markovChainLaw_parallelComp_map_fst, Measure.fst,
      Measure.map_dirac' measurable_fst]
  rw [meanReturnTime_def, meanReturnTime_def, hmap,
    MeasureTheory.lintegral_map hτ (by fun_prop)]
  exact lintegral_mono fun w => ENat.toENNReal_mono (hittingAfter_fst_le z 1 w)

/-- Returning to `z` requires returning to `z.2`, so the second-coordinate mean return time never
exceeds the joint mean return time. -/
theorem meanReturnTime_le_parallelComp_right [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    η.meanReturnTime z.2 ≤ (κ ∥ₖ η).meanReturnTime z := by
  have hτ : Measurable fun u : ℕ → β =>
      ENat.toENNReal (hittingAfter (fun n u => u n) {z.2} 1 u) :=
    Measurable.of_discrete.comp
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => β)) (measurableSet_singleton z.2)).measurable'
  have hmap : markovChainLaw (Measure.dirac z.2) η =
      (markovChainLaw (Measure.dirac z) (κ ∥ₖ η)).map (fun w n => (w n).2) := by
    rw [Measure.markovChainLaw_parallelComp_map_snd, Measure.snd,
      Measure.map_dirac' measurable_snd]
  rw [meanReturnTime_def, meanReturnTime_def, hmap,
    MeasureTheory.lintegral_map hτ (by fun_prop)]
  exact lintegral_mono fun w => ENat.toENNReal_mono (hittingAfter_snd_le z 1 w)

/-- Positive recurrence of `z` under `κ ∥ₖ η` implies positive recurrence of `z.1` under `κ`. -/
theorem IsPositiveRecurrent.of_parallelComp_left [MeasurableSingletonClass α]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsPositiveRecurrent z) :
    κ.IsPositiveRecurrent z.1 :=
  (isPositiveRecurrent_iff _ _).mpr
    ((meanReturnTime_le_parallelComp_left κ η z).trans_lt hz.meanReturnTime_lt_top)

/-- Positive recurrence of `z` under `κ ∥ₖ η` implies positive recurrence of `z.2` under `η`. -/
theorem IsPositiveRecurrent.of_parallelComp_right [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsPositiveRecurrent z) :
    η.IsPositiveRecurrent z.2 :=
  (isPositiveRecurrent_iff _ _).mpr
    ((meanReturnTime_le_parallelComp_right κ η z).trans_lt hz.meanReturnTime_lt_top)

/-- **Unconditional upper bound on the product cycle occupation measure.** For any Markov kernels
`κ` and `η` with measurable singletons and any state `z`, `(κ.cycleOccupation z.1).prod
(η.cycleOccupation z.2)` is `(κ ∥ₖ η)`-superharmonic with unit mass at `{z}`, and therefore
dominates `(κ ∥ₖ η).cycleOccupation z`. Neither irreducibility nor recurrence is required. -/
theorem cycleOccupation_parallelComp_le [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    (κ ∥ₖ η).cycleOccupation z ≤ (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2) := by
  have hsub : (κ ∥ₖ η) ∘ₘ ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) ≤
      (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2) := by
    rw [Measure.parallelComp_comp_prod]
    exact Measure.prod_mono (κ.comp_cycleOccupation_le z.1) (η.comp_cycleOccupation_le z.2)
  have hz : ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) {z} = 1 := by
    rw [← Prod.eta z, ← Set.singleton_prod_singleton, Measure.prod_prod,
      cycleOccupation_singleton_self, cycleOccupation_singleton_self, one_mul]
  simpa [hz] using smul_cycleOccupation_le_of_comp_le hsub z

/-- **Unconditional upper bound on the product mean return time.** For any Markov kernels `κ` and
`η` with measurable singletons and any state `z`,
`(κ ∥ₖ η).meanReturnTime z ≤ κ.meanReturnTime z.1 * η.meanReturnTime z.2`. -/
theorem meanReturnTime_parallelComp_le [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    (κ ∥ₖ η).meanReturnTime z ≤ κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
  calc (κ ∥ₖ η).meanReturnTime z
    _ = (κ ∥ₖ η).cycleOccupation z Set.univ := (cycleOccupation_univ _ _).symm
    _ ≤ ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) Set.univ :=
      (cycleOccupation_parallelComp_le κ η z) Set.univ
    _ = κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
      rw [← Set.univ_prod_univ, Measure.prod_prod, cycleOccupation_univ, cycleOccupation_univ]

/-- The pair `(x, y)` is positive recurrent under `κ ∥ₖ η` whenever `x` is positive recurrent
under `κ` and `y` is positive recurrent under `η`, with no irreducibility, aperiodicity, or
countability assumption. -/
theorem IsPositiveRecurrent.parallelComp [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {x : α} {y : β} (hx : κ.IsPositiveRecurrent x) (hy : η.IsPositiveRecurrent y) :
    (κ ∥ₖ η).IsPositiveRecurrent (x, y) :=
  (isPositiveRecurrent_iff _ _).mpr <|
    (meanReturnTime_parallelComp_le κ η (x, y)).trans_lt
      (ENNReal.mul_lt_top hx.meanReturnTime_lt_top hy.meanReturnTime_lt_top)

/-- **Characterization of positive recurrence in an independent product chain.** A pair `z` is
positive recurrent under `κ ∥ₖ η` if and only if both coordinates are positive recurrent under
their respective kernels. Neither irreducibility, aperiodicity, nor countability is needed. -/
@[simp]
theorem isPositiveRecurrent_parallelComp_iff
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    (κ ∥ₖ η).IsPositiveRecurrent z ↔ κ.IsPositiveRecurrent z.1 ∧ η.IsPositiveRecurrent z.2 :=
  ⟨fun hz => ⟨hz.of_parallelComp_left, hz.of_parallelComp_right⟩,
    fun ⟨hx, hy⟩ => hx.parallelComp hy⟩

end CoordinateBounds

/-! ### Reachability, irreducibility, and one-sided aperiodicity -/

section Irreducibility

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Reachability under `κ ∥ₖ η` projects to reachability in the first coordinate. -/
theorem Reaches.of_parallelComp_left {κ : Kernel α α} {η : Kernel β β}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {x y : α × β} (h : (κ ∥ₖ η).Reaches x y) :
    κ.Reaches x.1 y.1 := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp h
  rw [parallelComp_pow_apply_singleton, ENNReal.mul_pos_iff] at hn
  exact (reaches_def x.1 y.1).mpr ⟨n, hn.1⟩

/-- Reachability under `κ ∥ₖ η` projects to reachability in the second coordinate. -/
theorem Reaches.of_parallelComp_right {κ : Kernel α α} {η : Kernel β β}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {x y : α × β} (h : (κ ∥ₖ η).Reaches x y) :
    η.Reaches x.2 y.2 := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp h
  rw [parallelComp_pow_apply_singleton, ENNReal.mul_pos_iff] at hn
  exact (reaches_def x.2 y.2).mpr ⟨n, hn.2⟩

/-- If `κ ∥ₖ η` is irreducible with respect to counting measure and `β` is nonempty, then `κ` is
irreducible with respect to counting measure. -/
theorem isIrreducible_of_parallelComp_left (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [Nonempty β] [IsIrreducible Measure.count (κ ∥ₖ η)] :
    IsIrreducible Measure.count κ := by
  obtain ⟨b⟩ := ‹Nonempty β›
  exact isIrreducible_count_iff_forall_reaches.mpr fun x₁ x₂ =>
    ((isIrreducible_count_iff_forall_reaches.mp ‹_›) (x₁, b) (x₂, b)).of_parallelComp_left

/-- If `κ ∥ₖ η` is irreducible with respect to counting measure and `α` is nonempty, then `η` is
irreducible with respect to counting measure. -/
theorem isIrreducible_of_parallelComp_right (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [Nonempty α] [IsIrreducible Measure.count (κ ∥ₖ η)] :
    IsIrreducible Measure.count η := by
  obtain ⟨a⟩ := ‹Nonempty α›
  exact isIrreducible_count_iff_forall_reaches.mpr fun y₁ y₂ =>
    ((isIrreducible_count_iff_forall_reaches.mp ‹_›) (a, y₁) (a, y₂)).of_parallelComp_right

/-- In a counting-measure-irreducible Markov kernel, every state reaches every other state at
arbitrarily large times (`∃ᶠ n in atTop, 0 < (κ ^ n) x {y}`), without aperiodicity or measurable
singletons. -/
theorem frequently_pos_pow_apply_singleton (κ : Kernel α α) [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] (x y : α) :
    ∃ᶠ n in atTop, 0 < (κ ^ n) x {y} := by
  rw [frequently_atTop]
  intro N
  obtain ⟨B, hyB, hBm, hBeq⟩ :=
    exists_measurable_superset_forall_eq (fun m : ℕ => (κ ^ m) x) {y}
  have huniv : (⋃ k : ℕ, {u : α | (κ ^ k) u B ≠ 0}) = Set.univ := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := exists_pos_pow_apply_singleton (κ := κ) u y
    exact ⟨k, (hk.trans_le (measure_mono (Set.singleton_subset_iff.mpr (hyB rfl)))).ne'⟩
  have hnotall : ¬ ∀ k : ℕ, (κ ^ N) x {u : α | (κ ^ k) u B ≠ 0} = 0 := by
    intro hall
    have hzero : (κ ^ N) x Set.univ = 0 := by
      rw [← huniv]
      exact measure_iUnion_null hall
    simp at hzero
  push Not at hnotall
  obtain ⟨k, hk⟩ := hnotall
  have hint : ∫⁻ u, (κ ^ k) u B ∂(κ ^ N) x ≠ 0 := by
    rw [ne_eq, lintegral_eq_zero_iff ((κ ^ k).measurable_coe hBm)]
    exact fun hae => hk (ae_iff.mp hae)
  have hpos : 0 < (κ ^ (k + N)) x {y} := by
    rw [← hBeq (k + N), Kernel.pow_add, comp_apply, Measure.bind_apply hBm (κ ^ k).aemeasurable]
    exact pos_iff_ne_zero.mpr hint
  exact ⟨k + N, Nat.le_add_left N k, hpos⟩

/-- **One-sided aperiodicity suffices for product irreducibility (left factor).** If `κ` and `η`
are counting-measure irreducible, `κ` is aperiodic, and `η` is Markov, then `κ ∥ₖ η` is
counting-measure irreducible even when `η` is periodic. -/
theorem IsAperiodic.isIrreducible_parallelComp_left
    {κ : Kernel α α} {η : Kernel β β} [IsSFiniteKernel κ] [IsMarkovKernel η]
    [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]
    (hκ : κ.IsAperiodic) :
    IsIrreducible Measure.count (κ ∥ₖ η) := by
  refine isIrreducible_count_iff_forall_reaches.mpr fun x y => ?_
  have hfreq : ∃ᶠ n in atTop, 0 < ((κ ∥ₖ η) ^ n) x {y} := by
    refine ((frequently_pos_pow_apply_singleton η x.2 y.2).and_eventually
      (hκ.eventually_pos_pow_apply_singleton x.1 y.1)).mono fun n ⟨h₂, h₁⟩ => ?_
    rw [parallelComp_pow_apply_singleton]
    exact ENNReal.mul_pos_iff.mpr ⟨h₁, h₂⟩
  exact (reaches_def x y).mpr hfreq.exists

/-- **One-sided aperiodicity suffices for product irreducibility (right factor).** If `κ` and `η`
are counting-measure irreducible, `κ` is Markov, and `η` is aperiodic, then `κ ∥ₖ η` is
counting-measure irreducible even when `κ` is periodic. -/
theorem IsAperiodic.isIrreducible_parallelComp_right
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsSFiniteKernel η]
    [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]
    (hη : η.IsAperiodic) :
    IsIrreducible Measure.count (κ ∥ₖ η) := by
  refine isIrreducible_count_iff_forall_reaches.mpr fun x y => ?_
  have hfreq : ∃ᶠ n in atTop, 0 < ((κ ∥ₖ η) ^ n) x {y} := by
    refine ((frequently_pos_pow_apply_singleton κ x.1 y.1).and_eventually
      (hη.eventually_pos_pow_apply_singleton x.2 y.2)).mono fun n ⟨h₁, h₂⟩ => ?_
    rw [parallelComp_pow_apply_singleton]
    exact ENNReal.mul_pos_iff.mpr ⟨h₁, h₂⟩
  exact (reaches_def x y).mpr hfreq.exists

end Irreducibility

/-! ### Exact factorization on irreducible product chains -/

section IrreducibleProduct

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]

/-- **Automatic independence of coordinates under equilibrium.** When `κ ∥ₖ η` is irreducible with
respect to counting measure, every `(κ ∥ₖ η)`-invariant probability measure `ρ` equals the product
`ρ.fst.prod ρ.snd` of its marginals. -/
theorem Invariant.eq_fst_prod_snd_of_parallelComp
    [IsIrreducible Measure.count (κ ∥ₖ η)]
    {ρ : Measure (α × β)} [IsProbabilityMeasure ρ] (hρ : (κ ∥ₖ η).Invariant ρ) :
    ρ = ρ.fst.prod ρ.snd :=
  invariant_eq_of_isProbabilityMeasure hρ
    (hρ.fst_of_parallelComp.parallelComp hρ.snd_of_parallelComp)

/-- On a counting-measure-irreducible product chain, any `(κ ∥ₖ η)`-invariant probability measure
equals `π₁.prod π₂` for any invariant probability measures `π₁` of `κ` and `π₂` of `η`. -/
theorem Invariant.eq_prod_of_parallelComp
    [IsIrreducible Measure.count (κ ∥ₖ η)]
    {ρ : Measure (α × β)} {π₁ : Measure α} {π₂ : Measure β}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (hρ : (κ ∥ₖ η).Invariant ρ) (hπ₁ : κ.Invariant π₁) (hπ₂ : η.Invariant π₂) :
    ρ = π₁.prod π₂ :=
  invariant_eq_of_isProbabilityMeasure hρ (hπ₁.parallelComp hπ₂)

/-- **Cycle occupation factorization.** When `κ ∥ₖ η` is irreducible with respect to counting
measure and `z` is recurrent under `κ ∥ₖ η` (including the null-recurrent case), the cycle
occupation measure at `z` is the product of the coordinate cycle occupation measures. -/
theorem IsRecurrent.cycleOccupation_parallelComp
    [IsIrreducible Measure.count (κ ∥ₖ η)]
    {z : α × β} (hz : (κ ∥ₖ η).IsRecurrent z) :
    (κ ∥ₖ η).cycleOccupation z = (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2) := by
  have hinv : (κ ∥ₖ η).Invariant ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) :=
    hz.of_parallelComp_left.invariant_cycleOccupation.parallelComp
      hz.of_parallelComp_right.invariant_cycleOccupation
  have hmass : ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) {z} = 1 := by
    rw [← Prod.eta z, ← Set.singleton_prod_singleton, Measure.prod_prod,
      cycleOccupation_singleton_self, cycleOccupation_singleton_self, one_mul]
  simpa [hmass] using (hinv.eq_smul_cycleOccupation hz (by simp [hmass])).symm

/-- When `κ ∥ₖ η` is irreducible and `x`, `y` are positive recurrent for `κ`, `η`, the cycle
occupation measure of `κ ∥ₖ η` at `(x, y)` is `(κ.cycleOccupation x).prod (η.cycleOccupation y)`. -/
theorem IsPositiveRecurrent.cycleOccupation_parallelComp
    [IsIrreducible Measure.count (κ ∥ₖ η)]
    {x : α} {y : β} (hx : κ.IsPositiveRecurrent x) (hy : η.IsPositiveRecurrent y) :
    (κ ∥ₖ η).cycleOccupation (x, y) = (κ.cycleOccupation x).prod (η.cycleOccupation y) :=
  (hx.parallelComp hy).isRecurrent.cycleOccupation_parallelComp

/-- **Product formula for mean return times.** When `κ ∥ₖ η` is irreducible with respect to
counting measure, `(κ ∥ₖ η).meanReturnTime z = κ.meanReturnTime z.1 * η.meanReturnTime z.2` for
every state `z` (positive recurrent, null recurrent, or transient). -/
@[simp]
theorem meanReturnTime_parallelComp (κ : Kernel α α) (η : Kernel β β)
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsIrreducible Measure.count (κ ∥ₖ η)]
    (z : α × β) :
    (κ ∥ₖ η).meanReturnTime z = κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
  by_cases hz : (κ ∥ₖ η).IsRecurrent z
  · have huniv := congrArg (fun μ : Measure (α × β) => μ Set.univ) hz.cycleOccupation_parallelComp
    rwa [cycleOccupation_univ, ← Set.univ_prod_univ, Measure.prod_prod,
      cycleOccupation_univ, cycleOccupation_univ] at huniv
  · refine le_antisymm (meanReturnTime_parallelComp_le κ η z) ?_
    rw [(isTransient_iff.mpr hz).meanReturnTime_eq_top]
    exact le_top

/-- When `κ` and `η` are counting-measure irreducible and `κ` is aperiodic, the mean return time of
`z` under `κ ∥ₖ η` factors as `κ.meanReturnTime z.1 * η.meanReturnTime z.2`. -/
theorem IsAperiodic.meanReturnTime_parallelComp_left
    [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]
    (hκ : κ.IsAperiodic) (z : α × β) :
    (κ ∥ₖ η).meanReturnTime z = κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
  let := hκ.isIrreducible_parallelComp_left (η := η)
  exact meanReturnTime_parallelComp κ η z

/-- When `κ` and `η` are counting-measure irreducible and `η` is aperiodic, the mean return time of
`z` under `κ ∥ₖ η` factors as `κ.meanReturnTime z.1 * η.meanReturnTime z.2`. -/
theorem IsAperiodic.meanReturnTime_parallelComp_right
    [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]
    (hη : η.IsAperiodic) (z : α × β) :
    (κ ∥ₖ η).meanReturnTime z = κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
  let := hη.isIrreducible_parallelComp_right (κ := κ)
  exact meanReturnTime_parallelComp κ η z

/-- When `κ ∥ₖ η` is irreducible and `x`, `y` are positive recurrent for `κ`, `η`, the normalized
cycle occupation probability measure of `κ ∥ₖ η` around `(x, y)` is the product of the normalized
coordinate cycle occupation probability measures. -/
theorem IsPositiveRecurrent.inv_meanReturnTime_smul_cycleOccupation_parallelComp
    [IsIrreducible Measure.count (κ ∥ₖ η)]
    {x : α} {y : β} (hx : κ.IsPositiveRecurrent x) (hy : η.IsPositiveRecurrent y) :
    ((κ ∥ₖ η).meanReturnTime (x, y))⁻¹ • (κ ∥ₖ η).cycleOccupation (x, y) =
      ((κ.meanReturnTime x)⁻¹ • κ.cycleOccupation x).prod
        ((η.meanReturnTime y)⁻¹ • η.cycleOccupation y) := by
  have hxy : (κ ∥ₖ η).IsPositiveRecurrent (x, y) := hx.parallelComp hy
  have := hxy.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  have := hx.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  have := hy.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  exact hxy.invariant_inv_meanReturnTime_smul_cycleOccupation.eq_prod_of_parallelComp
    hx.invariant_inv_meanReturnTime_smul_cycleOccupation
    hy.invariant_inv_meanReturnTime_smul_cycleOccupation

end IrreducibleProduct

/-! ### Total-variation convergence of irreducible aperiodic product chains -/

section EquilibriumConvergence

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
  [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]

/-- **Joint convergence to product equilibrium.** For irreducible aperiodic Markov kernels `κ` and
`η` with invariant probability measures `π₁` and `π₂`, the time-`n` distribution of `κ ∥ₖ η`
started from any joint initial probability measure `ρ` (not necessarily a product measure)
converges in total variation to `π₁.prod π₂`. -/
theorem Invariant.tendsto_tvDist_parallelComp_pow_comp
    {π₁ : Measure α} {π₂ : Measure β} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (hπ₁ : κ.Invariant π₁) (hπ₂ : η.Invariant π₂)
    (hκ : κ.IsAperiodic) (hη : η.IsAperiodic)
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] :
    Tendsto (fun n : ℕ => tvDist (((κ ∥ₖ η) ^ n) ∘ₘ ρ) (π₁.prod π₂)) atTop (𝓝 0) := by
  let := hκ.isIrreducible_parallelComp hη
  exact (hπ₁.parallelComp hπ₂).tendsto_tvDist_pow_comp (hκ.parallelComp hη) ρ

/-- **Joint convergence to normalized product cycle occupation.** For irreducible aperiodic Markov
kernels `κ` and `η` with positive recurrent states `x` and `y`, the time-`n` distribution of
`κ ∥ₖ η` from any initial probability measure `ρ` converges in total variation to the product of
the normalized coordinate cycle occupation measures. -/
theorem IsPositiveRecurrent.tendsto_tvDist_parallelComp_pow_comp
    {x : α} {y : β} (hx : κ.IsPositiveRecurrent x) (hy : η.IsPositiveRecurrent y)
    (hκ : κ.IsAperiodic) (hη : η.IsAperiodic)
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] :
    Tendsto (fun n : ℕ =>
      tvDist (((κ ∥ₖ η) ^ n) ∘ₘ ρ)
        (((κ.meanReturnTime x)⁻¹ • κ.cycleOccupation x).prod
          ((η.meanReturnTime y)⁻¹ • η.cycleOccupation y))) atTop (𝓝 0) := by
  have := hx.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  have := hy.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  exact hx.invariant_inv_meanReturnTime_smul_cycleOccupation.tendsto_tvDist_parallelComp_pow_comp
    hy.invariant_inv_meanReturnTime_smul_cycleOccupation hκ hη ρ

end EquilibriumConvergence

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {P : Measure Ω} {X : ℕ → Ω → α} {Y : ℕ → Ω → β}
  {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
  [Kernel.IsIrreducible Measure.count κ] [Kernel.IsIrreducible Measure.count η]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The joint time-`n` law of two independent realizations of irreducible aperiodic Markov chains
on an arbitrary measurable sample space converges in total variation to the product of their
invariant probabilities. Countability of the state spaces is deduced automatically from
irreducibility. -/
theorem tendsto_tvDist_prodMk_of_invariant
    {π₁ : Measure α} {π₂ : Measure β} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw μ κ) P)
    (hY : HasLaw (fun ω n => Y n ω) (markovChainLaw ν η) P)
    (hindep : IndepFun (fun ω n => X n ω) (fun ω n => Y n ω) P)
    (hπ₁ : κ.Invariant π₁) (hπ₂ : η.Invariant π₂)
    (hκ : κ.IsAperiodic) (hη : η.IsAperiodic) :
    Tendsto (fun n : ℕ => tvDist (P.map fun ω => (X n ω, Y n ω)) (π₁.prod π₂)) atTop (𝓝 0) := by
  have := Kernel.countable_of_isIrreducible_count (κ := κ)
  have := Kernel.countable_of_isIrreducible_count (κ := η)
  let := hκ.isIrreducible_parallelComp hη
  exact (hX.prodMk_markovChainLaw hY hindep).tendsto_tvDist_map_of_invariant
    (hπ₁.parallelComp hπ₂) (hκ.parallelComp hη)

/-- Return-mean form of joint total-variation convergence for independent realizations of
irreducible aperiodic positive recurrent Markov chains on an arbitrary measurable sample space. -/
theorem tendsto_tvDist_prodMk_of_isPositiveRecurrent
    {x : α} {y : β}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw μ κ) P)
    (hY : HasLaw (fun ω n => Y n ω) (markovChainLaw ν η) P)
    (hindep : IndepFun (fun ω n => X n ω) (fun ω n => Y n ω) P)
    (hx : κ.IsPositiveRecurrent x) (hy : η.IsPositiveRecurrent y)
    (hκ : κ.IsAperiodic) (hη : η.IsAperiodic) :
    Tendsto (fun n : ℕ =>
      tvDist (P.map fun ω => (X n ω, Y n ω))
        (((κ.meanReturnTime x)⁻¹ • κ.cycleOccupation x).prod
          ((η.meanReturnTime y)⁻¹ • η.cycleOccupation y))) atTop (𝓝 0) := by
  have := hx.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  have := hy.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  exact hX.tendsto_tvDist_prodMk_of_invariant hY hindep
    hx.invariant_inv_meanReturnTime_smul_cycleOccupation
    hy.invariant_inv_meanReturnTime_smul_cycleOccupation hκ hη

end ProbabilityTheory.HasLaw

/-! ### Deterministic parallel products and sharpness of irreducibility -/

namespace ProbabilityTheory.Kernel

section DeterministicSharpness

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

open scoped Classical in
/-- Under `deterministic f hf ∥ₖ deterministic g hg`, the mean return time of `z` is the least
common multiple of `Function.minimalPeriod f z.1` and `Function.minimalPeriod g z.2` when both
coordinates are periodic, and `∞` otherwise. Whenever the two minimal periods share a nontrivial
common divisor, this is strictly smaller than the product of the coordinate mean return times. -/
@[simp]
theorem meanReturnTime_deterministic_parallelComp_deterministic
    {f : α → α} {g : β → β} (hf : Measurable f) (hg : Measurable g) (z : α × β) :
    (deterministic f hf ∥ₖ deterministic g hg).meanReturnTime z =
      if z.1 ∈ Function.periodicPts f ∧ z.2 ∈ Function.periodicPts g then
        ((Function.minimalPeriod f z.1).lcm (Function.minimalPeriod g z.2) : ℝ≥0∞)
      else ∞ := by
  have hmem : z ∈ Function.periodicPts (Prod.map f g) ↔
      z.1 ∈ Function.periodicPts f ∧ z.2 ∈ Function.periodicPts g := by
    rw [← isPositiveRecurrent_deterministic (hf.prodMap hg),
      ← isPositiveRecurrent_congr (deterministic_parallelComp_deterministic hf hg) z,
      isPositiveRecurrent_parallelComp_iff, isPositiveRecurrent_deterministic,
      isPositiveRecurrent_deterministic]
  rw [meanReturnTime_congr (deterministic_parallelComp_deterministic hf hg),
    meanReturnTime_deterministic, Function.minimalPeriod_prodMap]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact False.elim (h₂ (hmem.mp h₁))
  · exact False.elim (h₁ (hmem.mpr h₂))
  · rfl

/-- The deterministic flip kernel `deterministic (! ·)` on `Bool` is irreducible with respect to
counting measure. -/
theorem isIrreducible_deterministic_not :
    IsIrreducible Measure.count (deterministic (! ·) (measurable_of_countable _)) := by
  refine isIrreducible_count_iff_forall_reaches.mpr fun x y => ?_
  by_cases hxy : x = y
  · subst hxy
    exact Reaches.refl x
  · refine (reaches_def x y).mpr ⟨1, ?_⟩
    have hnot : (!x) = y := by cases x <;> cases y <;> simp_all
    simp [pow_one, deterministic_apply, hnot]

/-- **Irreducibility is not preserved by parallel products.** Although `deterministic (! ·)` on
`Bool` is counting-measure irreducible, its parallel square is not: `(false, false)` only ever
visits `(false, false)` and `(true, true)`, never `(false, true)`. -/
theorem not_isIrreducible_parallelComp_deterministic_not :
    ¬ IsIrreducible Measure.count
      (deterministic (! ·) (measurable_of_countable _) ∥ₖ
        deterministic (! ·) (measurable_of_countable _)) := by
  intro hirr
  have hreach := (isIrreducible_count_iff_forall_reaches.mp hirr) (false, false) (false, true)
  obtain ⟨n, hn⟩ := (reaches_def (false, false) (false, true)).mp hreach
  rw [parallelComp_pow_apply_singleton, deterministic_pow] at hn
  cases hb : (! ·)^[n] false <;> simp [deterministic_apply, hb] at hn

/-- **Sharpness of irreducibility in `meanReturnTime_parallelComp`.** For the irreducible
positive recurrent flip kernel on `Bool`, the parallel square has mean return time `2` at
`(false, false)`, strictly less than the product `2 * 2 = 4` of the coordinate mean return times. -/
theorem meanReturnTime_parallelComp_deterministic_not_lt :
    (deterministic (! ·) (measurable_of_countable _) ∥ₖ
        deterministic (! ·) (measurable_of_countable _)).meanReturnTime (false, false) <
      (deterministic (! ·) (measurable_of_countable _)).meanReturnTime false *
        (deterministic (! ·) (measurable_of_countable _)).meanReturnTime false := by
  have hper : false ∈ Function.periodicPts (! ·) :=
    ⟨2, by decide, by decide⟩
  have hmin : Function.minimalPeriod (! ·) false = 2 := by
    refine (Function.IsPeriodicPt.minimalPeriod_le (by decide : 0 < 2) (by decide)).antisymm ?_
    by_contra! hlt
    interval_cases h : Function.minimalPeriod (! ·) false
    · exact (Function.minimalPeriod_pos_of_mem_periodicPts hper).ne' h
    · have hfix := Function.minimalPeriod_eq_one_iff_isFixedPt.mp h
      exact Bool.false_ne_true hfix.symm
  rw [meanReturnTime_deterministic_parallelComp_deterministic, meanReturnTime_deterministic]
  simp [hper, hmin]
  norm_num

/-- **Sharpness of irreducibility in `Invariant.eq_fst_prod_snd_of_parallelComp`.** Although each
factor `deterministic (! ·)` on `Bool` is irreducible and positive recurrent, its reducible
parallel square admits a correlated diagonal invariant probability measure not equal to the product
of its marginals. -/
theorem exists_invariant_probability_parallelComp_deterministic_not_ne_prod :
    ∃ ρ : Measure (Bool × Bool),
      IsProbabilityMeasure ρ ∧
        (deterministic (! ·) (measurable_of_countable _) ∥ₖ
            deterministic (! ·) (measurable_of_countable _)).Invariant ρ ∧
          ρ ≠ ρ.fst.prod ρ.snd := by
  let ρ : Measure (Bool × Bool) :=
    (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (false, false) + Measure.dirac (true, true))
  have hprob : IsProbabilityMeasure ρ := ⟨by
    simp only [ρ, smul_apply, add_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul]
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩
  refine ⟨ρ, hprob, ?_, ?_⟩
  · rw [Invariant, deterministic_parallelComp_deterministic, Measure.deterministic_comp_eq_map]
    have hm : Measurable (Prod.map (! ·) (! ·)) := measurable_of_countable _
    rw [show ρ = _ from rfl, Measure.map_smul _ hm.aemeasurable, Measure.map_add _ _ hm,
      Measure.map_dirac' hm, Measure.map_dirac' hm]
    simp [ρ, Prod.map, add_comm]
  · intro heq
    have hft := congrArg (fun μ : Measure (Bool × Bool) => μ {(false, true)}) heq
    have hlhs : ρ {(false, true)} = 0 := by
      simp [ρ]
    have hfst : ρ.fst {false} = (2 : ℝ≥0∞)⁻¹ := by
      rw [Measure.fst, show ρ = _ from rfl, Measure.map_smul _ measurable_fst.aemeasurable,
        Measure.map_add _ _ measurable_fst, Measure.map_dirac' measurable_fst,
        Measure.map_dirac' measurable_fst]
      simp
    have hsnd : ρ.snd {true} = (2 : ℝ≥0∞)⁻¹ := by
      rw [Measure.snd, show ρ = _ from rfl, Measure.map_smul _ measurable_snd.aemeasurable,
        Measure.map_add _ _ measurable_snd, Measure.map_dirac' measurable_snd,
        Measure.map_dirac' measurable_snd]
      simp
    rw [hlhs, ← Set.singleton_prod_singleton, Measure.prod_prod, hfst, hsnd] at hft
    have hne : ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) ≠ 0 :=
      mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
    exact hne hft.symm

end DeterministicSharpness

end ProbabilityTheory.Kernel
