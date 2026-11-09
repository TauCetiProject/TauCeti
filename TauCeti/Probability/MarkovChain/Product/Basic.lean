/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Period
public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.Kernel.Composition.ParallelComp
public import TauCeti.Probability.Process.MarkovChain

/-!
# Independent product chains

The independent product of two chains uses Mathlib's parallel composition `κ ∥ₖ η`.
Its path law is obtained by pairing independent coordinate paths. On spaces with measurable
singletons, products of aperiodic kernels are aperiodic; if both factors are also irreducible,
the product is irreducible. The key point is that aperiodicity synchronizes the positive
transition times of the two coordinates. Irreducibility alone does not do so (two deterministic
two-cycles give a reducible product).

Together with `Kernel.Invariant.parallelComp`, these results provide the independent product
chain used in meeting-time coupling arguments for convergence to equilibrium.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8.
-/

public section

open MeasureTheory ProbabilityTheory Filter

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {κ : Kernel α α} {η : Kernel β β} [IsSFiniteKernel κ] [IsSFiniteKernel η]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- Independent products of aperiodic kernels are aperiodic, even without irreducibility. -/
theorem IsAperiodic.parallelComp (hκ : κ.IsAperiodic) (hη : η.IsAperiodic) :
    (κ ∥ₖ η).IsAperiodic := by
  rw [isAperiodic_iff]
  intro x
  have hpos : ∀ᶠ n in atTop, 0 < ((κ ∥ₖ η) ^ n) x {x} := by
    filter_upwards [eventually_pos_pow_apply_singleton_self_of_period_eq_one
      (isAperiodic_iff.mp hκ x.1), eventually_pos_pow_apply_singleton_self_of_period_eq_one
      (isAperiodic_iff.mp hη x.2)] with n hn hm
    rw [parallelComp_pow_apply_singleton]
    exact ENNReal.mul_pos_iff.mpr ⟨hn, hm⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  have h₁ := period_dvd_of_mem_returnLengths (κ := κ ∥ₖ η)
    (mem_returnLengths.mpr ⟨Nat.succ_pos N, hN (N + 1) (by omega)⟩)
  have h₂ := period_dvd_of_mem_returnLengths (κ := κ ∥ₖ η)
    (mem_returnLengths.mpr ⟨Nat.succ_pos (N + 1), hN (N + 2) (by omega)⟩)
  exact Nat.dvd_one.mp (by simpa using Nat.dvd_sub h₂ h₁)

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- In an irreducible aperiodic product, any fixed pair of states has positive transition mass
at every sufficiently large time. -/
theorem IsAperiodic.eventually_pos_parallelComp_pow_apply_singleton
    [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]
    (hκ : κ.IsAperiodic) (hη : η.IsAperiodic) (x y : α × β) :
    ∀ᶠ n in atTop, 0 < ((κ ∥ₖ η) ^ n) x {y} := by
  filter_upwards [hκ.eventually_pos_pow_apply_singleton x.1 y.1,
    hη.eventually_pos_pow_apply_singleton x.2 y.2] with n hn hm
  rw [parallelComp_pow_apply_singleton]
  exact ENNReal.mul_pos_iff.mpr ⟨hn, hm⟩

/-- The independent product of two irreducible aperiodic kernels is irreducible with respect
to counting measure. -/
theorem IsAperiodic.isIrreducible_parallelComp
    [IsIrreducible Measure.count κ] [IsIrreducible Measure.count η]
    (hκ : κ.IsAperiodic) (hη : η.IsAperiodic) :
    IsIrreducible Measure.count (κ ∥ₖ η) := by
  apply isIrreducible_count_iff_forall_reaches.mpr
  intro x y
  exact (reaches_def x y).mpr
    (hκ.eventually_pos_parallelComp_pow_apply_singleton hη x y).exists

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The law of the independent product chain is obtained by pairing independent coordinate
paths. The identity holds for finite initial measures, not only probability laws. -/
theorem markovChainLaw_parallelComp (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    markovChainLaw (μ.prod ν) (κ ∥ₖ η) =
      ((markovChainLaw μ κ).prod (markovChainLaw ν η)).map
        (fun w n => (w.1 n, w.2 n)) := by
  let P := (markovChainLaw μ κ).prod (markovChainLaw ν η)
  have h := (hasLaw_markovChainLaw_iff_prefixLaw_singleton (μ.prod ν) (κ ∥ₖ η)
    (μ := P) (X := fun n w => (w.1 n, w.2 n)) (fun n => by fun_prop)).mpr ?_
  · exact h.map_eq.symm
  intro n w
  rw [prefixLaw_singleton_eq_measure (fun i => by fun_prop)]
  have hevent : {z : (ℕ → α) × (ℕ → β) | ∀ i : Fin (n + 1), (z.1 i, z.2 i) = w i} =
      {z | ∀ i : Fin (n + 1), z i = (w i).1} ×ˢ
        {z | ∀ i : Fin (n + 1), z i = (w i).2} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Prod.ext_iff, forall_and]
  rw [hevent, Measure.prod_prod]
  rw [← prefixLaw_singleton_eq_measure (fun i => (measurable_pi_apply i).aemeasurable),
    ← prefixLaw_singleton_eq_measure (fun i => (measurable_pi_apply i).aemeasurable),
    markovChainLaw_prefixLaw_singleton, markovChainLaw_prefixLaw_singleton]
  simp only [Kernel.parallelComp_apply]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_mul_mul_comm,
    ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Independent chains on an arbitrary sample space form a chain with the parallel transition
kernel. Independence is required for entire paths, not merely at each separate time. -/
theorem prodMk_markovChainLaw
    {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
    [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {P : Measure Ω} {μ : Measure α} {ν : Measure β}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {X : ℕ → Ω → α} {Y : ℕ → Ω → β}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw μ κ) P)
    (hY : HasLaw (fun ω n => Y n ω) (markovChainLaw ν η) P)
    (hindep : IndepFun (fun ω n => X n ω) (fun ω n => Y n ω) P) :
    HasLaw (fun ω n => (X n ω, Y n ω)) (markovChainLaw (μ.prod ν) (κ ∥ₖ η)) P := by
  have := hX.isFiniteMeasure
  have hzip : HasLaw (fun w n => (w.1 n, w.2 n))
      (markovChainLaw (μ.prod ν) (κ ∥ₖ η))
      ((markovChainLaw μ κ).prod (markovChainLaw ν η)) :=
    ⟨by fun_prop, (Measure.markovChainLaw_parallelComp μ ν κ η).symm⟩
  exact hzip.fun_comp (hindep.hasLaw_prod hX hY)

end ProbabilityTheory.HasLaw
