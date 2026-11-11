/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Coupling.Basic
public import TauCeti.Probability.MarkovChain.Recurrence

/-!
# Asymptotic coupling of recurrent product chains

An almost-surely finite meeting makes the total variation distance between the two
marginal laws tend to zero. This applies to any Markovian coupling, not only independent
copies. For an irreducible independent square chain, a single recurrent state ensures
almost-sure meeting from every initial measure: the product chain hits a fixed diagonal
state almost surely.

Consequently such a square chain makes the original chain forget its initial probability
law in total variation. In particular, its laws at times `n` and `n + i` become
asymptotically indistinguishable for each fixed `i`. No invariant probability or finite
return-time mean is assumed; forgetting the initial law does not assert existence of a
limiting probability measure.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8,
  the meeting-time coupling argument for convergence to equilibrium.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti TauCeti.Probability
open scoped Topology

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

/-- An almost-surely finite meeting in a Markovian coupling makes the marginal laws
asymptotically equal in total variation. Finite initial measures suffice. -/
theorem tendsto_tvDist_pow_comp_of_ae_meeting [MeasurableEq α]
    (κ : Kernel α α) [IsMarkovKernel κ]
    {η : Kernel (α × α) (α × α)} [IsMarkovKernel η]
    (hη : ∀ p, IsCoupling (η p) (κ p.1) (κ p.2))
    {ρ : Measure (α × α)} [IsFiniteMeasure ρ] {ν ν' : Measure α}
    (hρ : IsCoupling ρ ν ν')
    (hmeet : ∀ᵐ ω ∂markovChainLaw ρ η, ∃ k, (ω k).1 = (ω k).2) :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n : Kernel α α) ∘ₘ ν)
      ((κ ^ n : Kernel α α) ∘ₘ ν')) atTop (𝓝 0) := by
  let P := markovChainLaw ρ η
  let A (n : ℕ) := {ω : ℕ → α × α | ∀ k ≤ n, (ω k).1 ≠ (ω k).2}
  have hA (n : ℕ) : MeasurableSet (A n) := by
    have h := Filtration.le (Filtration.piLE (X := fun _ : ℕ => α × α)) n _
      (measurableSet_piLE_exists_le_fst_eq_snd n)
    simpa only [Set.compl_ofPred, not_exists, not_and] using h.compl
  have hanti : Antitone A := fun _ _ hmn _ hω k hk => hω k (hk.trans hmn)
  have hzero : P (⋂ n, A n) = 0 := by
    apply measure_mono_null (t := {ω | ¬ ∃ k, (ω k).1 = (ω k).2}) _ (ae_iff.mp hmeet)
    intro ω hω ⟨k, hk⟩
    exact Set.mem_iInter.mp hω k k le_rfl hk
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hzero] using
      tendsto_measure_iInter_atTop (μ := P) (fun n => (hA n).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
  have hreal : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  exact squeeze_zero (fun _ => tvDist_nonneg)
    (fun n => κ.tvDist_pow_comp_le_of_isCoupling hη hρ n) (by
      simpa using hreal.const_mul 2)

/-- An irreducible chain on pairs with a recurrent state meets the diagonal almost
surely, from every initial measure. Independence of the coordinates is not required,
and the coordinates may already agree at time zero. -/
theorem ae_meeting_of_isRecurrent [MeasurableSingletonClass α]
    (η : Kernel (α × α) (α × α)) [IsMarkovKernel η]
    [IsIrreducible Measure.count η]
    {z : α × α} (hz : η.IsRecurrent z) (ρ : Measure (α × α)) :
    ∀ᵐ ω ∂markovChainLaw ρ η, ∃ k, (ω k).1 = (ω k).2 := by
  filter_upwards [hz.ae_hittingAfter_ne_top_of_isIrreducible ρ (z.1, z.1)] with ω hω
  by_contra h
  apply hω
  apply hittingAfter_eq_top_iff.mpr
  intro n _ hn
  have hn' : ω n = (z.1, z.1) := Set.mem_singleton_iff.mp hn
  exact h ⟨n, by simp [hn']⟩

/-- If the independent square chain is irreducible and recurrent, any two initial
probability laws become asymptotically indistinguishable in total variation. -/
theorem tendsto_tvDist_pow_comp_of_parallelComp_isRecurrent [MeasurableEq α]
    (κ : Kernel α α) [IsMarkovKernel κ]
    [IsIrreducible Measure.count (κ ∥ₖ κ)]
    {z : α × α} (hz : (κ ∥ₖ κ).IsRecurrent z)
    (ν ν' : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n : Kernel α α) ∘ₘ ν)
      ((κ ^ n : Kernel α α) ∘ₘ ν')) atTop (𝓝 0) := by
  apply κ.tendsto_tvDist_pow_comp_of_ae_meeting
    (η := κ ∥ₖ κ) (ρ := ν.prod ν')
    (fun p => by rw [parallelComp_apply]; exact isCoupling_prod _ _) (isCoupling_prod ν ν')
  exact (κ ∥ₖ κ).ae_meeting_of_isRecurrent hz _

/-- Under recurrence and irreducibility of the square chain, a fixed time shift does
not change the asymptotic marginal law, in total variation. -/
theorem tendsto_tvDist_pow_comp_pow_add_comp_of_parallelComp_isRecurrent [MeasurableEq α]
    (κ : Kernel α α) [IsMarkovKernel κ]
    [IsIrreducible Measure.count (κ ∥ₖ κ)]
    {z : α × α} (hz : (κ ∥ₖ κ).IsRecurrent z)
    (ν : Measure α) [IsProbabilityMeasure ν] (i : ℕ) :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n : Kernel α α) ∘ₘ ν)
      ((κ ^ (n + i) : Kernel α α) ∘ₘ ν))
      atTop (𝓝 0) := by
  simpa only [Kernel.pow_add, Measure.comp_assoc] using
    κ.tendsto_tvDist_pow_comp_of_parallelComp_isRecurrent hz ν ((κ ^ i : Kernel α α) ∘ₘ ν)

end ProbabilityTheory.Kernel
