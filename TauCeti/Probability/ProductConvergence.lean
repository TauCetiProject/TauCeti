/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti.  Mathlib is not the destination (`ForTauCeti/README.md`);
what follows is where this material would have gone on the closed Mathlib
track — additions to `Mathlib/Probability/Kernel/Composition/`.

Extraction class: re-proved.  The mathematics is the dominated convergence
theorem applied to slice measures; no source outside Mathlib was used.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-! # Convergence in probability passes from the slices of a composition to the whole

A limit theorem is often proved *conditionally*: for each value of a parameter, the probability
of a bad event tends to zero.  The statement one wants is the unconditional one, and this file is
the reason the passage is free.

  `κ a (slice at a of S r) → 0` for `μ`-a.e. `a`   ⟹   `(μ ⊗ₘ κ) (S r) → 0`.

A bad-event probability lies in `[0, 1]`, so the constant `1` dominates the family of slice
probabilities and the dominated convergence theorem takes the parameter integral through the
limit.  No rate is involved, and in particular no *uniformity in the parameter*.  This is worth
stating precisely, because the reflex when a conditional result is in hand and an unconditional
one is wanted is to reach for a bound uniform in the parameter — which strengthens the
hypotheses of the theorem being proved, sometimes past what its source states.

The kernel form is the one a statistical model needs: the parameter is the draw of a population
member and `κ` is the law of the data *given* that member, which is not a fixed measure.  The
product form is the special case `κ = const ν`.

## Main results

* `tendsto_measure_compProd_of_ae_tendsto_measure_slice` — the passage above.
* `tendsto_measure_compProd_gt_of_ae_tendsto_measure_slice` — the same in the form convergence in
  probability is usually written, for the tail events of a sequence of functions.
* `tendsto_measure_prod_of_ae_tendsto_measure_slice`,
  `tendsto_measure_prod_gt_of_ae_tendsto_measure_slice` — the product specializations.
-/

open Filter MeasureTheory ProbabilityTheory Topology

public section

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/--
**Conditional convergence in probability is unconditional convergence in probability.**

If the conditional measure of the slice of `S r` above `a` tends to `0` for `μ`-almost every `a`,
then the measure of `S r` under the composition tends to `0`.

The proof is `Measure.compProd_apply` followed by dominated convergence with the constant bound
`1`, available because `κ` is Markov and `μ` is finite.  Nothing asks the slice measures to
vanish at a rate independent of `a`.
-/
theorem tendsto_measure_compProd_of_ae_tendsto_measure_slice
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (S : Nat → Set (α × β)) (hS : ∀ r, MeasurableSet (S r))
    (h : ∀ᵐ a ∂μ, Tendsto (fun r => κ a (Prod.mk a ⁻¹' S r)) atTop (𝓝 0)) :
    Tendsto (fun r => (μ ⊗ₘ κ) (S r)) atTop (𝓝 0) := by
  have hmeas : ∀ r, Measurable fun a => κ a (Prod.mk a ⁻¹' S r) := fun r =>
    Kernel.measurable_kernel_prodMk_left (hS r)
  have key : Tendsto (fun r => ∫⁻ a, κ a (Prod.mk a ⁻¹' S r) ∂μ) atTop
      (𝓝 (∫⁻ _ : α, (0 : ENNReal) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) hmeas ?_ ?_ h
    · intro r
      filter_upwards with a
      calc κ a (Prod.mk a ⁻¹' S r) ≤ κ a Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · simp only [lintegral_const, one_mul]
      exact measure_ne_top μ Set.univ
  rw [lintegral_zero] at key
  exact key.congr fun r => (Measure.compProd_apply (hS r)).symm

/--
**Conditional convergence in probability is unconditional convergence in probability**, written
for the tail events of a sequence of functions.

`f r` is a statistic of the parameter and the data; the hypothesis is that it converges to `0` in
probability under the conditional law for almost every parameter value, and the conclusion is
that it converges to `0` in probability under the joint law.
-/
theorem tendsto_measure_compProd_gt_of_ae_tendsto_measure_slice
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (f : Nat → α × β → Real) (hf : ∀ r, Measurable (f r)) {ε : Real}
    (h : ∀ᵐ a ∂μ, Tendsto (fun r => κ a {b | ε < |f r (a, b)|}) atTop (𝓝 0)) :
    Tendsto (fun r => (μ ⊗ₘ κ) {z | ε < |f r z|}) atTop (𝓝 0) :=
  tendsto_measure_compProd_of_ae_tendsto_measure_slice μ κ
    (fun r => {z | ε < |f r z|})
    (fun r => measurableSet_lt measurable_const (Measurable.abs (hf r))) h

/--
The product specialization of `tendsto_measure_compProd_of_ae_tendsto_measure_slice`: the data
law does not depend on the parameter.
-/
theorem tendsto_measure_prod_of_ae_tendsto_measure_slice
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (S : Nat → Set (α × β)) (hS : ∀ r, MeasurableSet (S r))
    (h : ∀ᵐ a ∂μ, Tendsto (fun r => ν (Prod.mk a ⁻¹' S r)) atTop (𝓝 0)) :
    Tendsto (fun r => (μ.prod ν) (S r)) atTop (𝓝 0) := by
  have := tendsto_measure_compProd_of_ae_tendsto_measure_slice μ (Kernel.const α ν) S hS h
  rwa [Measure.compProd_const] at this

/--
The product specialization of `tendsto_measure_compProd_gt_of_ae_tendsto_measure_slice`.
-/
theorem tendsto_measure_prod_gt_of_ae_tendsto_measure_slice
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (f : Nat → α × β → Real) (hf : ∀ r, Measurable (f r)) {ε : Real}
    (h : ∀ᵐ a ∂μ, Tendsto (fun r => ν {b | ε < |f r (a, b)|}) atTop (𝓝 0)) :
    Tendsto (fun r => (μ.prod ν) {z | ε < |f r z|}) atTop (𝓝 0) :=
  tendsto_measure_prod_of_ae_tendsto_measure_slice μ ν
    (fun r => {z | ε < |f r z|})
    (fun r => measurableSet_lt measurable_const (Measurable.abs (hf r))) h

/-! ### An independent pair of two-stage experiments is a two-stage experiment on the pair

A "draw a parameter, then draw data given the parameter" experiment is `μ ⊗ₘ κ`.  Two such
experiments run independently give the product `(μ ⊗ₘ κ) ⊗ (ν ⊗ₘ η)` on
`(parameter × data) × (parameter × data)`; regrouping the coordinates as
`(parameter × parameter) × (data × data)` turns it into a single two-stage experiment whose
first stage is the pair of parameters and whose second stage is the parallel composition of the
two data kernels.

The regrouping is exactly what is needed to apply
`tendsto_measure_compProd_gt_of_ae_tendsto_measure_slice` to a statistic of two independently
drawn population members: the conditioning variable is the *pair* of members, and the data of the
two members are conditionally independent given it.
-/

/--
**Two independent two-stage experiments, regrouped as one two-stage experiment on the pair.**

`shuffle ((a, b), (c, d)) = ((a, c), (b, d))` moves the two parameters together and the two data
values together.
-/
theorem map_shuffle_prod_compProd
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure γ) [IsProbabilityMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel γ δ) [IsMarkovKernel η] :
    ((μ ⊗ₘ κ).prod (ν ⊗ₘ η)).map
        (fun z : (α × β) × (γ × δ) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      = (μ.prod ν) ⊗ₘ (κ ∥ₖ η) := by
  have hshuffle : Measurable fun z : (α × β) × (γ × δ) => ((z.1.1, z.2.1), (z.1.2, z.2.2)) :=
    (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
      (measurable_fst.snd.prodMk measurable_snd.snd)
  refine MeasureTheory.ext_of_generate_finite
    (Set.image2 (· ×ˢ ·)
      (Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {u : Set γ | MeasurableSet u})
      (Set.image2 (· ×ˢ ·) {t : Set β | MeasurableSet t} {v : Set δ | MeasurableSet v}))
    ?_ ?_ ?_ ?_
  · exact (generateFrom_eq_prod
      generateFrom_prod generateFrom_prod
      (isCountablySpanning_measurableSet.prod
        isCountablySpanning_measurableSet)
      (isCountablySpanning_measurableSet.prod
        isCountablySpanning_measurableSet)).symm
  · exact isPiSystem_prod.prod isPiSystem_prod
  · rintro _ ⟨_, ⟨s, hs, u, hu, rfl⟩, _, ⟨t, ht, v, hv, rfl⟩, rfl⟩
    have hpre : (fun z : (α × β) × (γ × δ) => ((z.1.1, z.2.1), (z.1.2, z.2.2))) ⁻¹'
        ((s ×ˢ u) ×ˢ (t ×ˢ v)) = (s ×ˢ t) ×ˢ (u ×ˢ v) := by
      ext ⟨⟨a, b⟩, c, d⟩
      simp only [Set.mem_preimage, Set.mem_prod]
      tauto
    rw [Measure.map_apply hshuffle
        (((hs.prod hu).prod (ht.prod hv)) : MeasurableSet ((s ×ˢ u) ×ˢ (t ×ˢ v))),
      hpre, Measure.prod_prod, Measure.compProd_apply_prod hs ht,
      Measure.compProd_apply_prod hu hv, Measure.compProd_apply_prod (hs.prod hu) (ht.prod hv)]
    have hval : ∀ x : α × γ, (κ ∥ₖ η) x (t ×ˢ v) = κ x.1 t * η x.2 v := fun x =>
      Kernel.parallelComp_apply_prod t v
    calc (∫⁻ a in s, κ a t ∂μ) * ∫⁻ c in u, η c v ∂ν
        = ∫⁻ x, κ x.1 t * η x.2 v ∂((μ.restrict s).prod (ν.restrict u)) :=
          (lintegral_prod_mul (Kernel.measurable_coe κ ht).aemeasurable
            (Kernel.measurable_coe η hv).aemeasurable).symm
      _ = ∫⁻ x in s ×ˢ u, κ x.1 t * η x.2 v ∂(μ.prod ν) := by rw [Measure.prod_restrict]
      _ = ∫⁻ x in s ×ˢ u, (κ ∥ₖ η) x (t ×ˢ v) ∂(μ.prod ν) := by simp_rw [hval]
  · rw [Measure.map_apply hshuffle MeasurableSet.univ]
    simp

end TauCeti
