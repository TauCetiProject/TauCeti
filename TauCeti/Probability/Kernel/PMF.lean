/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Countable transition kernels and probability mass functions

`Kernel.ofPMF` turns a family of probability mass functions on a countable source into a
Markov kernel. Conversely, `Kernel.toPMF` reads the singleton masses of a Markov kernel with
countable target. These operations are inverse when both spaces are countable, so normalized
transition weights determine a unique Markov kernel, without introducing a separate notion of
probability vector.

Kernel composition and propagation of an initial law agree with `PMF.bind`; mapping the target
agrees with `PMF.map`. The power formula gives the usual discrete Chapman–Kolmogorov sum.

The constructions use Mathlib's `Kernel.ofFunOfCountable`, `PMF.toMeasure`, and `Measure.toPMF`.
For the transition-weight interpretation, see J. R. Norris, *Markov Chains* (1997), §1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

section OfPMF

variable [Countable α] [MeasurableSingletonClass α]

/-- The Markov kernel whose row at `a` is the probability mass function `p a`. -/
def ofPMF (p : α → PMF β) : Kernel α β :=
  ofFunOfCountable fun a => (p a).toMeasure

theorem ofPMF_apply (p : α → PMF β) (a : α) : ofPMF p a = (p a).toMeasure := (rfl)

instance (p : α → PMF β) : IsMarkovKernel (ofPMF p) :=
  ⟨fun a => by rw [ofPMF_apply]; infer_instance⟩

@[simp]
theorem ofPMF_apply_singleton [MeasurableSingletonClass β] (p : α → PMF β) (a : α)
    (b : β) : ofPMF p a {b} = p a b := by
  rw [ofPMF_apply, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- Mapping the states sampled by a kernel agrees with mapping each row PMF. -/
@[simp]
theorem map_ofPMF (p : α → PMF β) {f : β → γ} (hf : Measurable f) :
    (ofPMF p).map f = ofPMF (fun a => (p a).map f) := by
  ext a : 1
  simp only [map_apply _ hf, ofPMF_apply, PMF.toMeasure_map _ _ hf]

/-- A family of point masses gives the corresponding deterministic kernel. -/
@[simp]
theorem ofPMF_pure (f : α → β) :
    ofPMF (fun a => PMF.pure (f a)) = deterministic f (measurable_of_countable f) := by
  ext a : 1
  simp only [ofPMF_apply, PMF.toMeasure_pure, deterministic_apply]

end OfPMF

section ToPMF

variable [Countable β] [MeasurableSingletonClass β]

/-- The row PMF of a Markov kernel with countable target, given by its singleton masses. -/
def toPMF (κ : Kernel α β) [IsMarkovKernel κ] (a : α) : PMF β := (κ a).toPMF

@[simp]
theorem toPMF_apply (κ : Kernel α β) [IsMarkovKernel κ] (a : α) (b : β) :
    κ.toPMF a b = κ a {b} := (rfl)

@[simp]
theorem toPMF_toMeasure (κ : Kernel α β) [IsMarkovKernel κ] (a : α) :
    (κ.toPMF a).toMeasure = κ a := by
  exact Measure.toPMF_toMeasure _

@[simp]
theorem toPMF_ofPMF [Countable α] [MeasurableSingletonClass α] (p : α → PMF β) :
    (ofPMF p).toPMF = p := by
  funext a
  exact PMF.ext fun b => ofPMF_apply_singleton p a b

@[simp]
theorem ofPMF_toPMF [Countable α] [MeasurableSingletonClass α] (κ : Kernel α β)
    [IsMarkovKernel κ] : ofPMF κ.toPMF = κ := by
  ext a : 1
  rw [ofPMF_apply, toPMF_toMeasure]

/-- Nonnegative transition weights with row sums one determine a unique Markov kernel. -/
theorem existsUnique_isMarkovKernel_of_tsum_eq_one [Countable α]
    [MeasurableSingletonClass α] (p : α → β → ℝ≥0∞) (hp : ∀ a, ∑' b, p a b = 1) :
    ∃! κ : Kernel α β, IsMarkovKernel κ ∧ ∀ a b, κ a {b} = p a b := by
  let q : α → PMF β := fun a => ⟨p a, ENNReal.summable.hasSum_iff.mpr (hp a)⟩
  refine ⟨ofPMF q, ⟨inferInstance, fun a b => ofPMF_apply_singleton q a b⟩, ?_⟩
  intro κ hκ
  apply Kernel.ext
  intro a
  apply Measure.ext_iff_singleton.mpr
  intro b
  rw [ofPMF_apply_singleton, hκ.2]
  rfl

end ToPMF

section Composition

variable [Countable α] [MeasurableSingletonClass α]

/-- Composition of discrete transition kernels is row-wise PMF binding. -/
@[simp]
theorem ofPMF_comp_ofPMF [Countable β] [MeasurableSingletonClass β]
    (p : α → PMF β) (q : β → PMF γ) :
    ofPMF q ∘ₖ ofPMF p = ofPMF (fun a => (p a).bind q) := by
  ext a s hs
  simp only [comp_apply' _ _ _ hs, ofPMF_apply, PMF.toMeasure_bind_apply _ _ _ hs,
    lintegral_countable', PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact tsum_congr fun b => mul_comm _ _

/-- Discrete Chapman–Kolmogorov: sum over the intermediate state. -/
theorem pow_add_apply_singleton (κ : Kernel α α) (m n : ℕ) (a b : α) :
    (κ ^ (m + n)) a {b} = ∑' c, (κ ^ m) a {c} * (κ ^ n) c {b} := by
  rw [pow_add_apply_eq_lintegral _ _ _ _ (measurableSet_singleton _),
    lintegral_countable']
  exact tsum_congr fun c => mul_comm _ _

end Composition

/-- The row PMF of a composite kernel is the binding of its row PMFs. -/
theorem toPMF_comp [Countable β] [MeasurableSingletonClass β]
    [Countable γ] [MeasurableSingletonClass γ] (κ : Kernel α β)
    (η : Kernel β γ) [IsMarkovKernel κ] [IsMarkovKernel η] (a : α) :
    (η ∘ₖ κ).toPMF a = (κ.toPMF a).bind η.toPMF := by
  ext c
  simp [toPMF_apply, PMF.bind_apply, comp_apply', lintegral_countable', mul_comm]

end ProbabilityTheory.Kernel

namespace PMF

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Countable α] [MeasurableSingletonClass α]

/-- Propagating a discrete initial law through a kernel is PMF binding. -/
theorem toMeasure_bind (p : PMF α) (q : α → PMF β) :
    (p.bind q).toMeasure = Kernel.ofPMF q ∘ₘ p.toMeasure := by
  ext s hs
  simp only [Measure.bind_apply hs (Kernel.ofPMF q).aemeasurable,
    Kernel.ofPMF_apply, PMF.toMeasure_bind_apply _ _ _ hs, lintegral_countable',
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact tsum_congr fun a => mul_comm _ _

end PMF
