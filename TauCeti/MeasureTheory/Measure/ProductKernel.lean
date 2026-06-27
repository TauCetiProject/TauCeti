module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measurability of finite product probability-measure kernels

A finite product of measurable probability-measure kernels is a measurable measure-valued map.
Given `ν i : Ω → ProbabilityMeasure (α i)` measurable for each coordinate of a finite index type,
`ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` is measurable into `Measure (Π i, α i)`,
together with its `AEMeasurable` corollary and the constant-coordinate specialization
(`fun _ : Fin m => ν ω`) used by `ConditionallyIIDWith`.

This file does not introduce a new product-kernel structure; it is a home for product-kernel
measurability lemmas phrased directly over Mathlib's `ProbabilityMeasure.pi`. The proof is the
finite-product analogue of Mathlib's binary `ProbabilityMeasure.measurable_fun_prod`: measurability
of the measure-valued map is checked on the generating π-system of measurable rectangles
(`generateFrom_pi`, `isPiSystem_pi`), where `ProbabilityMeasure.pi` evaluates to a finite product of
coordinate measures (`Measure.pi_pi`).

The `AEMeasurable` lemmas here are the corollaries from **measurable** coordinate kernels; the
stronger statement from merely `∀ i, AEMeasurable (ν i) μ` is deferred to a later product-kernel
strengthening — this file supplies the measurable-input form the current `ConditionallyIIDWith` API
needs.

This advances `TauCetiRoadmap/Exchangeability`, Layer 1 (product kernels, conditional independence,
mixtures). It is motivated by the product-kernel layer of `cameronfreer/exchangeability`
(`MeasureKernels.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`) and implemented using
Mathlib's `ProbabilityMeasure.pi` and Giry measurability API.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

/-- A finite product of measurable probability-measure kernels is a measurable measure-valued map:
if each `ν i : Ω → ProbabilityMeasure (α i)` is measurable, then
`ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` is measurable. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi_toMeasure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, Measurable (ν i)) :
    Measurable fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi univ '' Set.pi univ fun i => {s : Set (α i) | MeasurableSet s})
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _ ⟨B, hB, rfl⟩
  have hBmeas : ∀ i, MeasurableSet (B i) := fun i => hB i (mem_univ i)
  simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
  exact Finset.measurable_prod Finset.univ fun i _ =>
    (Measure.measurable_coe (hBmeas i)).comp (measurable_subtype_coe.comp (hν i))

/-- `AEMeasurable` form of `measurable_probabilityMeasure_pi_toMeasure` from **measurable**
coordinate kernels (hence the `_of_measurable` suffix — this is not the stronger statement from
merely `∀ i, AEMeasurable (ν i) μ`). This is the form `Measure.bind_apply` consumers need. -/
theorem aemeasurable_probabilityMeasure_pi_toMeasure_of_measurable {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)] {μ : Measure Ω}
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, Measurable (ν i)) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) μ :=
  (measurable_probabilityMeasure_pi_toMeasure ν hν).aemeasurable

/-- Constant-coordinate specialization of `measurable_probabilityMeasure_pi_toMeasure`: the random
product `ω ↦ (ν ω)^{⊗ Fin m}` is measurable. This is the form `ConditionallyIIDWith` uses. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi_const_toMeasure {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {m : ℕ} (ν : Ω → ProbabilityMeasure α) (hν : Measurable ν) :
    Measurable fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  measurable_probabilityMeasure_pi_toMeasure (fun _ => ν) (fun _ => hν)

/-- `AEMeasurable` form of `measurable_probabilityMeasure_pi_const_toMeasure` from a **measurable**
directing kernel. -/
theorem aemeasurable_probabilityMeasure_pi_const_toMeasure_of_measurable {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : Measurable ν) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
  (measurable_probabilityMeasure_pi_const_toMeasure ν hν).aemeasurable

end MeasureTheory

end TauCeti
