module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Measurability of finite product probability-measure kernels

This file provides the measurability API for the finite product of probability measures over a
finite index type, phrased directly over Mathlib's `ProbabilityMeasure.pi`:

* `measurable_probabilityMeasure_pi` — the product combinator
  `ProbabilityMeasure.pi : (Π i, ProbabilityMeasure (α i)) → ProbabilityMeasure (Π i, α i)`
  is measurable.
* `measurable_probabilityMeasure_pi_toMeasure` — the measure-valued random product
  `ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` is measurable, for measurable coordinate
  kernels `ν i`.
* `aemeasurable_probabilityMeasure_pi_toMeasure` — the same map is `AEMeasurable` from
  a.e.-measurable coordinate kernels (`∀ i, AEMeasurable (ν i) μ`); the `_of_measurable` corollary
  is the measurable-input form.
* the constant-coordinate (`fun _ : Fin m => ν ω`) specializations
  `measurable_probabilityMeasure_pi_const_toMeasure` and
  `aemeasurable_probabilityMeasure_pi_const_toMeasure`, used by `ConditionallyIIDWith`.

This file does not introduce a new product-kernel structure; the lemmas live directly over Mathlib's
`ProbabilityMeasure.pi`. It advances `TauCetiRoadmap/Exchangeability`, Layer 1 (product kernels,
conditional independence, mixtures), and is motivated by the product-kernel layer of
`cameronfreer/exchangeability` (`MeasureKernels.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`), implemented using Mathlib's `ProbabilityMeasure.pi` and
Giry measurability API; the combinator generalizes Mathlib's binary
`ProbabilityMeasure.measurable_fun_prod` to finite index types.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : Measure Ω}

/-- The finite product combinator `ProbabilityMeasure.pi` is a measurable map
`(Π i, ProbabilityMeasure (α i)) → ProbabilityMeasure (Π i, α i)`. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi :
    Measurable (ProbabilityMeasure.pi : (∀ i, ProbabilityMeasure (α i)) → ProbabilityMeasure
      (∀ i, α i)) := by
  have hcore : Measurable fun p : ∀ i, ProbabilityMeasure (α i) =>
      (ProbabilityMeasure.pi p).toMeasure := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi univ '' Set.pi univ fun i => {s : Set (α i) | MeasurableSet s})
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨B, hB, rfl⟩
    have hBmeas : ∀ i, MeasurableSet (B i) := fun i => hB i (mem_univ i)
    simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    exact Finset.measurable_prod Finset.univ fun i _ =>
      (Measure.measurable_coe (hBmeas i)).comp (measurable_subtype_coe.comp (measurable_pi_apply i))
  exact hcore.subtype_mk

/-- A finite product of measurable probability-measure kernels is a measurable measure-valued map:
if each `ν i : Ω → ProbabilityMeasure (α i)` is measurable, then
`ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` is measurable. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi_toMeasure
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, Measurable (ν i)) :
    Measurable fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure :=
  (measurable_subtype_coe.comp measurable_probabilityMeasure_pi).comp (measurable_pi_lambda _ hν)

/-- A finite product of a.e.-measurable probability-measure kernels is an a.e.-measurable
measure-valued map: if each `ν i : Ω → ProbabilityMeasure (α i)` is `AEMeasurable`, then so is
`ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure`. -/
@[fun_prop]
theorem aemeasurable_probabilityMeasure_pi_toMeasure
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, AEMeasurable (ν i) μ) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) μ :=
  (measurable_subtype_coe.comp measurable_probabilityMeasure_pi).comp_aemeasurable
    (aemeasurable_pi_lambda _ hν)

/-- Measurable-input corollary of `aemeasurable_probabilityMeasure_pi_toMeasure`. -/
theorem aemeasurable_probabilityMeasure_pi_toMeasure_of_measurable
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, Measurable (ν i)) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) μ :=
  aemeasurable_probabilityMeasure_pi_toMeasure ν fun i => (hν i).aemeasurable

/-- Constant-coordinate specialization of `measurable_probabilityMeasure_pi_toMeasure`: the random
product `ω ↦ (ν ω)^{⊗ Fin m}` is measurable. This is the form `ConditionallyIIDWith` uses. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi_const_toMeasure {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : Measurable ν) :
    Measurable fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  measurable_probabilityMeasure_pi_toMeasure (fun _ => ν) (fun _ => hν)

/-- Constant-coordinate specialization of `aemeasurable_probabilityMeasure_pi_toMeasure`: the random
product `ω ↦ (ν ω)^{⊗ Fin m}` is `AEMeasurable` from an a.e.-measurable directing kernel. -/
@[fun_prop]
theorem aemeasurable_probabilityMeasure_pi_const_toMeasure {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : AEMeasurable ν μ) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
  aemeasurable_probabilityMeasure_pi_toMeasure (fun _ => ν) (fun _ => hν)

/-- Measurable-input corollary of `aemeasurable_probabilityMeasure_pi_const_toMeasure`. -/
theorem aemeasurable_probabilityMeasure_pi_const_toMeasure_of_measurable {α : Type*}
    [MeasurableSpace α] {m : ℕ} (ν : Ω → ProbabilityMeasure α) (hν : Measurable ν) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
  aemeasurable_probabilityMeasure_pi_const_toMeasure ν hν.aemeasurable

end MeasureTheory

end TauCeti
