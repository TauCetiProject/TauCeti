/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability of Carathéodory compositions

Let `g : α → X → G` be a *Carathéodory function*: `t ↦ g t x` is almost everywhere strongly
measurable for each `x` and `x ↦ g t x` is continuous for each `t`. Then `t ↦ g t (u t)` is almost
everywhere strongly measurable for every almost everywhere strongly measurable `u : α → X`
(`MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuous`). For a real-valued `g`, as in
the application below, measurability of each section `t ↦ g t x` already suffices.

No separability or metrizability is asked of `X`: `u` is approximated by simple functions, on
whose finitely many fibres `t ↦ g t (u t)` is one of the sections `t ↦ g t x`. This
is what weak measurability of a time-dependent operator `A(t) : V →L[ℝ] V*` in parabolic problems
needs: `t ↦ A(t) u(t) φ(t)` is measurable as soon as `t ↦ A(t) u v` is for all fixed `u, v`, for
an arbitrary Hilbert space `V`. Mathlib's
`stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` proves joint measurability
instead, which needs a second-countable metrizable parameter space.
-/

public section

open Filter Set
open scoped Topology

namespace MeasureTheory

variable {α X G : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace X]
  [TopologicalSpace G] [TopologicalSpace.PseudoMetrizableSpace G]

/-- **Carathéodory composition.** If `t ↦ g t x` is almost everywhere strongly measurable for every
`x` and each `g t` is continuous, then `t ↦ g t (u t)` is almost everywhere strongly measurable for
every almost everywhere strongly measurable `u`. -/
theorem AEStronglyMeasurable.apply_of_forall_of_continuous {u : α → X}
    (hu : AEStronglyMeasurable u μ) {g : α → X → G}
    (hg : ∀ x, AEStronglyMeasurable (fun t => g t x) μ) (hg_cont : ∀ t, Continuous (g t)) :
    AEStronglyMeasurable (fun t => g t (u t)) μ := by
  obtain ⟨v, hv, huv⟩ := hu
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n t => g t (hv.approx n t))
    (fun n => ?_) ?_
  · -- On each of the finitely many fibres of `hv.approx n`, the function is some `t ↦ g t x`.
    have hcover : (⋃ x : (hv.approx n).range, hv.approx n ⁻¹' {(x : X)}) = univ :=
      eq_univ_of_forall fun t => mem_iUnion.2 ⟨⟨_, (hv.approx n).mem_range_self t⟩, rfl⟩
    have : Countable (hv.approx n).range := Finset.countable_toSet _
    rw [← Measure.restrict_univ (μ := μ), ← hcover, aestronglyMeasurable_iUnion_iff]
    intro x
    refine (hg x).restrict.congr ?_
    filter_upwards [ae_restrict_mem ((hv.approx n).measurableSet_fiber x)] with t ht
    rw [mem_preimage, mem_singleton_iff] at ht
    rw [ht]
  · filter_upwards [huv] with t ht
    rw [ht]
    exact ((hg_cont t).tendsto _).comp (hv.tendsto_approx t)

end MeasureTheory
