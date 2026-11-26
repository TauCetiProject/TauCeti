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
measurable for each `x` and `x ↦ g t x` is continuous for almost every `t`. Then `t ↦ g t (u t)` is
almost everywhere strongly measurable for every almost everywhere strongly measurable `u : α → X`
(`MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuousAt`); in fact continuity of `g t`
at the point `u t` suffices. When `G` is second countable, for instance for a real-valued `g`,
measurability of each section `t ↦ g t x` already implies the measurability hypothesis.

No separability or metrizability is asked of `X`: `u` is approximated by simple functions `s`, on
whose finitely many fibres `t ↦ g t (s t)` is one of the sections `t ↦ g t x`. This
is what weak measurability of a time-dependent operator `A(t) : V →L[ℝ] V*` in parabolic problems
needs: `t ↦ A(t) u(t) φ(t)` is measurable as soon as `t ↦ A(t) u v` is for all fixed `u, v`, for
an arbitrary Hilbert space `V`. Mathlib's
`stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` proves joint measurability
instead, which needs a second-countable metrizable parameter space.

The pointwise version and the finite-support versions allow the same evaluation without
separability assumptions on the parameter space. The finite-support versions assume that the
evaluated family preserves zero and allow an arbitrary measure.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, Proposition 1.1.28.
-/

public section

open Filter Set

namespace MeasureTheory

variable {α X G : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace X]
  [TopologicalSpace G] [TopologicalSpace.PseudoMetrizableSpace G]

/-- **Pointwise Carathéodory composition.** Strongly measurable sections evaluated at a
strongly measurable argument are strongly measurable if each section in the argument variable
is continuous at the evaluation point. -/
theorem StronglyMeasurable.apply_of_forall_of_continuousAt {u : α → X}
    (hu : StronglyMeasurable u) {g : α → X → G}
    (hg : ∀ x, StronglyMeasurable (fun t ↦ g t x))
    (hg_cont : ∀ t, ContinuousAt (g t) (u t)) :
    StronglyMeasurable (fun t ↦ g t (u t)) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact StronglyMeasurable.of_subsingleton_dom
  have : Nonempty X := hα.map u
  have hs (s : SimpleFunc α X) : StronglyMeasurable (fun t ↦ g t (s t)) := by
    induction s using SimpleFunc.induction' with
    | const x => exact hg x
    | @pcw v w s hs hv hw =>
      have hp : StronglyMeasurable (fun t ↦ if t ∈ s then g t (v t) else g t (w t)) :=
        hv.ite hs hw
      simpa only [SimpleFunc.piecewise_apply, apply_ite] using hp
  exact stronglyMeasurable_of_tendsto atTop (fun n ↦ hs (hu.approx n))
    (tendsto_pi_nhds.2 fun t ↦ (hg_cont t).tendsto.comp (hu.tendsto_approx t))

/-- **Carathéodory composition.** If `t ↦ g t x` is almost everywhere strongly measurable for every
`x` and `g t` is continuous at `u t` for almost every `t`, then `t ↦ g t (u t)` is almost everywhere
strongly measurable for every almost everywhere strongly measurable `u`. -/
theorem AEStronglyMeasurable.apply_of_forall_of_continuousAt {u : α → X}
    (hu : AEStronglyMeasurable u μ) {g : α → X → G}
    (hg : ∀ x, AEStronglyMeasurable (fun t => g t x) μ)
    (hg_cont : ∀ᵐ t ∂μ, ContinuousAt (g t) (u t)) :
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
    filter_upwards [ae_restrict_mem ((hv.approx n).measurableSet_fiber x)] with t (ht : _ = _)
    rw [ht]
  · filter_upwards [huv, hg_cont] with t ht hct
    rw [ht] at hct ⊢
    exact hct.tendsto.comp (hv.tendsto_approx t)

/-- A zero-preserving Carathéodory family preserves finite strong measurability, without
sigma-finiteness of the ambient measure. Only strong measurability of its fixed sections is
required. -/
theorem FinStronglyMeasurable.apply_of_forall_of_continuousAt [Zero X] [T2Space X] [Zero G]
    {u : α → X} (hu : FinStronglyMeasurable u μ) {g : α → X → G}
    (hg : ∀ x, StronglyMeasurable (fun t ↦ g t x))
    (hg_cont : ∀ t, ContinuousAt (g t) (u t)) (hg_zero : ∀ t, g t 0 = 0) :
    FinStronglyMeasurable (fun t ↦ g t (u t)) μ := by
  obtain ⟨s, hs, hus, hμs⟩ := hu.exists_set_sigmaFinite
  have hv := hu.stronglyMeasurable.apply_of_forall_of_continuousAt hg hg_cont
  exact hv.finStronglyMeasurable_of_set_sigmaFinite hs
    (fun t ht ↦ by rw [hus t ht, hg_zero t]) hμs

/-- The a.e. Carathéodory evaluation preserves a.e. finite strong measurability when it
preserves zero almost everywhere. Exceptional sets for the fixed sections may depend on the
argument. The ambient measure need not be sigma-finite. -/
theorem AEFinStronglyMeasurable.apply_of_forall_of_continuousAt [Zero X] [T2Space X] [Zero G]
    {u : α → X} (hu : AEFinStronglyMeasurable u μ) {g : α → X → G}
    (hg : ∀ x, AEStronglyMeasurable (fun t ↦ g t x) μ)
    (hg_cont : ∀ᵐ t ∂μ, ContinuousAt (g t) (u t)) (hg_zero : ∀ᵐ t ∂μ, g t 0 = 0) :
    AEFinStronglyMeasurable (fun t ↦ g t (u t)) μ := by
  classical
  have hu' : AEStronglyMeasurable u μ :=
    ⟨hu.mk u, hu.finStronglyMeasurable_mk.stronglyMeasurable, hu.ae_eq_mk⟩
  have hv := hu'.apply_of_forall_of_continuousAt hg hg_cont
  obtain ⟨s, hs, hus, hμs⟩ := hu.exists_set_sigmaFinite
  refine ⟨s.indicator (hv.mk _), hv.stronglyMeasurable_mk.indicator hs
    |>.finStronglyMeasurable_of_set_sigmaFinite hs
      (fun t ht ↦ Set.indicator_of_notMem ht _) hμs, ?_⟩
  filter_upwards [hv.ae_eq_mk, (ae_restrict_iff' hs.compl).1 hus, hg_zero] with t ht hus ht0
  by_cases hts : t ∈ s
  · simp [hts, ht]
  · simp [hts, hus hts, ht0]

end MeasureTheory
