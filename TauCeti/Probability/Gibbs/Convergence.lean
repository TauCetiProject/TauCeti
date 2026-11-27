/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Specification
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Condexp
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cylinder
import TauCeti.Probability.Gibbs.Tail
import TauCeti.Probability.Martingale.Convergence

/-!
# Almost-sure limits of finite-volume Gibbs kernels

Let `γ` be a specification on a subshift `X`. For a Gibbs measure `μ`, the finite-volume
kernels along an increasing exhaustion give the conditional probability of each measurable
event given the tail σ-algebra in the almost-sure limit. For an extreme Gibbs probability
measure, tail triviality makes this limit the unconditional probability of the event. For a
finite alphabet the convergence then holds simultaneously on all cylinder events.
On a standard Borel subshift with a countable discrete alphabet, the kernels converge weakly
almost surely to the regular conditional law given the tail.

## References

* S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press, 2017, Theorem 6.63, p. 307.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set TauCeti.MeasureTheory
open scoped ENNReal

namespace TauCeti.Specification

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [TopologicalSpace S] [MeasurableSpace S]
  {X : Subshift Γ I S} {γ : Specification X} {μ : Measure X} {Λ : ℕ → Finset I}

/-- Along an increasing, cofinal sequence of volumes, the probabilities assigned by a Gibbs
specification to a measurable event converge almost surely to its conditional probability given
the tail σ-algebra. -/
theorem IsGibbs.ae_tendsto_kernel_measureReal [IsFiniteMeasure μ] (hμ : γ.IsGibbs μ)
    (hmono : Monotone Λ) (hΛ : Tendsto Λ atTop atTop) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (γ.kernel (Λ n) ω).real A) atTop
      (𝓝 (μ[A.indicator 1 | ⨅ D : Finset I, X.exterior D] ω)) := by
  have hanti : Antitone (fun D : Finset I => X.exterior D) :=
    fun _ _ h => X.exterior_anti (Finset.coe_subset.2 h)
  have htail : (⨅ n, X.exterior (Λ n : Set I)) = ⨅ D : Finset I, X.exterior D :=
    hanti.iInf_comp_tendsto_atTop hΛ
  have hcond := ae_all_iff.2 fun n =>
    (isGibbs_iff_ae_eq_condExp.1 hμ) (Λ n) A hA
  have hlimit := tendsto_ae_condExp_iInf (𝔽 := fun n => X.exterior (Λ n : Set I))
    (hanti.comp_monotone hmono) (X.exterior_le (Λ 0))
    (A.indicator (1 : X → ℝ)) (μ := μ)
  rw [htail] at hlimit
  filter_upwards [hcond, hlimit] with ω hω hlim
  exact hlim.congr fun n => (hω n).symm

/-- On a standard Borel subshift, for each measurable event the finite-volume probabilities
converge almost surely to the probability assigned by the regular conditional kernel given
the tail σ-algebra. -/
theorem IsGibbs.ae_tendsto_kernel_apply_condExpKernel [IsFiniteMeasure μ] [StandardBorelSpace X]
    (hμ : γ.IsGibbs μ) (hmono : Monotone Λ) (hΛ : Tendsto Λ atTop atTop) {A : Set X}
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => γ.kernel (Λ n) ω A) atTop
      (𝓝 (condExpKernel μ (⨅ D : Finset I, X.exterior D) ω A)) := by
  have hle : (⨅ D : Finset I, X.exterior D) ≤ Subtype.instMeasurableSpace :=
    (iInf_le _ ∅).trans (X.exterior_le _)
  filter_upwards [hμ.ae_tendsto_kernel_measureReal hmono hΛ hA,
    condExpKernel_ae_eq_condExp hle (μ := μ) hA] with ω hlim hω
  rw [← ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top _ _) (measure_ne_top _ _),
    ← measureReal_def, hω]
  exact hlim

/-- The finite-volume kernels converge weakly almost surely to the regular conditional law given
the tail σ-algebra. -/
theorem IsGibbs.ae_tendsto_kernel_condExpKernel [IsFiniteMeasure μ] [StandardBorelSpace X]
    [Countable I] [Countable S] [DiscreteTopology S] [DiscreteMeasurableSpace S]
    (hμ : γ.IsGibbs μ) (hmono : Monotone Λ) (hΛ : Tendsto Λ atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (γ.kernel (Λ n) ω).toProbabilityMeasure) atTop
      (𝓝 ((condExpKernel μ (⨅ D : Finset I, X.exterior D) ω).toProbabilityMeasure)) := by
  -- Only the countable family of cylinders prescribing a single pattern is needed for the limit.
  let C (D : Finset I) (η : D → S) : Set X :=
    (↑) ⁻¹' cylinder (α := fun _ : I => S) D {η}
  have hconv : ∀ᵐ ω ∂μ, ∀ (D : Finset I) (η : D → S),
      Tendsto (fun n => γ.kernel (Λ n) ω (C D η)) atTop
        (𝓝 (condExpKernel μ (⨅ D : Finset I, X.exterior D) ω (C D η))) :=
    ae_all_iff.2 fun D => ae_all_iff.2 fun η =>
      hμ.ae_tendsto_kernel_apply_condExpKernel hmono hΛ
        (measurable_subtypeVal ((measurableSet_singleton η).cylinder D))
  filter_upwards [hconv] with ω hω
  refine tendsto_of_forall_tendsto_fullShift_cylinder (X := (X : Set (I → S))) fun D η => ?_
  simp only [SymbolicDynamics.FullShift.cylinder_eq_cylinder_singleton,
    ProbabilityMeasure.coeFn_def, Measure.coe_toProbabilityMeasure]
  exact (ENNReal.tendsto_toNNReal_iff (measure_ne_top _ _) (fun _ => measure_ne_top _ _)).2
    (hω D (D.restrict η))

/-- For an extreme Gibbs probability measure, the finite-volume probabilities of a fixed
measurable event converge almost surely to its unconditional probability along any increasing
exhaustion. -/
theorem ae_tendsto_kernel_apply_of_mem_extremePoints [Countable I]
    (hμ : μ ∈ extremePoints ℝ≥0∞ γ.gibbsMeasures)
    (hmono : Monotone Λ) (hΛ : Tendsto Λ atTop atTop) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => γ.kernel (Λ n) ω A) atTop (𝓝 (μ A)) := by
  have hmem := (mem_extremePoints.1 hμ).1
  obtain ⟨_, hGibbs⟩ := mem_gibbsMeasures_iff.1 hmem
  have htriv := (mem_extremePoints_gibbsMeasures_iff_measure_eq_zero_or_one hmem).1 hμ
  have hle : (⨅ D : Finset I, X.exterior D) ≤ Subtype.instMeasurableSpace :=
    (iInf_le _ ∅).trans (X.exterior_le _)
  have hconst := condExp_ae_eq_integral_of_forall_zero_or_one hle
    (fun B hB => htriv B (MeasurableSpace.measurableSet_iInf.1 hB)) (A.indicator (1 : X → ℝ))
  rw [integral_indicator_one hA] at hconst
  filter_upwards [hGibbs.ae_tendsto_kernel_measureReal hmono hΛ hA, hconst] with ω hlim hω
  rw [hω] at hlim
  exact (ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top _ _) (measure_ne_top μ A)).1 hlim

/-- **Extreme Gibbs measures are limits.** For a finite alphabet, along any increasing exhaustion
the finite-volume kernels converge to an extreme Gibbs probability measure on all cylinder
events simultaneously for almost every boundary configuration. -/
theorem ae_forall_tendsto_kernel_cylinder_of_mem_extremePoints [Countable I] [Finite S]
    (hμ : μ ∈ extremePoints ℝ≥0∞ γ.gibbsMeasures)
    (hmono : Monotone Λ) (hΛ : Tendsto Λ atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ A ∈ measurableCylinders (fun _ : I => S),
      Tendsto (fun n => γ.kernel (Λ n) ω ((↑) ⁻¹' A)) atTop (𝓝 (μ ((↑) ⁻¹' A))) := by
  have h : ∀ᵐ ω ∂μ, ∀ (D : Finset I) (B : {B : Set (D → S) // MeasurableSet B}),
      Tendsto (fun n => γ.kernel (Λ n) ω ((↑) ⁻¹' cylinder (α := fun _ : I => S) D B.val))
        atTop (𝓝 (μ ((↑) ⁻¹' cylinder (α := fun _ : I => S) D B.val))) :=
    ae_all_iff.2 fun D => ae_all_iff.2 fun B =>
      ae_tendsto_kernel_apply_of_mem_extremePoints hμ hmono hΛ
        (measurable_subtypeVal (B.property.cylinder D))
  filter_upwards [h] with ω hω A hA
  obtain ⟨D, B, hB, rfl⟩ := (mem_measurableCylinders A).1 hA
  exact hω D ⟨B, hB⟩

end TauCeti.Specification
