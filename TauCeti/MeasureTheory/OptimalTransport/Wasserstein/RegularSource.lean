/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier.RegularSource
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Regular sources on the quadratic Wasserstein space

This module lifts the `MemLp`-form characterization of `c - c`-regularity in
`TauCeti.MeasureTheory.OptimalTransport.Brenier.RegularSource` (Ambrosio–Gigli Theorem 1.26)
to `TauCeti.WassersteinSpace 2 E`.

## Main statements

In `TauCeti.WassersteinSpace`:

* `isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan` — a law in `WassersteinSpace 2 E`
  is `c - c`-regular iff every optimal quadratic coupling to any target in
  `WassersteinSpace 2 E` is induced by a measurable map.
* `isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling` —
  a law in `WassersteinSpace 2 E` is `c - c`-regular iff for every target in
  `WassersteinSpace 2 E`, there exists a quadratic optimal transport map whose graph plan is the
  unique optimal coupling.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace WassersteinSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Ambrosio–Gigli Theorem 1.26 on `WassersteinSpace 2 E` (determinism form).** A quadratic
Wasserstein law `μ : WassersteinSpace 2 E` has `c - c`-regular underlying measure iff for every
target `ν : WassersteinSpace 2 E`, every optimal quadratic coupling is induced by a measurable
transport map. -/
theorem isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan (μ : WassersteinSpace 2 E) :
    IsCCRegular ((μ : ProbabilityMeasure E) : Measure E) ↔
      ∀ (ν : WassersteinSpace 2 E) (π : Measure (E × E)),
        IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
          ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
        ∃ T : E → E, Measurable T ∧ π = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan μ.hasFiniteMoment.memLp_id]
  refine ⟨fun h ν π hπ => h _ ν.hasFiniteMoment.memLp_id π hπ,
    fun h ν hν2 π hπ => ?_⟩
  have : IsProbabilityMeasure ν := ⟨hπ.toIsCoupling.measure_univ_eq.symm.trans measure_univ⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hmk := h (WassersteinSpace.mk νP (hasFiniteMoment_of_memLp_id hν2)) π
  rw [WassersteinSpace.coe_mk] at hmk; exact hmk hπ

/-- **Ambrosio–Gigli Theorem 1.26 on `WassersteinSpace 2 E` (existence and uniqueness form).** A
quadratic Wasserstein law `μ : WassersteinSpace 2 E` has `c - c`-regular underlying measure iff for
every target `ν : WassersteinSpace 2 E`, there exists an optimal transport map `T` whose graph plan
is the unique optimal quadratic coupling between `μ` and `ν`. -/
theorem isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling
    (μ : WassersteinSpace 2 E) :
    IsCCRegular ((μ : ProbabilityMeasure E) : Measure E) ↔
      ∀ ν : WassersteinSpace 2 E,
        ∃ T : E → E,
          IsKantorovichOptimalTransportMap
            (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
            ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) T ∧
          ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
            ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) ↔
            π = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [
  isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling
    μ.hasFiniteMoment.memLp_id]
  refine ⟨fun h ν => h _ (by simp) ν.hasFiniteMoment.memLp_id, fun h ν hνeq hν2 => ?_⟩
  have : IsProbabilityMeasure ν := ⟨by rw [hνeq, measure_univ]⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hmk := h (WassersteinSpace.mk νP (hasFiniteMoment_of_memLp_id hν2))
  rw [WassersteinSpace.coe_mk] at hmk; exact hmk

end WassersteinSpace

end TauCeti
