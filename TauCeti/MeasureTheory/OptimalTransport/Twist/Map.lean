/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Twist.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MeasurableSelection
public import TauCeti.MeasureTheory.OptimalTransport.Monge

/-!
# Optimal transport maps from the twist condition

A dual certificate for a differentiable twisted cost determines a transport map. The contact
condition makes almost every conditional law a Dirac measure; measurable selection then realizes
the certified plan as a graph plan. The resulting map attains both the Kantorovich and Monge
values, and every other Kantorovich-optimal map agrees with it almost everywhere. The source
derivative of the cost at the selected partner equals the derivative of the potential:
`fderiv ℝ φ x = fderiv ℝ (fun x' ↦ c (x', T x)) x` almost everywhere.

The cost is jointly measurable to identify the integral of the selected map with the cost of its
graph plan. The target is standard Borel to select a measurable representative of the conditional
Dirac points. No compactness, absolute continuity, or finite-dimensionality is required.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 10, for the abstract
  twist mechanism that turns a contact set into a transport map.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace TauCeti

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  {μ : Measure E} [IsFiniteMeasure μ] {ν : Measure Y} {π : Measure (E × Y)}
  {c : E × Y → ℝ} {φ : E → ℝ} {ψ : Y → ℝ}

/-- A certified optimal plan for a jointly measurable twisted cost is induced by a measurable
transport map. The map attains the Kantorovich value and is unique up to `μ`-almost everywhere
equality among maps attaining that value. Almost everywhere, the selected pair lies in the
contact set and `fderiv ℝ φ x = fderiv ℝ (fun x' ↦ c (x', T x)) x`. -/
theorem IsDualCertificate.exists_optimal_transportMap_unique_ae
    (hc₀ : ∀ z, 0 ≤ c z)
    (h : IsDualCertificate (fun z ↦ ENNReal.ofReal (c z)) π μ ν φ ψ)
    (hcmeas : Measurable c)
    (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x)
    (hc : ∀ᵐ x ∂μ, ∀ y, (x, y) ∈ contactSet c (fun x ↦ (φ x : EReal))
      (fun y ↦ (ψ y : EReal)) → DifferentiableAt ℝ (fun x' ↦ c (x', y)) x)
    (htwist : ∀ᵐ x ∂μ, Set.InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x)
      {y | DifferentiableAt ℝ (fun x' ↦ c (x', y)) x}) :
    ∃ T : E → Y, Measurable T ∧
      IsKantorovichOptimalTransportMap (fun z ↦ ENNReal.ofReal (c z)) μ ν T ∧
      π = graphPlan T μ ∧
      (∀ᵐ x ∂μ, (x, T x) ∈ contactSet c (fun x ↦ (φ x : EReal))
        (fun y ↦ (ψ y : EReal)) ∧
        fderiv ℝ φ x = fderiv ℝ (fun x' ↦ c (x', T x)) x) ∧
      ∀ S : E → Y,
        IsKantorovichOptimalTransportMap (fun z ↦ ENNReal.ofReal (c z)) μ ν S →
        S =ᵐ[μ] T := by
  let : IsFiniteMeasure π := h.toIsCoupling.isFiniteMeasure
  have hcost : AEMeasurable (fun z ↦ ENNReal.ofReal (c z)) π :=
    hcmeas.ennreal_ofReal.aemeasurable
  obtain ⟨T, hT, hLaw, hgraph⟩ :=
    h.toIsCoupling.exists_graphPlan_of_ae_exists_condKernel_eq_dirac
      ((h.ae_exists_condKernel_eq_dirac hc₀ h.isOptimalCoupling hcost hφ hc htwist).mono
        fun _ ⟨y, _, hy⟩ ↦ ⟨y, hy⟩)
  have hopt : IsKantorovichOptimalTransportMap (fun z ↦ ENNReal.ofReal (c z)) μ ν T :=
    (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hLaw
      hcmeas.ennreal_ofReal.aemeasurable).2 (hgraph ▸ h.isOptimalCoupling)
  have hcontact : ∀ᵐ x ∂μ, (x, T x) ∈ contactSet c
      (fun x ↦ (φ x : EReal)) (fun y ↦ (ψ y : EReal)) := by
    have haeπ := h.ae_mem_dualContactSet
    rw [hgraph, graphPlan_def] at haeπ
    have hae : ∀ᵐ x ∂μ,
        (x, T x) ∈ dualContactSet (fun z ↦ ENNReal.ofReal (c z)) φ ψ :=
      MeasureTheory.ae_of_ae_map (aemeasurable_prodMk_self hT.aemeasurable)
        haeπ
    simpa only [← dualContactSet_ofReal hc₀] using hae
  have hderiv : ∀ᵐ x ∂μ,
      fderiv ℝ φ x = fderiv ℝ (fun x' ↦ c (x', T x)) x := by
    filter_upwards [hcontact, hφ, hc] with x hxy hφx hcx
    have hfeas : ∀ x' y, (φ x' : EReal) + (ψ y : EReal) ≤ (c (x', y) : EReal) :=
      fun x' y ↦ by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        exact (dualFeasible_ofReal_iff hc₀ φ ψ).1 h.dualFeasible x' y
    simpa using fderiv_eq_of_mem_contactSet
      (.of_forall fun x' ↦ hfeas x' (T x))
      (.of_forall fun _ ↦ EReal.coe_ne_bot _) hxy hφx (hcx (T x) hxy)
  refine ⟨T, hT, hopt, hgraph, ?_, ?_⟩
  · filter_upwards [hcontact, hderiv] with x hxy hd using ⟨hxy, hd⟩
  · intro S hS
    have hSgraph : IsOptimalCoupling (fun z ↦ ENNReal.ofReal (c z))
        (graphPlan S μ) μ ν :=
      (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hS.toHasLaw
        hcmeas.ennreal_ofReal.aemeasurable).1 hS
    have heq : graphPlan S μ = π :=
      h.eq_of_isOptimalCoupling hc₀ hSgraph hcmeas.ennreal_ofReal.aemeasurable hφ hc htwist
    exact (graphPlan_eq_graphPlan_iff hS.toHasLaw.aemeasurable hT.aemeasurable).1
      (heq.trans hgraph)

end TauCeti
