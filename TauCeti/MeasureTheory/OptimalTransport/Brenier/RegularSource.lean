/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.Analysis.Convex.CCHypersurface.Zajicek

/-!
# Regular sources for quadratic optimal transport

Brenier's theorem (`TauCeti/MeasureTheory/OptimalTransport/Brenier.lean`) holds whenever the source
law `μ` on a finite-dimensional real inner product space `E` is **`c - c`-regular**
(`TauCeti.IsCCRegular μ`), strictly generalizing absolute continuity with respect to additive Haar
measure (e.g. atomless singular measures on `ℝ`, or product Cantor measures on `ℝ²`).

This module proves the converse / sharp characterization of Gangbo–McCann (1996) and
Ambrosio–Gigli (2013, Theorem 1.26): a `P₂` probability law `μ` is `c - c`-regular iff for every
`P₂` target `ν`, every quadratic optimal coupling is induced by a measurable transport map (note
uniqueness *alone* holds trivially for Dirac masses).

## Main statements

* `TauCeti.exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular`,
  `TauCeti.isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan`, and its existence
  and uniqueness counterpart — **Ambrosio–Gigli Theorem 1.26** in `MemLp` form.
* In `TauCeti.WassersteinSpace`: `isCCRegular_iff_forall_isOptimalCoupling_exists_eq_graphPlan` and
  `isCCRegular_iff_forall_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling`
  — **Ambrosio–Gigli Theorem 1.26** on `WassersteinSpace 2 E`.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113–161.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.25 and Theorem 1.26.
* C. Villani, *Topics in Optimal Transportation*, GSM 58, AMS, 2003, §2.1.3 and §2.4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace

namespace TauCeti

section SharpCharacterization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Converse splitting construction for non-regular sources (Ambrosio–Gigli Theorem 1.26,
necessity).** If a probability measure `μ` of finite second moment on a finite-dimensional real
inner product space `E` is *not* `c - c`-regular, then there exist a probability measure `ν` on `E`
with `MemLp id 2 ν` and a quadratic optimal coupling `π` between `μ` and `ν` that is not of the form
`graphPlan T μ` for any map `T : E → E`. -/
theorem exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular {μ : Measure E}
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hnot : ¬ IsCCRegular μ) :
    ∃ (ν : Measure E) (_ : IsProbabilityMeasure ν) (_ : MemLp id 2 ν) (π : Measure (E × E)),
      IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ∧
        ∀ T : E → E, π ≠ graphPlan T μ := by
  have : MeasurableEq E := ⟨isClosed_diagonal.measurableSet⟩
  simp only [isCCRegular_def, not_forall] at hnot; obtain ⟨s, hs, hμs⟩ := hnot
  obtain ⟨N, hμB⟩ : ∃ N : ℕ, μ (s ∩ closedBall 0 N) ≠ 0 := by
    by_contra! hall
    exact hμs ((Metric.iUnion_inter_closedBall_nat s 0).symm ▸ measure_iUnion_null hall)
  obtain ⟨K, ψ, T₁, T₂, -, -, hT₁m, hT₂m, hT₁s, hT₂s, hT₁n, hT₂n, hTne⟩ :=
    hs.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne (N : ℝ)
  let S₁ : E → E := fun x => x + T₁ x; let S₂ : E → E := fun x => x + T₂ x
  have hS₁m : Measurable S₁ := measurable_id.add hT₁m
  have hS₂m : Measurable S₂ := measurable_id.add hT₂m
  have hlp {T : E → E} (hTm : Measurable T) (hTn : ∀ x, ‖T x‖ ≤ K) :
      MemLp id 2 (μ.map (fun x => x + T x)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (measurable_id.add hTm).aemeasurable).2
      (hμ2.add (MemLp.of_bound hTm.aestronglyMeasurable K (.of_forall hTn)))
  let ν : Measure E := (2⁻¹ : ℝ≥0∞) • μ.map S₁ + (2⁻¹ : ℝ≥0∞) • μ.map S₂
  have hν2 : MemLp id 2 ν :=
    ((hlp hT₁m hT₁n).smul_measure (ENNReal.inv_ne_top.2 two_ne_zero)).add_measure
      ((hlp hT₂m hT₂n).smul_measure (ENNReal.inv_ne_top.2 two_ne_zero))
  have hπ : IsCoupling ((2⁻¹ : ℝ≥0∞) • graphPlan S₁ μ + (2⁻¹ : ℝ≥0∞) • graphPlan S₂ μ) μ ν := by
    have h := ((isCoupling_graphPlan_map (μ := μ) hS₁m.aemeasurable).smul (2⁻¹ : ℝ≥0∞)).add
      ((isCoupling_graphPlan_map (μ := μ) hS₂m.aemeasurable).smul (2⁻¹ : ℝ≥0∞))
    rwa [← add_smul, ENNReal.inv_two_add_inv_two, one_smul] at h
  have hsub {T : E → E} (hTm : Measurable T) (hTs : ∀ x z, ψ x + inner ℝ (z - x) (T x) ≤ ψ z) :
      ∀ᵐ z ∂(2⁻¹ : ℝ≥0∞) • graphPlan (fun x => x + T x) μ,
        z.2 ∈ subdifferential (innerₗ E)
          (fun w => ((‖w‖ ^ 2 / 2 : ℝ) : EReal) + (ψ w : EReal)) z.1 :=
    Measure.ae_smul_measure ((ae_snd_eq_graphPlan (measurable_id.add hTm).aemeasurable).mono
      fun z hz => hz ▸ mem_subdifferential_add (innerₗ E)
        (mem_subdifferential_norm_sq_div_two z.1)
        ((mem_subdifferential_coe_iff (innerₗ E) ψ).2 fun w => by
          simpa only [innerₗ_apply_apply] using hTs z.1 w)) _
  exact ⟨ν, ⟨by simp [ν, smul_eq_mul, ENNReal.inv_two_add_inv_two]⟩, hν2, _,
    hπ.isOptimalCoupling_of_ae_mem_subdifferential hμ2 hν2
      (ae_add_measure_iff.2 ⟨hsub hT₁m hT₁s, hsub hT₂m hT₂s⟩),
    smul_graphPlan_add_smul_graphPlan_ne_graphPlan (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
      (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) hS₁m.aemeasurable hS₂m.aemeasurable
      (fun hae => hμB (measure_mono_null (t := {x | ¬ S₁ x = S₂ x})
        (fun x hx => mem_ofPred_eq.mpr fun hEq => hTne x hx (add_left_cancel hEq))
        (ae_iff.1 hae)))⟩

/-- **Ambrosio–Gigli Theorem 1.26 (determinism of all optimal plans).** Let `μ` be a probability
measure with `MemLp id 2 μ` on a finite-dimensional real inner product space `E`. Then `μ` is
`c - c`-regular if and only if for every probability measure `ν` on `E` with `MemLp id 2 ν`, every
optimal quadratic coupling between `μ` and `ν` is induced by a measurable transport map. -/
theorem isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan {μ : Measure E}
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) :
    IsCCRegular μ ↔
      ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν →
        ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν →
          ∃ T : E → E, Measurable T ∧ π = graphPlan T μ := by
  refine ⟨fun hμ ν _ hν2 π hπ => ?_, fun hall => by_contra fun hnot => ?_⟩
  · have hfin := hπ.toIsCoupling.transportCost_norm_sub_sq_div_two_ne_top hμ2 hν2
    exact let ⟨_, _, _, _, _, hgraph⟩ := hπ.exists_eq_graphPlan_gradient hμ hfin
      ⟨_, measurable_gradient _, hgraph⟩
  · obtain ⟨ν, hνp, hν2, π, hπ, hne⟩ :=
      exists_memLp_isOptimalCoupling_forall_ne_graphPlan_of_not_isCCRegular hμ2 hnot
    exact let ⟨T, _, hT⟩ := @hall ν hνp hν2 π hπ; hne T hT

/-- **Ambrosio–Gigli Theorem 1.26 (existence of a unique, map-induced optimal plan).** Let `μ` be a
probability measure with `MemLp id 2 μ` on a finite-dimensional real inner product space `E`. Then
`μ` is `c - c`-regular if and only if for every probability measure `ν` on `E` with `MemLp id 2 ν`,
there exists an optimal transport map `T : E → E` from `μ` to `ν` whose graph plan `graphPlan T μ`
is the unique optimal quadratic coupling between `μ` and `ν`. -/
theorem
  isCCRegular_iff_forall_memLp_exists_isKantorovichOptimalTransportMap_and_unique_isOptimalCoupling
    {μ : Measure E} [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) :
    IsCCRegular μ ↔
      ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν →
        ∃ T : E → E,
          IsKantorovichOptimalTransportMap
            (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν T ∧
          ∀ π, IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν ↔
            π = graphPlan T μ := by
  refine ⟨fun hμ ν _ hν2 => ?_, fun hall =>
    (isCCRegular_iff_forall_memLp_isOptimalCoupling_exists_eq_graphPlan hμ2).2
      fun ν _ hν2 π hπ => by
        obtain ⟨T, hT, hiff⟩ := hall ν hν2
        exact ⟨hT.aemeasurable.mk T, hT.aemeasurable.measurable_mk,
          ((hiff π).1 hπ).trans (graphPlan_congr hT.aemeasurable.ae_eq_mk)⟩⟩
  have hfin := transportCost_norm_sub_sq_div_two_ne_top_of_memLp hμ2 hν2
  exact let ⟨_, _, _, _, _, hT, hiff, _⟩ := exists_isKantorovichOptimalTransportMap_gradient hμ hfin
    ⟨_, hT, hiff⟩

namespace WassersteinSpace

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
  refine ⟨fun h ν π hπ => h _ ν.hasFiniteMoment.memLp_id π hπ, fun h ν _ hν2 π hπ => ?_⟩
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
  refine ⟨fun h ν => h _ ν.hasFiniteMoment.memLp_id, fun h ν _ hν2 => ?_⟩
  let νP : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hmk := h (WassersteinSpace.mk νP (hasFiniteMoment_of_memLp_id hν2))
  rw [WassersteinSpace.coe_mk] at hmk; exact hmk

end WassersteinSpace

end SharpCharacterization

end TauCeti
