/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer.Specification
import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift

/-!
# Gibbs measures of the dimer specification satisfy the cylinder identities

Let `G` be a locally finite graph with countably many edges, `w` a positive weight on its edges
and `γ^w` the dimer specification on the subshift `𝔛(G)` of dimer configurations. For a finite
set `F` of edges, let `E` be a finite set containing every edge that shares a vertex with an edge
of `F`, and write `[ω]_E` for the cylinder of the configurations agreeing with `ω` on `E`.

**The Boltzmann mass of a cylinder.** For dimer configurations `ω` and `η`, the law
`γ^w_F(· | η)` gives `[ω]_E` the mass `w(ω ∩ F) / Z^w_F(η)` when `η` agrees with `ω` on `E ∖ F`,
and `0` otherwise (`SimpleGraph.dimerBoltzmann_setOf_forall_mem_eq`, proved in
`TauCeti.Probability.Gibbs.Dimer.Basic`): the only candidate in the completion set `Ω_F(η)` is the
gluing of `ω` on `F` to `η` off `F`, and it is a dimer configuration because `η` and `ω` agree on
the edges outside `F` at the vertices of `F`, so the restrictions to `F` of their completion sets
coincide (`SimpleGraph.image_restrict_dimerCompletionSet_eq`).

**Gibbs measures are dimer Gibbs.** Integrating this against a Gibbs probability measure `ν` of
`γ^w` gives `μ[ω]_E = ∫_{[ω]_{E ∖ F}} w(ω ∩ F) / Z^w_F dν` for the push-forward `μ` of `ν` to the
configurations. For dimer configurations `ω`, `ω'` agreeing off `F` the domains of integration
agree, so `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E`: the push-forward is dimer Gibbs in cylinder
form (`SimpleGraph.isDimerGibbs_map_val`).

## References

* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  Section 2.2.1.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.4.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

variable [G.LocallyFinite] [Countable G.edgeSet] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
  {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e}

/-- **Gibbs measures of the dimer specification are dimer Gibbs.** The push-forward to the
configurations of a Gibbs probability measure of `γ^w` on `𝔛(G)` is a probability measure carried
by the dimer configurations and satisfies the cylinder identities
`w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E`. -/
theorem isDimerGibbs_map_val {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    {ν : Measure (G.dimerSubshift Γ hΓ)} [IsProbabilityMeasure ν]
    (hν : (dimerSpecification Γ hΓ hw).IsGibbs ν) : G.IsDimerGibbs w (ν.map Subtype.val) := by
  have hval : Measurable (Subtype.val : G.dimerSubshift Γ hΓ → G.edgeSet → Bool) :=
    measurable_subtypeVal
  refine isDimerGibbs_iff.2 ⟨inferInstance, ?_, ?_⟩
  · rw [← compl_ofPred, Measure.map_apply hval measurableSet_setOf_isDimerConfiguration.compl]
    convert measure_empty (μ := ν)
    ext η
    simpa using mem_dimerSubshift.1 η.property
  intro F E ω ω' hω hω' hF hE
  -- the mass of a cylinder under the push-forward, by the DLR equation at `F`
  have key (ζ : G.edgeSet → Bool) (hζ : G.IsDimerConfiguration ζ) :
      ν.map Subtype.val {η | ∀ e ∈ E, η e = ζ e} =
        ∫⁻ η, {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ζ e}.indicator
          (fun _ => ENNReal.ofReal (G.dimerWeight w F ζ /
            G.dimerPartitionFunction w F η.val)) η.val ∂ν := by
    have hmeas : MeasurableSet {η : G.edgeSet → Bool | ∀ e ∈ E, η e = ζ e} :=
      SymbolicDynamics.FullShift.measurableSet_cylinder E ζ
    rw [Measure.map_apply hval hmeas, ← hν.lintegral_kernel F (hval hmeas)]
    refine lintegral_congr fun η => ?_
    rw [dimerSpecification_kernel, dimerKernel_apply, image_preimage_eq_inter_range,
      Subtype.range_coe_subtype, measure_inter_conull, dimerBoltzmann_setOf_forall_mem_eq w hE hζ
        (mem_dimerSubshift.1 η.property)]
    simpa [compl_ofPred] using dimerBoltzmann_setOf_not_isDimerConfiguration w F η.val
  have hcyl : {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ω' e} =
      {θ | ∀ e ∈ E, e ∉ F → θ e = ω e} := by
    ext θ
    simp only [mem_ofPred_eq]
    exact forall₂_congr fun e _ => forall_congr' fun he => by rw [hF e he]
  rw [key ω hω, key ω' hω', hcyl, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun η => ?_
  by_cases hη : η.val ∈ {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ω e}
  · simp only [indicator_of_mem hη]
    rw [← ENNReal.ofReal_mul (dimerWeight_pos hw F ω').le,
      ← ENNReal.ofReal_mul (dimerWeight_pos hw F ω).le]
    congr 1
    ring
  · simp only [indicator_of_notMem hη, mul_zero]

end SimpleGraph
