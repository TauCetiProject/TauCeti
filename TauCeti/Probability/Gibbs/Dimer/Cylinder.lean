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
and `0` otherwise (`SimpleGraph.dimerBoltzmann_setOf_forall_mem_eq`): the only candidate in the
completion set `Ω_F(η)` is the gluing of `ω` on `F` to `η` off `F`, and it is a dimer
configuration because `η` and `ω` agree on the edges outside `F` at the vertices of `F`, so the
restrictions to `F` of their completion sets coincide
(`SimpleGraph.image_restrict_dimerCompletionSet_eq`).

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

/-- **The Boltzmann mass of a cylinder.** Let `E` contain every edge sharing a vertex with an edge
of `F`. For dimer configurations `ω` and `η`, `γ^w_F(· | η)` gives the cylinder `[ω]_E` the mass
`w(ω ∩ F) / Z^w_F(η)` if `η` agrees with `ω` on `E ∖ F`, and `0` otherwise. -/
theorem dimerBoltzmann_setOf_forall_mem_eq (w : G.edgeSet → ℝ) {F E : Finset G.edgeSet}
    (hE : ∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E)
    {ω η : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) (hη : G.IsDimerConfiguration η) :
    G.dimerBoltzmann w F η {ζ | ∀ e ∈ E, ζ e = ω e} =
      {ζ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → ζ e = ω e}.indicator
        (fun _ => ENNReal.ofReal (G.dimerWeight w F ω / G.dimerPartitionFunction w F η)) η := by
  have hmeas : MeasurableSet {ζ : G.edgeSet → Bool | ∀ e ∈ E, ζ e = ω e} :=
    SymbolicDynamics.FullShift.measurableSet_cylinder E ω
  rw [dimerBoltzmann_apply w F η hmeas]
  by_cases hηω : ∀ e ∈ E, e ∉ F → η e = ω e
  · rw [indicator_of_mem (by exact hηω)]
    -- the gluing of `ω` on `F` to `η` off `F` is a dimer configuration
    have himg := image_restrict_dimerCompletionSet_eq hη hω fun e he ⟨f, hf, v, hve, hvf⟩ =>
      hηω e (hE f hf e ⟨v, hvf, hve⟩) he
    obtain ⟨ω', hω', hr⟩ : F.restrict ω ∈ F.restrict '' G.dimerCompletionSet F η :=
      himg ▸ ⟨ω, mem_dimerCompletionSet_self hω, rfl⟩
    have hω'F (e : G.edgeSet) (he : e ∈ F) : ω' e = ω e := congrFun hr ⟨e, he⟩
    have hmem : ω' ∈ {ζ : G.edgeSet → Bool | ∀ e ∈ E, ζ e = ω e} := fun e he => by
      by_cases hF : e ∈ F
      · exact hω'F e hF
      · exact ((mem_dimerCompletionSet.1 hω').2 e hF).trans (hηω e he hF)
    rw [Finset.sum_eq_single_of_mem ω' ((Finite.mem_toFinset _).2 hω')]
    · rw [indicator_of_mem hmem, dimerWeight_congr w hω'F]
    · intro ζ hζ hne
      refine indicator_of_notMem (fun hζE => hne (funext fun e => ?_)) _
      rw [Finite.mem_toFinset] at hζ
      by_cases hF : e ∈ F
      · exact (hζE e (hE e hF e ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩)).trans
          (hω'F e hF).symm
      · exact ((mem_dimerCompletionSet.1 hζ).2 e hF).trans
          ((mem_dimerCompletionSet.1 hω').2 e hF).symm
  · rw [indicator_of_notMem (by exact hηω)]
    refine Finset.sum_eq_zero fun ζ hζ => indicator_of_notMem (fun hζE => hηω ?_) _
    rw [Finite.mem_toFinset] at hζ
    intro e he hF
    rw [← (mem_dimerCompletionSet.1 hζ).2 e hF]
    exact hζE e he

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
