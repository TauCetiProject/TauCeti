/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer.Basic
public import TauCeti.Probability.Gibbs.Specification
import TauCeti.MeasureTheory.Constructions.Cylinder.Events
import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift

/-!
# The dimer specification

Let `G` be a locally finite graph with countably many edges, `𝔛(G)` its subshift of dimer
configurations (`SimpleGraph.dimerSubshift`) and `w` a positive weight on the edges. The dimer
Boltzmann laws `γ^w_F(· | ω)` (`SimpleGraph.dimerBoltzmann`), restricted to `𝔛(G)`
(`SimpleGraph.dimerKernel`), form a specification on `𝔛(G)` (`SimpleGraph.dimerSpecification`):

* the kernel `γ^w_F` is measurable for the exterior σ-algebra of `F`: its masses are finite sums,
  over the configurations `η` on `F`, of measurable functions of the gluing of `η` to `ω` off `F`
  (`SimpleGraph.dimerBoltzmann_apply_eq_sum_updateFinset`,
  `TauCeti.Subshift.measurable_updateFinset_exterior`,
  `SimpleGraph.measurable_dimerBoltzmann_apply`);
* it is Markov (`SimpleGraph.isMarkovKernel_dimerKernel`), since `γ^w_F(· | ω)` is a probability
  measure carried by dimer configurations;
* it is proper (`SimpleGraph.isProper_dimerKernel`), since every member of the completion set
  `Ω_F(ω)` agrees with `ω` off `F`;
* the family is consistent, `γ^w_Λ ∘ γ^w_Δ = γ^w_Δ` for `Λ ⊆ Δ`
  (`SimpleGraph.lintegral_dimerBoltzmann_dimerBoltzmann`, `SimpleGraph.dimerKernel_comp_eq`):
  resampling `Λ` inside a configuration drawn from `γ^w_Δ(· | ω)` changes neither its weight on
  `Δ ∖ Λ` nor the partition function of `Λ`, and the weights on `Λ` sum to that partition
  function.

The specification does not change under a gauge transformation of the weight
(`SimpleGraph.dimerSpecification_gaugeWeight`).

**Gibbs measures are dimer Gibbs.** Let `ν` be a Gibbs probability measure of `γ^w`, `μ` its
push-forward to the configurations, `F` a finite set of edges and `E` a finite set containing
every edge that shares a vertex with an edge of `F`. By the DLR equation at `F` and the Boltzmann
mass of a cylinder (`SimpleGraph.dimerBoltzmann_setOf_forall_mem_eq`),
`μ[ω]_E = ∫_{[ω]_{E ∖ F}} w(ω ∩ F) / Z^w_F dν`. For dimer configurations `ω`, `ω'` agreeing off
`F` the domains of integration agree, so `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E`: the
push-forward is dimer Gibbs in cylinder form (`SimpleGraph.isDimerGibbs_map_val`).

## References

* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  Section 2.2.1.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Section 5.1.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### The specification -/

section Specification

variable [G.LocallyFinite] [Countable G.edgeSet] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
  {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e}

variable (Γ hΓ) in
/-- The mass `γ^w_F(s | ω)` of a measurable set is measurable in `ω ∈ 𝔛(G)` for the exterior
σ-algebra of `F`. -/
theorem measurable_dimerBoltzmann_apply (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    {s : Set (G.edgeSet → Bool)} (hs : MeasurableSet s) :
    Measurable[(G.dimerSubshift Γ hΓ).exterior F]
      fun ω : G.dimerSubshift Γ hΓ => G.dimerBoltzmann w F ω.val s := by
  classical
  let : MeasurableSpace (G.dimerSubshift Γ hΓ) := (G.dimerSubshift Γ hΓ).exterior F
  have hglue := (G.dimerSubshift Γ hΓ).measurable_updateFinset_exterior F
  have hD (η : F → Bool) :
      MeasurableSet {ω : G.dimerSubshift Γ hΓ | G.IsDimerConfiguration (updateFinset ω.val F η)} :=
    hglue η measurableSet_setOf_isDimerConfiguration
  have hZ : Measurable fun ω : G.dimerSubshift Γ hΓ => G.dimerPartitionFunction w F ω.val := by
    simp_rw [dimerPartitionFunction_eq_sum_updateFinset, Finset.sum_filter]
    exact Finset.measurable_sum _ fun η _ => Measurable.ite (hD η)
      ((measurable_dimerWeight w F).comp (hglue η)) measurable_const
  simp_rw [dimerBoltzmann_apply_eq_sum_updateFinset w F _ hs, Finset.sum_filter]
  refine Finset.measurable_sum _ fun η _ => Measurable.ite (hD η) ?_ measurable_const
  refine Measurable.indicator ?_ (hglue η hs)
  exact (((measurable_dimerWeight w F).comp (hglue η)).div hZ).ennreal_ofReal

variable (Γ hΓ) in
/-- The kernel `γ^w_F` of the dimer specification: the Boltzmann law `γ^w_F(· | ω)` of a dimer
configuration `ω`, as a measure on `𝔛(G)`, measurable in `ω` for the exterior σ-algebra of
`F`. -/
def dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) :
    Kernel[(G.dimerSubshift Γ hΓ).exterior F] (G.dimerSubshift Γ hΓ) (G.dimerSubshift Γ hΓ) :=
  @Kernel.mk _ _ ((G.dimerSubshift Γ hΓ).exterior F) _
    (fun ω => (G.dimerBoltzmann w F ω.val).comap Subtype.val) <| by
    refine Measure.measurable_of_measurable_coe (mα := Subtype.instMeasurableSpace)
      (mβ := (G.dimerSubshift Γ hΓ).exterior F) _ fun C hC => ?_
    have hemb : MeasurableEmbedding (Subtype.val : G.dimerSubshift Γ hΓ → _) :=
      .subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
    simp_rw [hemb.comap_apply]
    exact measurable_dimerBoltzmann_apply Γ hΓ w F (hemb.measurableSet_image' hC)

/-- The measure `γ^w_F(· | ω)` on `𝔛(G)` is the pullback of the Boltzmann law along the inclusion
of `𝔛(G)` into the configurations. This holds by definition of `SimpleGraph.dimerKernel`. -/
theorem dimerKernel_apply_eq_comap (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.dimerSubshift Γ hΓ) :
    dimerKernel Γ hΓ w F ω = (G.dimerBoltzmann w F ω.val).comap Subtype.val :=
  (rfl)

/-- The kernel `γ^w_F` gives a set `C ⊆ 𝔛(G)` the Boltzmann mass of its image. -/
@[simp]
theorem dimerKernel_apply (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.dimerSubshift Γ hΓ)
    (C : Set (G.dimerSubshift Γ hΓ)) :
    dimerKernel Γ hΓ w F ω C = G.dimerBoltzmann w F ω.val (Subtype.val '' C) := by
  rw [dimerKernel_apply_eq_comap]
  exact (MeasurableEmbedding.subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe).comap_apply _ _

/-- Integrating against `γ^w_F(· | ω)` on `𝔛(G)` is integrating against the Boltzmann law. -/
theorem lintegral_dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.dimerSubshift Γ hΓ) (f : (G.edgeSet → Bool) → ℝ≥0∞) :
    ∫⁻ x, f x.val ∂dimerKernel Γ hΓ w F ω = ∫⁻ x, f x ∂G.dimerBoltzmann w F ω.val := by
  have h := lintegral_subtype_comap (μ := G.dimerBoltzmann w F ω.val)
    (G.dimerSubshift Γ hΓ).measurableSet_coe f
  refine h.trans (congrArg (lintegral · f) (Measure.restrict_eq_self_of_ae_mem ?_))
  rw [ae_iff]
  simpa using dimerBoltzmann_setOf_not_isDimerConfiguration w F ω.val

variable (Γ hΓ) in
/-- For a positive weight, the kernel `γ^w_F` is Markov. -/
theorem isMarkovKernel_dimerKernel {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset G.edgeSet) : IsMarkovKernel (dimerKernel Γ hΓ w F) := by
  refine ⟨fun ω => ⟨?_⟩⟩
  have := isProbabilityMeasure_dimerBoltzmann hw F (mem_dimerSubshift.1 ω.property)
  rw [dimerKernel_apply, image_univ, Subtype.range_coe]
  refine (prob_compl_eq_zero_iff (G.dimerSubshift Γ hΓ).measurableSet_coe).1 ?_
  rw [coe_dimerSubshift, compl_ofPred]
  exact dimerBoltzmann_setOf_not_isDimerConfiguration w F ω.val

variable (Γ hΓ) in
/-- The kernel `γ^w_F` is proper: every member of the completion set agrees with `ω` off `F`, so
an event of the exterior σ-algebra of `F` holds for it exactly when it holds for `ω`. -/
theorem isProper_dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) :
    (dimerKernel Γ hΓ w F).IsProper := by
  have hemb := MeasurableEmbedding.subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
  refine (Kernel.isProper_iff_inter_eq_indicator_mul
    ((G.dimerSubshift Γ hΓ).exterior_le F)).2 fun A hA B hB ω => ?_
  rw [TauCeti.Subshift.exterior_def, MeasurableSpace.measurableSet_comap] at hB
  obtain ⟨B', hB', rfl⟩ := hB
  have hdep := hB'.dependsOn_of_cylinderEvents
  have hA' := hemb.measurableSet_image' hA
  rw [dimerKernel_apply, dimerKernel_apply, image_inter_preimage,
    dimerBoltzmann_apply w F _ (s := Subtype.val '' A ∩ B')
      (by exact hA'.inter (cylinderEvents_le_pi _ hB')),
    dimerBoltzmann_apply w F _ (s := Subtype.val '' A) (by exact hA'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω' hω' => ?_
  simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
  have hiff : (ω' ∈ B') = (ω.val ∈ B') := hdep fun e he => hω'.2 e he
  by_cases hωB : ω.val ∈ B'
  · have hω'B : ω' ∈ B' := hiff ▸ hωB
    rw [indicator_of_mem (mem_preimage.2 hωB), Pi.one_apply, one_mul]
    by_cases hω'A : ω' ∈ Subtype.val '' A
    · rw [indicator_of_mem hω'A, indicator_of_mem (mem_inter hω'A hω'B)]
    · rw [indicator_of_notMem hω'A, indicator_of_notMem fun h => hω'A (mem_of_mem_inter_left h)]
  · have hω'B : ω' ∉ B' := hiff ▸ hωB
    rw [indicator_of_notMem (fun h => hωB (mem_preimage.1 h)), zero_mul,
      indicator_of_notMem fun h => hω'B (mem_of_mem_inter_right h)]

variable (Γ hΓ) in
/-- **Consistency of the dimer kernels**: `γ^w_Λ ∘ γ^w_Δ = γ^w_Δ` for `Λ ⊆ Δ`. -/
theorem dimerKernel_comp_eq {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) {Λ Δ : Finset G.edgeSet}
    (h : Λ ⊆ Δ) :
    (dimerKernel Γ hΓ w Λ).comap id
        (measurable_id'' ((G.dimerSubshift Γ hΓ).exterior_le Λ)) ∘ₖ dimerKernel Γ hΓ w Δ =
      dimerKernel Γ hΓ w Δ := by
  have hemb := MeasurableEmbedding.subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
  ext ω A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  simp only [Kernel.comap_apply, id, dimerKernel_apply]
  rw [lintegral_dimerKernel w Δ ω fun y => G.dimerBoltzmann w Λ y (Subtype.val '' A),
    lintegral_dimerBoltzmann_dimerBoltzmann hw h _ (A := Subtype.val '' A)
      (by exact hemb.measurableSet_image' hA)]

variable (Γ hΓ) in
/-- **The dimer specification** `γ^w` of a positive weight `w` on the subshift `𝔛(G)` of dimer
configurations: its kernel at a finite set `F` is the Boltzmann law `γ^w_F(· | ω)`. -/
def dimerSpecification {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    TauCeti.Specification (G.dimerSubshift Γ hΓ) where
  kernel F := dimerKernel Γ hΓ w F
  isMarkovKernel F := isMarkovKernel_dimerKernel Γ hΓ hw F
  isProper F := isProper_dimerKernel Γ hΓ w F
  comp_eq _ _ h := dimerKernel_comp_eq Γ hΓ hw h

@[simp]
theorem dimerSpecification_kernel {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) (F : Finset G.edgeSet) :
    (dimerSpecification Γ hΓ hw).kernel F = dimerKernel Γ hΓ w F :=
  (rfl)

/-- **Gauge invariance of the dimer specification.** For a positive `g`, the gauge transform
`w(uv) g(u) g(v)` of the weight has the same specification. -/
theorem dimerSpecification_gaugeWeight {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) {g : V → ℝ}
    (hg : ∀ v, 0 < g v) :
    dimerSpecification Γ hΓ (gaugeWeight_pos hw hg) = dimerSpecification Γ hΓ hw := by
  ext F ω A _
  simp only [dimerSpecification_kernel, dimerKernel_apply, dimerBoltzmann_gaugeWeight w hg]

end Specification

/-! ### Gibbs measures of the dimer specification -/

section IsGibbs

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

end IsGibbs

end SimpleGraph
