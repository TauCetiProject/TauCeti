/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer.Basic
public import TauCeti.Probability.Gibbs.Specification
import TauCeti.MeasureTheory.Constructions.Cylinder.Events

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
  measure carried by dimer configurations (`SimpleGraph.restrict_dimerSubshift_dimerBoltzmann`);
* it is proper (`SimpleGraph.isProper_dimerKernel`), since every member of the completion set
  `Ω_F(ω)` agrees with `ω` off `F`;
* the family is consistent, `γ^w_Λ ∘ γ^w_Δ = γ^w_Δ` for `Λ ⊆ Δ`
  (`SimpleGraph.lintegral_dimerBoltzmann_dimerBoltzmann`, `SimpleGraph.dimerKernel_comp_eq`):
  resampling `Λ` inside a configuration drawn from `γ^w_Δ(· | ω)` changes neither its weight on
  `Δ ∖ Λ` nor the partition function of `Λ`, and the weights on `Λ` sum to that partition
  function.

The specification does not change under a gauge transformation of the weight
(`SimpleGraph.dimerSpecification_gaugeWeight`).

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

/-- The Boltzmann law `γ^w_F(· | ω)` is carried by the dimer configurations: restricting it to
`𝔛(G)` does not change it. -/
theorem restrict_dimerSubshift_dimerBoltzmann (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.edgeSet → Bool) :
    (G.dimerBoltzmann w F ω).restrict (G.dimerSubshift Γ hΓ) = G.dimerBoltzmann w F ω := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  simpa using dimerBoltzmann_setOf_not_isDimerConfiguration w F ω

/-- Integrating against `γ^w_F(· | ω)` on `𝔛(G)` is integrating against the Boltzmann law. -/
theorem lintegral_dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.dimerSubshift Γ hΓ) (f : (G.edgeSet → Bool) → ℝ≥0∞) :
    ∫⁻ x, f x.val ∂dimerKernel Γ hΓ w F ω = ∫⁻ x, f x ∂G.dimerBoltzmann w F ω.val := by
  have h := lintegral_subtype_comap (μ := G.dimerBoltzmann w F ω.val)
    (G.dimerSubshift Γ hΓ).measurableSet_coe f
  rwa [restrict_dimerSubshift_dimerBoltzmann] at h

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

end SimpleGraph
