/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer.Basic
public import TauCeti.Probability.Gibbs.Closed
import TauCeti.Combinatorics.SimpleGraph.Finite
import TauCeti.MeasureTheory.Constructions.Cylinder.Events
import Mathlib.Topology.LocallyConstant.Basic

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

**Quasilocality.** For dimer configurations `ω₁`, `ω₂` agreeing on the edges outside `F` that
share a vertex with an edge of `F`, and on the edges of a finite set `s` outside `F`, the laws
`γ^w_F(· | ω₁)` and `γ^w_F(· | ω₂)` give every cylinder event over `s` the same mass
(`SimpleGraph.dimerBoltzmann_cylinder_congr`): the completion sets of `ω₁` and `ω₂` have the same
restrictions to `F`, and the weights only see `F`. As a locally finite graph has only finitely
many edges sharing a vertex with an edge of `F`
(`SimpleGraph.finite_setOf_exists_mem_and_mem`), the mass of a cylinder event is a locally
constant function of `ω`, so `γ^w` is quasilocal (`SimpleGraph.isQuasilocal_dimerSpecification`).
Hence its Gibbs measures and its invariant Gibbs measures form weakly compact sets
(`SimpleGraph.isCompact_setOf_isGibbs_dimerSpecification`,
`SimpleGraph.isCompact_setOf_mem_gibbsInvariant_dimerSpecification`).

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

/-! ### Quasilocality -/

omit [G.LocallyFinite] [Countable G.edgeSet] in
/-- **Locality of the Boltzmann law.** For dimer configurations `ω₁`, `ω₂` agreeing on the edges
outside `F` that share a vertex with an edge of `F`, and on the edges of `s` outside `F`, the laws
`γ^w_F(· | ω₁)` and `γ^w_F(· | ω₂)` give every cylinder event over `s` the same mass. -/
theorem dimerBoltzmann_cylinder_congr (w : G.edgeSet → ℝ) (F s : Finset G.edgeSet)
    {t : Set (s → Bool)} (ht : MeasurableSet t) {ω₁ ω₂ : G.edgeSet → Bool}
    (h₁ : G.IsDimerConfiguration ω₁) (h₂ : G.IsDimerConfiguration ω₂)
    (hF : ∀ e ∉ F, (∃ f ∈ F, ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ω₁ e = ω₂ e)
    (hs : ∀ e ∈ s, e ∉ F → ω₁ e = ω₂ e) :
    G.dimerBoltzmann w F ω₁ (cylinder s t) = G.dimerBoltzmann w F ω₂ (cylinder s t) := by
  classical
  have hD (η : F → Bool) : G.IsDimerConfiguration (updateFinset ω₁ F η) ↔
      G.IsDimerConfiguration (updateFinset ω₂ F η) := by
    rw [isDimerConfiguration_updateFinset_iff, isDimerConfiguration_updateFinset_iff,
      image_restrict_dimerCompletionSet_eq h₁ h₂ hF]
  have hW (η : F → Bool) :
      G.dimerWeight w F (updateFinset ω₁ F η) = G.dimerWeight w F (updateFinset ω₂ F η) :=
    dimerWeight_congr w fun e he => by
      rw [updateFinset_apply_of_mem he, updateFinset_apply_of_mem he]
  have hZ : G.dimerPartitionFunction w F ω₁ = G.dimerPartitionFunction w F ω₂ := by
    rw [dimerPartitionFunction_eq_sum_updateFinset, dimerPartitionFunction_eq_sum_updateFinset]
    exact Finset.sum_congr (Finset.filter_congr fun η _ => hD η) fun η _ => hW η
  have hC (η : F → Bool) :
      s.restrict (updateFinset ω₁ F η) = s.restrict (updateFinset ω₂ F η) := by
    funext ⟨e, he⟩
    by_cases heF : e ∈ F
    · simp only [Finset.restrict_def, updateFinset_apply_of_mem heF]
    · simp only [Finset.restrict_def, updateFinset_apply_of_notMem heF, hs e he heF]
  rw [dimerBoltzmann_apply_eq_sum_updateFinset w F ω₁ (.cylinder s ht),
    dimerBoltzmann_apply_eq_sum_updateFinset w F ω₂ (.cylinder s ht)]
  refine Finset.sum_congr (Finset.filter_congr fun η _ => hD η) fun η _ => ?_
  simp only [indicator_apply, mem_cylinder, hC η, hW η, hZ]

variable (Γ hΓ) in
/-- The mass of a set under `γ^w_F(· | ω)` on `𝔛(G)` is the Boltzmann mass of the set of
configurations it is the trace of. -/
theorem dimerKernel_apply_preimage_val (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.dimerSubshift Γ hΓ) (A : Set (G.edgeSet → Bool)) :
    dimerKernel Γ hΓ w F ω (Subtype.val ⁻¹' A) = G.dimerBoltzmann w F ω.val A := by
  rw [dimerKernel_apply, image_preimage_eq_inter_range, Subtype.range_coe_subtype,
    measure_inter_conull]
  simpa [compl_ofPred] using dimerBoltzmann_setOf_not_isDimerConfiguration w F ω.val

variable (Γ hΓ) in
/-- **The dimer specification is quasilocal.** The mass `γ^w_F(C | ω)` of a cylinder event `C`
depends on `ω` only through the finitely many edges of `C` and the edges sharing a vertex with an
edge of `F`, so it is a locally constant, hence continuous, function of `ω`. -/
theorem isQuasilocal_dimerSpecification {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    (dimerSpecification Γ hΓ hw).IsQuasilocal := by
  refine TauCeti.Specification.isQuasilocal_iff.2 fun F s t ht => ?_
  simp_rw [dimerSpecification_kernel, dimerKernel_apply_preimage_val]
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun ω => ?_)
  have hE := (G.finite_setOf_exists_mem_and_mem F).union s.finite_toSet
  have hev : ∀ e ∈ {e : G.edgeSet | ∃ f ∈ F, ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)} ∪ ↑s,
      ∀ᶠ ω' : G.dimerSubshift Γ hΓ in nhds ω, ω'.val e = ω.val e := fun e _ => by
    have hc : Continuous fun ω' : G.dimerSubshift Γ hΓ => ω'.val e :=
      (continuous_apply e).comp continuous_subtypeVal
    simpa using hc.continuousAt.eventually_mem ((isOpen_discrete {ω.val e}).mem_nhds rfl)
  filter_upwards [(Filter.eventually_all_finite hE).2 hev] with ω' hω'
  exact dimerBoltzmann_cylinder_congr w F s ht (mem_dimerSubshift.1 ω'.property)
    (mem_dimerSubshift.1 ω.property) (fun e _ he => hω' e (Or.inl he))
    fun e he _ => hω' e (Or.inr he)

variable (Γ hΓ) in
/-- The Gibbs probability measures of the dimer specification form a weakly compact set. -/
theorem isCompact_setOf_isGibbs_dimerSpecification {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    IsCompact {μ : ProbabilityMeasure (G.dimerSubshift Γ hΓ) |
      (dimerSpecification Γ hΓ hw).IsGibbs (μ : Measure (G.dimerSubshift Γ hΓ))} :=
  TauCeti.Specification.isCompact_setOf_isGibbs (isQuasilocal_dimerSpecification Γ hΓ hw)

variable (Γ hΓ) in
/-- The invariant Gibbs probability measures of the dimer specification form a weakly compact
set. -/
theorem isCompact_setOf_mem_gibbsInvariant_dimerSpecification {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) :
    IsCompact {μ : ProbabilityMeasure (G.dimerSubshift Γ hΓ) |
      (μ : Measure (G.dimerSubshift Γ hΓ)) ∈ (dimerSpecification Γ hΓ hw).gibbsInvariant} :=
  TauCeti.Specification.isCompact_setOf_mem_gibbsInvariant
    (isQuasilocal_dimerSpecification Γ hΓ hw)

end Specification

end SimpleGraph
