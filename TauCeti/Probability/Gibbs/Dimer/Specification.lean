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
import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift
import TauCeti.MeasureTheory.Constructions.Cylinder.Partition
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

**Gibbs measures are dimer Gibbs.** Let `ν` be a Gibbs probability measure of `γ^w`, `μ` its
push-forward to the configurations, `F` a finite set of edges and `E` a finite set containing
every edge that shares a vertex with an edge of `F`. By the DLR equation at `F` and the Boltzmann
mass of a cylinder (`SimpleGraph.dimerBoltzmann_setOf_forall_mem_eq`),
`μ[ω]_E = ∫_{[ω]_{E ∖ F}} w(ω ∩ F) / Z^w_F dν`. For dimer configurations `ω`, `ω'` agreeing off
`F` the domains of integration agree, so `w(ω' ∩ F) · μ[ω]_E = w(ω ∩ F) · μ[ω']_E`: the
push-forward is dimer Gibbs in cylinder form (`SimpleGraph.isDimerGibbs_map_val`).

**Dimer Gibbs measures come from Gibbs measures.** Conversely, a dimer Gibbs measure `μ` is carried
by `𝔛(G)`, so it is the push-forward of its pull-back `ν` to `𝔛(G)`
(`SimpleGraph.IsDimerGibbs.map_comap_val`). By the DLR equations on cylinder events, and splitting
a cylinder into the cylinders of the patterns on a window `E` containing every edge that shares a
vertex with an edge of `F`, it suffices to show `∫ γ^w_F([ω]_E | η) dμ(η) = μ[ω]_E` for dimer
configurations `ω`. The partition function `Z^w_F(η)` only depends on `η` near `F`
(`SimpleGraph.dimerPartitionFunction_congr_of_isDimerConfiguration`), so the integrand is the
constant `w(ω ∩ F) / Z^w_F(ω)` on `[ω]_{E ∖ F}` and `0` off it, and the cylinder identities summed
over the completion set `Ω_F(ω)` give `w(ω ∩ F) / Z^w_F(ω) · μ[ω]_{E ∖ F} = μ[ω]_E`
(`SimpleGraph.IsDimerGibbs.ofReal_mul_measure_setOf_forall_mem_notMem_eq`,
`SimpleGraph.IsDimerGibbs.lintegral_dimerBoltzmann_setOf_forall_mem_eq`). Hence `ν` is Gibbs
(`SimpleGraph.IsDimerGibbs.isGibbs_comap_val`), and a measure is dimer Gibbs iff it is the
push-forward of a Gibbs probability measure of `γ^w`
(`SimpleGraph.isDimerGibbs_iff_exists_isGibbs`).

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

/-- Pushing `γ^w_F(· | ω)` forward along the inclusion of `𝔛(G)` into the configurations gives
the Boltzmann law. -/
theorem map_val_dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.dimerSubshift Γ hΓ) :
    (dimerKernel Γ hΓ w F ω).map Subtype.val = G.dimerBoltzmann w F ω.val := by
  have hemb : MeasurableEmbedding (Subtype.val : G.dimerSubshift Γ hΓ → _) :=
    .subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
  rw [dimerKernel_apply_eq_comap, hemb.map_comap, Subtype.range_coe,
    restrict_dimerSubshift_dimerBoltzmann]

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
  have hZ := dimerPartitionFunction_congr_of_isDimerConfiguration w F h₁ h₂ hF
  have hC (η : F → Bool) :
      s.restrict (updateFinset ω₁ F η) = s.restrict (updateFinset ω₂ F η) := by
    funext ⟨e, he⟩
    by_cases heF : e ∈ F
    · simp only [Finset.restrict_def, updateFinset_apply_of_mem heF]
    · simp only [Finset.restrict_def, updateFinset_apply_of_notMem heF, hs e he heF]
  rw [dimerBoltzmann_apply_eq_sum_updateFinset w F ω₁ (.cylinder s ht),
    dimerBoltzmann_apply_eq_sum_updateFinset w F ω₂ (.cylinder s ht)]
  refine Finset.sum_congr
    (Finset.filter_congr fun η _ => isDimerConfiguration_updateFinset_congr h₁ h₂ hF η)
    fun η _ => ?_
  simp only [indicator_apply, mem_cylinder, hC η, dimerWeight_updateFinset_congr w F ω₁ ω₂ η, hZ]

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

omit [Countable G.edgeSet] in
variable (Γ hΓ) in
/-- A dimer Gibbs measure is carried by `𝔛(G)`. -/
theorem IsDimerGibbs.ae_mem_dimerSubshift {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)}
    (hμ : G.IsDimerGibbs w μ) : ∀ᵐ ω ∂μ, ω ∈ G.dimerSubshift Γ hΓ :=
  hμ.ae_isDimerConfiguration.mono fun _ => mem_dimerSubshift.2

variable (Γ hΓ) in
/-- A dimer Gibbs measure is carried by `𝔛(G)`: pulling it back to `𝔛(G)` and pushing forward
along the inclusion gives it back. -/
theorem IsDimerGibbs.map_comap_val {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)}
    (hμ : G.IsDimerGibbs w μ) :
    (μ.comap (Subtype.val : G.dimerSubshift Γ hΓ → _)).map Subtype.val = μ :=
  (map_comap_subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe μ).trans
    (Measure.restrict_eq_self_of_ae_mem (hμ.ae_mem_dimerSubshift Γ hΓ))

variable (Γ hΓ) in
/-- The pull-back to `𝔛(G)` of a dimer Gibbs measure is a probability measure. -/
theorem IsDimerGibbs.isProbabilityMeasure_comap_val {w : G.edgeSet → ℝ}
    {μ : Measure (G.edgeSet → Bool)} (hμ : G.IsDimerGibbs w μ) :
    IsProbabilityMeasure (μ.comap (Subtype.val : G.dimerSubshift Γ hΓ → _)) := by
  have := hμ.isProbabilityMeasure
  exact (MeasurableEmbedding.subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe)
    |>.isProbabilityMeasure_comap
      ((hμ.ae_mem_dimerSubshift Γ hΓ).mono fun ω hω => ⟨⟨ω, hω⟩, rfl⟩)

variable (Γ hΓ) in
/-- **The DLR equation on a cylinder.** Let `μ` be dimer Gibbs for a positive `w`, `ω` a dimer
configuration and `E` a finite set containing every edge sharing a vertex with an edge of `F`.
Then integrating `γ^w_F([ω]_E | η)` against the pull-back of `μ` to `𝔛(G)` gives `μ[ω]_E`. -/
theorem IsDimerGibbs.lintegral_dimerBoltzmann_setOf_forall_mem_eq {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) {μ : Measure (G.edgeSet → Bool)} (hμ : G.IsDimerGibbs w μ)
    {F E : Finset G.edgeSet}
    (hE : ∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E)
    {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω) :
    ∫⁻ η, G.dimerBoltzmann w F η.val {ζ | ∀ e ∈ E, ζ e = ω e}
        ∂μ.comap (Subtype.val : G.dimerSubshift Γ hΓ → _) =
      μ {η | ∀ e ∈ E, η e = ω e} := by
  classical
  have hC : MeasurableSet {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ω e} := by
    convert SymbolicDynamics.FullShift.measurableSet_cylinder (E \ F) ω using 1
    ext θ
    simp [SymbolicDynamics.FullShift.mem_cylinder, Finset.mem_sdiff]
  calc ∫⁻ η, G.dimerBoltzmann w F η.val {ζ | ∀ e ∈ E, ζ e = ω e} ∂μ.comap Subtype.val
      = ∫⁻ η, {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ω e}.indicator
          (fun _ => ENNReal.ofReal (G.dimerWeight w F ω / G.dimerPartitionFunction w F ω))
          η.val ∂μ.comap Subtype.val := by
        refine lintegral_congr fun η => ?_
        rw [dimerBoltzmann_setOf_forall_mem_eq w hE hω (mem_dimerSubshift.1 η.property)]
        by_cases hη : η.val ∈ {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ω e}
        · rw [indicator_of_mem hη, indicator_of_mem hη,
            dimerPartitionFunction_congr_of_isDimerConfiguration w F
              (mem_dimerSubshift.1 η.property) hω
              fun e he ⟨f, hf, v, hve, hvf⟩ => hη e (hE f hf e ⟨v, hvf, hve⟩) he]
        · rw [indicator_of_notMem hη, indicator_of_notMem hη]
    _ = ∫⁻ θ, {θ : G.edgeSet → Bool | ∀ e ∈ E, e ∉ F → θ e = ω e}.indicator
          (fun _ => ENNReal.ofReal (G.dimerWeight w F ω / G.dimerPartitionFunction w F ω))
          θ ∂μ := by
        rw [← lintegral_map (measurable_const.indicator hC) measurable_subtypeVal,
          hμ.map_comap_val Γ hΓ]
    _ = μ {η | ∀ e ∈ E, η e = ω e} := by
        rw [lintegral_indicator_const hC,
          hμ.ofReal_mul_measure_setOf_forall_mem_notMem_eq hw hE hω]

variable (Γ hΓ) in
/-- **Dimer Gibbs measures come from Gibbs measures.** The pull-back to `𝔛(G)` of a dimer Gibbs
measure `μ` is a Gibbs measure of `γ^w`. -/
theorem IsDimerGibbs.isGibbs_comap_val {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    {μ : Measure (G.edgeSet → Bool)} (hμ : G.IsDimerGibbs w μ) :
    (dimerSpecification Γ hΓ hw).IsGibbs (μ.comap (Subtype.val : G.dimerSubshift Γ hΓ → _)) := by
  classical
  have := hμ.isProbabilityMeasure_comap_val Γ hΓ
  refine TauCeti.Specification.isGibbs_iff_forall_lintegral_eq.2 fun F A hA => ?_
  simp only [dimerSpecification_kernel, dimerKernel_apply_preimage_val]
  rw [← Measure.map_apply measurable_subtypeVal (MeasurableSet.of_mem_measurableCylinders hA),
    hμ.map_comap_val Γ hΓ]
  obtain ⟨s, t, -, rfl⟩ := (mem_measurableCylinders A).1 hA
  -- enlarge the window to contain every edge sharing a vertex with an edge of `F`
  set E : Finset G.edgeSet := s ∪ (G.finite_setOf_exists_mem_and_mem F).toFinset
  have hE : ∀ e ∈ F, ∀ e' : G.edgeSet, (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (e' : Sym2 V)) → e' ∈ E :=
    fun e he e' ⟨v, hve, hve'⟩ =>
      Finset.mem_union_right _ ((Finite.mem_toFinset _).2 ⟨e, he, v, hve', hve⟩)
  have hsE : s ⊆ E := Finset.subset_union_left
  -- split the cylinder into the cylinders of the patterns on `E`
  simp_rw [TauCeti.MeasureTheory.measure_cylinder_eq_sum_measure_cylinder_singleton
    (α := fun _ => Bool) hsE t]
  rw [lintegral_finsetSum _ fun p _ => (measurable_dimerBoltzmann_apply Γ hΓ w F
    (MeasurableSet.cylinder E (measurableSet_singleton p))).mono
    ((G.dimerSubshift Γ hΓ).exterior_le F) le_rfl]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ∃ ω, G.IsDimerConfiguration ω ∧ E.restrict ω = p
  · obtain ⟨ω, hω, rfl⟩ := hp
    have hcyl : SymbolicDynamics.FullShift.cylinder E ω = {ζ | ∀ e ∈ E, ζ e = ω e} :=
      Set.ext fun _ => SymbolicDynamics.FullShift.mem_cylinder
    rw [← SymbolicDynamics.FullShift.cylinder_eq_cylinder_singleton, hcyl]
    exact hμ.lintegral_dimerBoltzmann_setOf_forall_mem_eq Γ hΓ hw hE hω
  · -- no dimer configuration has the pattern `p`: both sides vanish
    have hnull : MeasureTheory.cylinder (α := fun _ : G.edgeSet => Bool) E {p} ⊆
        {ω | ¬ G.IsDimerConfiguration ω} :=
      fun η hη hD => hp ⟨η, hD, by simpa [mem_cylinder] using hη⟩
    rw [measure_mono_null hnull hμ.measure_setOf_not_isDimerConfiguration]
    exact (lintegral_congr fun η : G.dimerSubshift Γ hΓ => measure_mono_null hnull
      (dimerBoltzmann_setOf_not_isDimerConfiguration w F η.val)).trans lintegral_zero

variable (Γ hΓ) in
/-- **Dimer Gibbs measures are the push-forwards of Gibbs measures.** A measure on configurations
is dimer Gibbs for a positive weight `w` iff it is the push-forward along the inclusion of a
Gibbs probability measure of the dimer specification `γ^w` on `𝔛(G)`. -/
theorem isDimerGibbs_iff_exists_isGibbs {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    {μ : Measure (G.edgeSet → Bool)} :
    G.IsDimerGibbs w μ ↔ ∃ ν : Measure (G.dimerSubshift Γ hΓ), IsProbabilityMeasure ν ∧
      (dimerSpecification Γ hΓ hw).IsGibbs ν ∧ ν.map Subtype.val = μ := by
  refine ⟨fun hμ => ⟨_, hμ.isProbabilityMeasure_comap_val Γ hΓ, hμ.isGibbs_comap_val Γ hΓ hw,
    hμ.map_comap_val Γ hΓ⟩, ?_⟩
  rintro ⟨ν, _, hν, rfl⟩
  exact isDimerGibbs_map_val hw hν

end IsGibbs

end SimpleGraph
