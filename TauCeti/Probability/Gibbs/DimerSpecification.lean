/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer
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

/-! ### Weights and partition functions -/

/-- The weight on `F` of a configuration depends only on its values on `F`. -/
theorem dimerWeight_congr (w : G.edgeSet → ℝ) {F : Finset G.edgeSet} {ω ω' : G.edgeSet → Bool}
    (h : ∀ e ∈ F, ω e = ω' e) : G.dimerWeight w F ω = G.dimerWeight w F ω' := by
  simp only [dimerWeight_def]
  exact Finset.prod_congr (Finset.filter_congr fun e he => by rw [h e he]) fun _ _ => rfl

/-- For `Λ ⊆ Δ`, the weight on `Δ` is the product of the weights on `Λ` and on `Δ ∖ Λ`. -/
theorem dimerWeight_eq_mul_sdiff [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    {Λ Δ : Finset G.edgeSet} (h : Λ ⊆ Δ) (ω : G.edgeSet → Bool) :
    G.dimerWeight w Δ ω = G.dimerWeight w Λ ω * G.dimerWeight w (Δ \ Λ) ω := by
  simp only [dimerWeight_def, Finset.prod_filter]
  rw [mul_comm, Finset.prod_sdiff h]

/-- The partition function of `F` at `ω` depends on `ω` only off `F`. -/
theorem dimerPartitionFunction_congr (w : G.edgeSet → ℝ) {F : Finset G.edgeSet}
    {ω₁ ω₂ : G.edgeSet → Bool} (h : ∀ e ∉ F, ω₁ e = ω₂ e) :
    G.dimerPartitionFunction w F ω₁ = G.dimerPartitionFunction w F ω₂ := by
  simp only [dimerPartitionFunction_def, dimerCompletionSet_congr h]

/-! ### Completion sets as gluings -/

/-- A sum over the completion set `Ω_F(ω)` is a sum over the configurations `η` on `F` whose
gluing to `ω` off `F` is a dimer configuration. -/
theorem sum_dimerCompletionSet_eq_sum_updateFinset [DecidableEq G.edgeSet] {M : Type*}
    [AddCommMonoid M] (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) (f : (G.edgeSet → Bool) → M)
    [DecidablePred fun η : F → Bool => G.IsDimerConfiguration (updateFinset ω F η)] :
    ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, f ω' =
      ∑ η with G.IsDimerConfiguration (updateFinset ω F η), f (updateFinset ω F η) := by
  symm
  refine Finset.sum_nbij' (fun η => updateFinset ω F η) (fun ω' => F.restrict ω') ?_ ?_ ?_ ?_
    fun _ _ => rfl
  · intro η hη
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet]
    exact ⟨hη, fun e he => updateFinset_apply_of_notMem he⟩
  · intro ω' hω'
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
    have hglue : updateFinset ω F (F.restrict ω') = ω' := by
      ext e
      by_cases he : e ∈ F
      · rw [updateFinset_apply_of_mem he, Finset.restrict_def]
      · rw [updateFinset_apply_of_notMem he, hω'.2 e he]
    simpa [hglue] using hω'.1
  · intro η _
    exact restrict_updateFinset ω η
  · intro ω' hω'
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
    ext e
    by_cases he : e ∈ F
    · rw [updateFinset_apply_of_mem he, Finset.restrict_def]
    · rw [updateFinset_apply_of_notMem he, hω'.2 e he]

/-- **The Boltzmann masses as a sum over configurations on `F`.** The mass of a measurable set `s`
under `γ^w_F(· | ω)` is the sum, over the configurations `η` on `F` whose gluing `ω_η` to `ω` off
`F` is a dimer configuration, of `w(ω_η ∩ F) / Z^w_F(ω)` times `1_s(ω_η)`. -/
theorem dimerBoltzmann_apply_eq_sum_updateFinset [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) {s : Set (G.edgeSet → Bool)}
    (hs : MeasurableSet s)
    [DecidablePred fun η : F → Bool => G.IsDimerConfiguration (updateFinset ω F η)] :
    G.dimerBoltzmann w F ω s = ∑ η with G.IsDimerConfiguration (updateFinset ω F η),
      s.indicator (fun _ => ENNReal.ofReal (G.dimerWeight w F (updateFinset ω F η) /
        G.dimerPartitionFunction w F ω)) (updateFinset ω F η) := by
  rw [dimerBoltzmann_apply w F ω hs, sum_dimerCompletionSet_eq_sum_updateFinset]

/-- The partition function as a sum over configurations on `F`. -/
theorem dimerPartitionFunction_eq_sum_updateFinset [DecidableEq G.edgeSet] (w : G.edgeSet → ℝ)
    (F : Finset G.edgeSet) (ω : G.edgeSet → Bool)
    [DecidablePred fun η : F → Bool => G.IsDimerConfiguration (updateFinset ω F η)] :
    G.dimerPartitionFunction w F ω = ∑ η with G.IsDimerConfiguration (updateFinset ω F η),
      G.dimerWeight w F (updateFinset ω F η) := by
  rw [dimerPartitionFunction_def, sum_dimerCompletionSet_eq_sum_updateFinset]

/-! ### Measurability -/

/-- On a locally finite graph with countably many edges, the dimer configurations form a
measurable set. -/
theorem measurableSet_setOf_isDimerConfiguration [G.LocallyFinite] [Countable G.edgeSet] :
    MeasurableSet {ω : G.edgeSet → Bool | G.IsDimerConfiguration ω} :=
  isClosed_setOf_isDimerConfiguration.measurableSet

/-- The Boltzmann law `γ^w_F(· | ω)` is carried by dimer configurations. -/
theorem dimerBoltzmann_setOf_not_isDimerConfiguration [G.LocallyFinite] [Countable G.edgeSet]
    (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerBoltzmann w F ω {ω' | ¬ G.IsDimerConfiguration ω'} = 0 := by
  have h := dimerBoltzmann_apply w F ω measurableSet_setOf_isDimerConfiguration.compl
  rw [compl_ofPred] at h
  rw [h]
  refine Finset.sum_eq_zero fun ω' hω' => indicator_of_notMem ?_ _
  simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
  simpa using hω'.1

/-! ### Consistency -/

/-- The Boltzmann law integrates a function as the weighted sum of its values on the completion
set. -/
theorem lintegral_dimerBoltzmann [Countable G.edgeSet] (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.edgeSet → Bool) (f : (G.edgeSet → Bool) → ℝ≥0∞) :
    ∫⁻ ω', f ω' ∂G.dimerBoltzmann w F ω = ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset,
      ENNReal.ofReal (G.dimerWeight w F ω' / G.dimerPartitionFunction w F ω) * f ω' := by
  rw [dimerBoltzmann_def, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- For `Λ ⊆ Δ` and `ω'` in the completion set of `ω` at `Δ`, resampling `Λ` inside the Boltzmann
law of `Δ` gives back the Boltzmann mass of `ω'`:
`∑_{ω'' ∈ Ω_Λ(ω')} γ^w_Δ({ω''} | ω) γ^w_Λ({ω'} | ω'') = γ^w_Δ({ω'} | ω)`. -/
private theorem sum_dimerCompletionSet_mul_eq {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    {Λ Δ : Finset G.edgeSet} (h : Λ ⊆ Δ) (ω : G.edgeSet → Bool) {ω' : G.edgeSet → Bool}
    (hω' : G.IsDimerConfiguration ω') :
    ∑ ω'' ∈ (G.finite_dimerCompletionSet Λ ω').toFinset,
        ENNReal.ofReal (G.dimerWeight w Δ ω'' / G.dimerPartitionFunction w Δ ω) *
          ENNReal.ofReal (G.dimerWeight w Λ ω' / G.dimerPartitionFunction w Λ ω'') =
      ENNReal.ofReal (G.dimerWeight w Δ ω' / G.dimerPartitionFunction w Δ ω) := by
  classical
  set ZΔ := G.dimerPartitionFunction w Δ ω
  set K := G.dimerWeight w (Δ \ Λ) ω'
  set a := G.dimerWeight w Λ ω'
  have hZΛ := dimerPartitionFunction_pos hw Λ hω'
  have hZΔ : 0 ≤ ZΔ := by
    simp only [ZΔ, dimerPartitionFunction_def]
    exact Finset.sum_nonneg fun _ _ => (dimerWeight_pos hw Δ _).le
  have hc : 0 ≤ K / ZΔ * (a / G.dimerPartitionFunction w Λ ω') :=
    mul_nonneg (div_nonneg (dimerWeight_pos hw _ _).le hZΔ)
      (div_nonneg (dimerWeight_pos hw _ _).le hZΛ.le)
  calc ∑ ω'' ∈ (G.finite_dimerCompletionSet Λ ω').toFinset,
        ENNReal.ofReal (G.dimerWeight w Δ ω'' / ZΔ) *
          ENNReal.ofReal (a / G.dimerPartitionFunction w Λ ω'')
      = ∑ ω'' ∈ (G.finite_dimerCompletionSet Λ ω').toFinset,
          ENNReal.ofReal (G.dimerWeight w Λ ω'' *
            (K / ZΔ * (a / G.dimerPartitionFunction w Λ ω'))) := by
        refine Finset.sum_congr rfl fun ω'' hω'' => ?_
        simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω''
        rw [← ENNReal.ofReal_mul (div_nonneg (dimerWeight_pos hw _ _).le hZΔ),
          dimerPartitionFunction_congr w hω''.2, dimerWeight_eq_mul_sdiff w h,
          dimerWeight_congr w (F := Δ \ Λ) (ω' := ω') fun e he =>
            hω''.2 e (Finset.mem_sdiff.1 he).2]
        simp only [K]
        ring_nf
    _ = ENNReal.ofReal (G.dimerPartitionFunction w Λ ω' *
          (K / ZΔ * (a / G.dimerPartitionFunction w Λ ω'))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun ω'' _ =>
            mul_nonneg (dimerWeight_pos hw _ _).le hc, ← Finset.sum_mul,
          dimerPartitionFunction_def]
    _ = ENNReal.ofReal (G.dimerWeight w Δ ω' / ZΔ) := by
        rw [dimerWeight_eq_mul_sdiff w h]
        congr 1
        simp only [K, a]
        field_simp

/-- **Consistency of the Boltzmann laws.** For `Λ ⊆ Δ`, resampling `Λ` from `γ^w_Λ` inside a
configuration drawn from `γ^w_Δ(· | ω)` gives `γ^w_Δ(· | ω)` back:
`∫ γ^w_Λ(A | ω'') dγ^w_Δ(ω'' | ω) = γ^w_Δ(A | ω)`. -/
theorem lintegral_dimerBoltzmann_dimerBoltzmann [Countable G.edgeSet] {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) {Λ Δ : Finset G.edgeSet} (h : Λ ⊆ Δ) (ω : G.edgeSet → Bool)
    {A : Set (G.edgeSet → Bool)} (hA : MeasurableSet A) :
    ∫⁻ ω'', G.dimerBoltzmann w Λ ω'' A ∂G.dimerBoltzmann w Δ ω = G.dimerBoltzmann w Δ ω A := by
  rw [lintegral_dimerBoltzmann, dimerBoltzmann_apply w Δ ω hA]
  simp_rw [dimerBoltzmann_apply w Λ _ hA, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := (G.finite_dimerCompletionSet Δ ω).toFinset)
    (s' := fun ω' => (G.finite_dimerCompletionSet Λ ω').toFinset) ?_]
  · refine Finset.sum_congr rfl fun ω' hω' => ?_
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω'
    by_cases hA' : ω' ∈ A
    · simp only [indicator_of_mem hA']
      exact sum_dimerCompletionSet_mul_eq hw h ω hω'.1
    · simp [indicator_of_notMem hA']
  · intro ω'' ω'
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, fun e he => (h4 e he).symm⟩, h3,
        fun e he => (h4 e fun hΛ => he (h hΛ)).trans (h2 e he)⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, fun e he => (h2 e fun hΛ => he (h hΛ)).trans (h4 e he)⟩, h3,
        fun e he => (h2 e he).symm⟩

/-! ### The specification -/

section Specification

variable [G.LocallyFinite] [Countable G.edgeSet] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]
  {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e}

omit [G.LocallyFinite] [Countable G.edgeSet] in
/-- The weight on a finite set `F` is a measurable function of the configuration. -/
theorem measurable_dimerWeight (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) :
    Measurable (G.dimerWeight w F) := by
  simp_rw [funext (dimerWeight_def w F), Finset.prod_filter]
  exact Finset.measurable_prod _ fun e _ => Measurable.ite
    (measurableSet_eq_fun (measurable_pi_apply e) measurable_const) measurable_const
    measurable_const

/-- The subshift of dimer configurations is a measurable set. -/
theorem measurableSet_dimerSubshift :
    MeasurableSet (G.dimerSubshift Γ hΓ : Set (G.edgeSet → Bool)) := by
  have h : (G.dimerSubshift Γ hΓ : Set (G.edgeSet → Bool)) = {ω | G.IsDimerConfiguration ω} :=
    Set.ext fun _ => SetLike.mem_coe.trans mem_dimerSubshift
  rw [h]
  exact measurableSet_setOf_isDimerConfiguration

omit [Countable G.edgeSet] in
/-- The gluing `ω ↦ ω_η` of a fixed configuration `η` on `F` to `ω` off `F` is measurable for the
exterior σ-algebra of `F`. -/
theorem measurable_updateFinset_exterior [DecidableEq G.edgeSet] (F : Finset G.edgeSet)
    (η : F → Bool) :
    Measurable[(G.dimerSubshift Γ hΓ).exterior F]
      fun ω : G.dimerSubshift Γ hΓ => updateFinset ω.val F η := by
  refine @measurable_pi_iff _ _ _ ((G.dimerSubshift Γ hΓ).exterior F) _ _ |>.2 fun e => ?_
  by_cases he : e ∈ F
  · simp only [updateFinset_apply_of_mem he]
    exact @measurable_const _ _ _ ((G.dimerSubshift Γ hΓ).exterior F) _
  · simp only [updateFinset_apply_of_notMem he]
    exact (G.dimerSubshift Γ hΓ).measurable_apply_exterior (by simpa using he)

/-- The mass `γ^w_F(s | ω)` of a measurable set is measurable in `ω ∈ 𝔛(G)` for the exterior
σ-algebra of `F`. -/
theorem measurable_dimerBoltzmann_apply (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    {s : Set (G.edgeSet → Bool)} (hs : MeasurableSet s) :
    Measurable[(G.dimerSubshift Γ hΓ).exterior F]
      fun ω : G.dimerSubshift Γ hΓ => G.dimerBoltzmann w F ω.val s := by
  classical
  let : MeasurableSpace (G.dimerSubshift Γ hΓ) := (G.dimerSubshift Γ hΓ).exterior F
  have hD (η : F → Bool) :
      MeasurableSet {ω : G.dimerSubshift Γ hΓ | G.IsDimerConfiguration (updateFinset ω.val F η)} :=
    measurable_updateFinset_exterior F η measurableSet_setOf_isDimerConfiguration
  have hZ : Measurable fun ω : G.dimerSubshift Γ hΓ => G.dimerPartitionFunction w F ω.val := by
    simp_rw [dimerPartitionFunction_eq_sum_updateFinset, Finset.sum_filter]
    exact Finset.measurable_sum _ fun η _ => Measurable.ite (hD η)
      ((measurable_dimerWeight w F).comp (measurable_updateFinset_exterior F η)) measurable_const
  simp_rw [dimerBoltzmann_apply_eq_sum_updateFinset w F _ hs, Finset.sum_filter]
  refine Finset.measurable_sum _ fun η _ => Measurable.ite (hD η) ?_ measurable_const
  refine Measurable.indicator ?_ (measurable_updateFinset_exterior F η hs)
  exact (((measurable_dimerWeight w F).comp (measurable_updateFinset_exterior F η)).div
    hZ).ennreal_ofReal

/-- The kernel `γ^w_F` of the dimer specification: the Boltzmann law `γ^w_F(· | ω)` of a dimer
configuration `ω`, as a measure on `𝔛(G)`, measurable in `ω` for the exterior σ-algebra of
`F`. -/
def dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) :
    Kernel[(G.dimerSubshift Γ hΓ).exterior F] (G.dimerSubshift Γ hΓ) (G.dimerSubshift Γ hΓ) :=
  @Kernel.mk _ _ ((G.dimerSubshift Γ hΓ).exterior F) _
    (fun ω => (G.dimerBoltzmann w F ω.val).comap Subtype.val) <| by
    refine Measure.measurable_of_measurable_coe (mα := Subtype.instMeasurableSpace)
      (mβ := (G.dimerSubshift Γ hΓ).exterior F) _ fun C hC => ?_
    simp_rw [(MeasurableEmbedding.subtypeVal measurableSet_dimerSubshift).comap_apply]
    exact measurable_dimerBoltzmann_apply w F
      ((MeasurableEmbedding.subtypeVal measurableSet_dimerSubshift).measurableSet_image' hC)

/-- The kernel `γ^w_F` gives a set `C ⊆ 𝔛(G)` the Boltzmann mass of its image. -/
theorem dimerKernel_apply (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) (ω : G.dimerSubshift Γ hΓ)
    (C : Set (G.dimerSubshift Γ hΓ)) :
    dimerKernel w F ω C = G.dimerBoltzmann w F ω.val (Subtype.val '' C) := by
  rw [show dimerKernel w F ω = (G.dimerBoltzmann w F ω.val).comap Subtype.val from rfl]
  exact (MeasurableEmbedding.subtypeVal measurableSet_dimerSubshift).comap_apply _ _

/-- Integrating against `γ^w_F(· | ω)` on `𝔛(G)` is integrating against the Boltzmann law. -/
theorem lintegral_dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet)
    (ω : G.dimerSubshift Γ hΓ) (f : (G.edgeSet → Bool) → ℝ≥0∞) :
    ∫⁻ x, f x.val ∂dimerKernel w F ω = ∫⁻ x, f x ∂G.dimerBoltzmann w F ω.val := by
  have h := lintegral_subtype_comap (μ := G.dimerBoltzmann w F ω.val)
    (measurableSet_dimerSubshift (Γ := Γ) (hΓ := hΓ)) f
  refine h.trans (congrArg (lintegral · f) (Measure.restrict_eq_self_of_ae_mem ?_))
  rw [ae_iff]
  simpa using dimerBoltzmann_setOf_not_isDimerConfiguration w F ω.val

/-- For a positive weight, the kernel `γ^w_F` is Markov. -/
theorem isMarkovKernel_dimerKernel {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset G.edgeSet) : IsMarkovKernel (dimerKernel (Γ := Γ) (hΓ := hΓ) w F) := by
  refine ⟨fun ω => ⟨?_⟩⟩
  have := isProbabilityMeasure_dimerBoltzmann hw F (mem_dimerSubshift.1 ω.property)
  rw [dimerKernel_apply, image_univ, Subtype.range_coe]
  refine (prob_compl_eq_zero_iff measurableSet_dimerSubshift).1 ?_
  have h : (G.dimerSubshift Γ hΓ : Set (G.edgeSet → Bool))ᶜ =
      {ω' | ¬ G.IsDimerConfiguration ω'} :=
    Set.ext fun _ => not_congr (SetLike.mem_coe.trans mem_dimerSubshift)
  rw [h]
  exact dimerBoltzmann_setOf_not_isDimerConfiguration w F ω.val

/-- The kernel `γ^w_F` is proper: every member of the completion set agrees with `ω` off `F`, so
an event of the exterior σ-algebra of `F` holds for it exactly when it holds for `ω`. -/
theorem isProper_dimerKernel (w : G.edgeSet → ℝ) (F : Finset G.edgeSet) :
    (dimerKernel (Γ := Γ) (hΓ := hΓ) w F).IsProper := by
  have hemb := MeasurableEmbedding.subtypeVal (measurableSet_dimerSubshift (Γ := Γ) (hΓ := hΓ))
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
    rw [indicator_of_mem (show ω ∈ Subtype.val ⁻¹' B' from hωB), Pi.one_apply, one_mul]
    by_cases hω'A : ω' ∈ Subtype.val '' A
    · rw [indicator_of_mem hω'A, indicator_of_mem (mem_inter hω'A hω'B)]
    · rw [indicator_of_notMem hω'A, indicator_of_notMem fun h => hω'A (mem_of_mem_inter_left h)]
  · have hω'B : ω' ∉ B' := hiff ▸ hωB
    rw [indicator_of_notMem (show ω ∉ Subtype.val ⁻¹' B' from hωB), zero_mul,
      indicator_of_notMem fun h => hω'B (mem_of_mem_inter_right h)]

/-- **Consistency of the dimer kernels**: `γ^w_Λ ∘ γ^w_Δ = γ^w_Δ` for `Λ ⊆ Δ`. -/
theorem dimerKernel_comp_eq {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) {Λ Δ : Finset G.edgeSet}
    (h : Λ ⊆ Δ) :
    (dimerKernel (Γ := Γ) (hΓ := hΓ) w Λ).comap id
        (measurable_id'' ((G.dimerSubshift Γ hΓ).exterior_le Λ)) ∘ₖ dimerKernel w Δ =
      dimerKernel w Δ := by
  have hemb := MeasurableEmbedding.subtypeVal (measurableSet_dimerSubshift (Γ := Γ) (hΓ := hΓ))
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
  kernel F := dimerKernel w F
  isMarkovKernel F := isMarkovKernel_dimerKernel hw F
  isProper F := isProper_dimerKernel w F
  comp_eq _ _ h := dimerKernel_comp_eq hw h

@[simp]
theorem dimerSpecification_kernel {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) (F : Finset G.edgeSet) :
    (dimerSpecification Γ hΓ hw).kernel F = dimerKernel w F :=
  (rfl)

/-- **Gauge invariance of the dimer specification.** For a positive `g`, the gauge transform
`w(uv) g(u) g(v)` of the weight has the same specification. -/
theorem dimerSpecification_gaugeWeight {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) {g : V → ℝ}
    (hg : ∀ v, 0 < g v) (hw' : ∀ e, 0 < G.gaugeWeight w g e) :
    dimerSpecification Γ hΓ hw' = dimerSpecification Γ hΓ hw := by
  ext F ω A _
  simp only [dimerSpecification_kernel, dimerKernel_apply, dimerBoltzmann_gaugeWeight w hg]

end Specification

end SimpleGraph
