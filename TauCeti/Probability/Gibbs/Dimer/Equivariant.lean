/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Dimer.Specification

/-!
# Equivariance of the dimer specification

Let `G` be a locally finite graph with countably many edges and `Γ` a group acting on its edges
through graph automorphisms, so that `Γ` acts on the subshift `𝔛(G)` of dimer configurations by
`(g • ω)(e) = ω(g⁻¹ • e)`. Write `σ_g ω` for this action on all configurations.

Moving a configuration by `g` moves its completion set: `σ_g` maps `Ω_F(ω)` bijectively onto
`Ω_{g • F}(σ_g ω)` (`SimpleGraph.sum_dimerCompletionSet_smul`). When the weight is invariant,
`w (g • e) = w e`, the weight of `σ_g ω` on `g • F` is the weight of `ω` on `F`
(`SimpleGraph.dimerWeight_smul`), so the partition functions agree
(`SimpleGraph.dimerPartitionFunction_smul`) and `σ_g` carries the Boltzmann law `γ^w_F(· | ω)` to
`γ^w_{g • F}(· | σ_g ω)` (`SimpleGraph.map_dimerBoltzmann_smul`). On `𝔛(G)` this says that the
dimer specification of an invariant weight is equivariant
(`SimpleGraph.isEquivariant_dimerSpecification`), so `Γ` acts on its Gibbs probability measures
(`SimpleGraph.map_smul_mem_gibbsMeasures_dimerSpecification`).

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.4.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Pointwise

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {Γ : Type*} [Group Γ]
  [MulAction Γ G.edgeSet] {hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e}

include hΓ in
/-- Moving a dimer configuration by an element of `Γ` gives a dimer configuration. -/
theorem IsDimerConfiguration.smul {ω : G.edgeSet → Bool} (hω : G.IsDimerConfiguration ω)
    (g : Γ) : G.IsDimerConfiguration fun e => ω (g⁻¹ • e) :=
  mem_dimerSubshift.1 ((G.dimerSubshift Γ hΓ).smul_mem g (mem_dimerSubshift.2 hω))

include hΓ in
/-- **Moving a completion set.** The map `σ_g ω = (e ↦ ω (g⁻¹ • e))` is a bijection from the
completion set `Ω_F(ω)` onto `Ω_{g • F}(σ_g ω)`, so sums over the two sets agree. -/
theorem sum_dimerCompletionSet_smul [DecidableEq G.edgeSet] {M : Type*} [AddCommMonoid M]
    (g : Γ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) (f : (G.edgeSet → Bool) → M) :
    ∑ ω' ∈ (G.finite_dimerCompletionSet (g • F) fun e => ω (g⁻¹ • e)).toFinset, f ω' =
      ∑ ω' ∈ (G.finite_dimerCompletionSet F ω).toFinset, f fun e => ω' (g⁻¹ • e) := by
  symm
  refine Finset.sum_nbij' (fun ω' e => ω' (g⁻¹ • e)) (fun ω' e => ω' (g • e)) ?_ ?_ ?_ ?_
    fun _ _ => rfl
  · intro ω' hω'
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω' ⊢
    refine ⟨hω'.1.smul (hΓ := hΓ) g, fun e he => hω'.2 _ fun h => he ?_⟩
    rwa [← Finset.inv_smul_mem_iff]
  · intro ω' hω'
    simp only [Finite.mem_toFinset, mem_dimerCompletionSet] at hω' ⊢
    refine ⟨by simpa using hω'.1.smul (hΓ := hΓ) g⁻¹, fun e he => ?_⟩
    rw [hω'.2 _ fun h => he ((Finset.smul_mem_smul_finset_iff g).1 h), inv_smul_smul]
  · intro ω' _
    exact funext fun e => congrArg ω' (inv_smul_smul g e)
  · intro ω' _
    exact funext fun e => congrArg ω' (smul_inv_smul g e)

omit [G.LocallyFinite] in
/-- **Invariance of the weight.** For an invariant weight, the weight on `g • F` of the moved
configuration `e ↦ ω (g⁻¹ • e)` is the weight of `ω` on `F`. -/
theorem dimerWeight_smul [DecidableEq G.edgeSet] {w : G.edgeSet → ℝ}
    (hw : ∀ (g : Γ) e, w (g • e) = w e) (g : Γ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerWeight w (g • F) (fun e => ω (g⁻¹ • e)) = G.dimerWeight w F ω := by
  simp only [dimerWeight_def, Finset.prod_filter, Finset.smul_finset_def]
  rw [Finset.prod_image fun _ _ _ _ h => smul_left_cancel g h]
  simp only [inv_smul_smul, hw]

include hΓ in
/-- For an invariant weight, the partition function of `g • F` at the moved configuration is the
partition function of `F`. -/
theorem dimerPartitionFunction_smul [DecidableEq G.edgeSet] {w : G.edgeSet → ℝ}
    (hw : ∀ (g : Γ) e, w (g • e) = w e) (g : Γ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerPartitionFunction w (g • F) (fun e => ω (g⁻¹ • e)) =
      G.dimerPartitionFunction w F ω := by
  rw [dimerPartitionFunction_def, sum_dimerCompletionSet_smul (hΓ := hΓ)]
  simp only [dimerWeight_smul hw, dimerPartitionFunction_def]

include hΓ in
/-- **Equivariance of the Boltzmann laws.** For an invariant weight, moving configurations by `g`
carries `γ^w_F(· | ω)` to `γ^w_{g • F}(· | σ_g ω)`, where `σ_g ω = (e ↦ ω (g⁻¹ • e))`. -/
theorem map_dimerBoltzmann_smul [DecidableEq G.edgeSet] {w : G.edgeSet → ℝ}
    (hw : ∀ (g : Γ) e, w (g • e) = w e) (g : Γ) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    (G.dimerBoltzmann w F ω).map (fun ω' e => ω' (g⁻¹ • e)) =
      G.dimerBoltzmann w (g • F) fun e => ω (g⁻¹ • e) := by
  have hm : Measurable fun (ω' : G.edgeSet → Bool) e => ω' (g⁻¹ • e) :=
    Measurable.of_eval fun e => measurable_pi_apply _
  ext s hs
  rw [Measure.map_apply hm hs, dimerBoltzmann_apply w F ω (hm hs), dimerBoltzmann_apply w _ _ hs,
    sum_dimerCompletionSet_smul (hΓ := hΓ), dimerPartitionFunction_smul (hΓ := hΓ) hw]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [dimerWeight_smul hw]
  rfl

variable [Countable G.edgeSet]

variable (Γ hΓ) in
/-- **The dimer specification of an invariant weight is equivariant**: moving the boundary
condition by `g` moves the resampled law, `γ^w_{g • F}(g • C | g • ω) = γ^w_F(C | ω)`. -/
theorem isEquivariant_dimerSpecification [DecidableEq G.edgeSet] {w : G.edgeSet → ℝ}
    (hw₀ : ∀ e, 0 < w e) (hw : ∀ (g : Γ) e, w (g • e) = w e) :
    (dimerSpecification Γ hΓ hw₀).IsEquivariant := by
  refine TauCeti.Specification.isEquivariant_iff.2 fun g F ω => ?_
  simp only [dimerSpecification_kernel]
  have hemb : MeasurableEmbedding (Subtype.val : G.dimerSubshift Γ hΓ → _) :=
    .subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
  have hcarried (ν : G.edgeSet → Bool) :
      (G.dimerBoltzmann w (g • F) ν).restrict
          (range (Subtype.val : G.dimerSubshift Γ hΓ → _)) =
        G.dimerBoltzmann w (g • F) ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, Subtype.range_coe_subtype]
    simpa using dimerBoltzmann_setOf_not_isDimerConfiguration w (g • F) ν
  have hcarried' (ν : G.edgeSet → Bool) :
      (G.dimerBoltzmann w F ν).restrict (range (Subtype.val : G.dimerSubshift Γ hΓ → _)) =
        G.dimerBoltzmann w F ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, Subtype.range_coe_subtype]
    simpa using dimerBoltzmann_setOf_not_isDimerConfiguration w F ν
  -- both sides are determined by their push-forwards along the inclusion of `𝔛(G)`
  have key : ((dimerKernel Γ hΓ w F ω).map (g • ·)).map Subtype.val =
      (dimerKernel Γ hΓ w (g • F) (g • ω)).map Subtype.val := by
    rw [Measure.map_map hemb.measurable (measurable_const_smul g),
      show Subtype.val ∘ (g • · : G.dimerSubshift Γ hΓ → G.dimerSubshift Γ hΓ) =
        (fun ω' e => ω' (g⁻¹ • e)) ∘ Subtype.val from rfl,
      ← Measure.map_map (Measurable.of_eval fun e => measurable_pi_apply _) hemb.measurable,
      dimerKernel_apply_eq_comap, dimerKernel_apply_eq_comap, hemb.map_comap, hemb.map_comap,
      hcarried', hcarried, map_dimerBoltzmann_smul (hΓ := hΓ) hw]
    rfl
  ext C _
  have h := congrArg (fun μ : Measure (G.edgeSet → Bool) => μ (Subtype.val '' C)) key
  simpa only [hemb.map_apply, Subtype.val_injective.preimage_image] using h

/-- For an invariant weight, moving a Gibbs probability measure of the dimer specification by
`g` gives a Gibbs probability measure: `𝒢(γ^w)` is `Γ`-invariant. -/
theorem map_smul_mem_gibbsMeasures_dimerSpecification {w : G.edgeSet → ℝ} (hw₀ : ∀ e, 0 < w e)
    (hw : ∀ (g : Γ) e, w (g • e) = w e)
    {μ : Measure (G.dimerSubshift Γ hΓ)} (hμ : μ ∈ (dimerSpecification Γ hΓ hw₀).gibbsMeasures)
    (g : Γ) : μ.map (g • ·) ∈ (dimerSpecification Γ hΓ hw₀).gibbsMeasures :=
  open scoped Classical in
  TauCeti.Specification.map_smul_mem_gibbsMeasures
    (isEquivariant_dimerSpecification Γ hΓ hw₀ hw) hμ g

end SimpleGraph
