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
`Ω_{g • F}(σ_g ω)` (`SimpleGraph.dimerCompletionSet_smul`, with the sum form
`SimpleGraph.sum_dimerCompletionSet_smul`). When the weight is invariant under
`g`, `w (g • e) = w e`, the weight of `σ_g ω` on `g • F` is the weight of `ω` on `F`
(`SimpleGraph.dimerWeight_smul`), so the partition functions agree
(`SimpleGraph.dimerPartitionFunction_smul`) and `σ_g` carries the Boltzmann law `γ^w_F(· | ω)` to
`γ^w_{g • F}(· | σ_g ω)` (`SimpleGraph.map_dimerBoltzmann_smul`). On `𝔛(G)` this says that the
dimer specification of a `Γ`-invariant weight is equivariant
(`SimpleGraph.isEquivariant_dimerSpecification`), so by
`TauCeti.Specification.map_smul_mem_gibbsMeasures` the group `Γ` acts on its Gibbs probability
measures.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.4.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Pointwise

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]

/-- **Invariance of the weight.** For a weight invariant under `g`, the weight on `g • F` of the
moved configuration `e ↦ ω (g⁻¹ • e)` is the weight of `ω` on `F`. -/
theorem dimerWeight_smul [DecidableEq G.edgeSet] {w : G.edgeSet → ℝ} (g : Γ)
    (hw : ∀ e, w (g • e) = w e) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerWeight w (g • F) (fun e => ω (g⁻¹ • e)) = G.dimerWeight w F ω := by
  simp only [dimerWeight_def, Finset.prod_filter, Finset.smul_finset_def]
  rw [Finset.prod_image fun _ _ _ _ h => smul_left_cancel g h]
  simp only [inv_smul_smul, hw]

/-- For a weight invariant under `g`, the partition function of `g • F` at the moved configuration
is the partition function of `F`. -/
theorem dimerPartitionFunction_smul [DecidableEq G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) {w : G.edgeSet → ℝ} (g : Γ)
    (hw : ∀ e, w (g • e) = w e) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    G.dimerPartitionFunction w (g • F) (fun e => ω (g⁻¹ • e)) =
      G.dimerPartitionFunction w F ω := by
  rw [dimerPartitionFunction_def, sum_dimerCompletionSet_smul hΓ]
  simp only [dimerWeight_smul g hw, dimerPartitionFunction_def]

/-- **Equivariance of the Boltzmann laws.** For a weight invariant under `g`, moving
configurations by `g` carries `γ^w_F(· | ω)` to `γ^w_{g • F}(· | σ_g ω)`, where
`σ_g ω = (e ↦ ω (g⁻¹ • e))`. -/
theorem map_dimerBoltzmann_smul [DecidableEq G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) {w : G.edgeSet → ℝ} (g : Γ)
    (hw : ∀ e, w (g • e) = w e) (F : Finset G.edgeSet) (ω : G.edgeSet → Bool) :
    (G.dimerBoltzmann w F ω).map (fun ω' e => ω' (g⁻¹ • e)) =
      G.dimerBoltzmann w (g • F) fun e => ω (g⁻¹ • e) := by
  have hm : Measurable fun (ω' : G.edgeSet → Bool) e => ω' (g⁻¹ • e) :=
    Measurable.of_eval fun e => measurable_pi_apply _
  ext s hs
  rw [Measure.map_apply hm hs, dimerBoltzmann_apply w F ω (hm hs), dimerBoltzmann_apply w _ _ hs,
    sum_dimerCompletionSet_smul hΓ, dimerPartitionFunction_smul hΓ g hw]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [dimerWeight_smul g hw]
  exact indicator_comp_right (g := fun _ => _) _

variable [G.LocallyFinite] [Countable G.edgeSet]

variable (Γ) in
/-- **The dimer specification of an invariant weight is equivariant**: moving the boundary
condition by `g` moves the resampled law, `γ^w_{g • F}(g • C | g • ω) = γ^w_F(C | ω)`. -/
theorem isEquivariant_dimerSpecification [DecidableEq G.edgeSet]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) {w : G.edgeSet → ℝ}
    (hw₀ : ∀ e, 0 < w e) (hw : ∀ (g : Γ) e, w (g • e) = w e) :
    (dimerSpecification Γ hΓ hw₀).IsEquivariant := by
  refine TauCeti.Specification.isEquivariant_iff.2 fun g F ω => ?_
  simp only [dimerSpecification_kernel]
  have hemb : MeasurableEmbedding (Subtype.val : G.dimerSubshift Γ hΓ → _) :=
    .subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
  have hcomp : Subtype.val ∘ (g • · : G.dimerSubshift Γ hΓ → G.dimerSubshift Γ hΓ) =
      (fun ω' e => ω' (g⁻¹ • e)) ∘ Subtype.val :=
    funext fun ω' => TauCeti.Subshift.coe_smul g ω'
  -- both sides are determined by their push-forwards along the inclusion of `𝔛(G)`
  have key : ((dimerKernel Γ hΓ w F ω).map (g • ·)).map Subtype.val =
      (dimerKernel Γ hΓ w (g • F) (g • ω)).map Subtype.val := by
    rw [Measure.map_map hemb.measurable (measurable_const_smul g), hcomp,
      ← Measure.map_map (Measurable.of_eval fun e => measurable_pi_apply _) hemb.measurable,
      map_val_dimerKernel, map_val_dimerKernel, map_dimerBoltzmann_smul hΓ g (hw g),
      TauCeti.Subshift.coe_smul]
  exact hemb.map_injective key

end SimpleGraph
