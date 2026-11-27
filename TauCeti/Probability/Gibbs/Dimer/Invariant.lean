/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import TauCeti.Probability.Gibbs.Dimer.Specification
import TauCeti.Probability.Gibbs.Extreme

/-!
# Invariant and ergodic dimer Gibbs measures

Let `G` be a locally finite graph with countably many edges, `Γ` a group acting on its edges
through graph automorphisms, and let `Γ` act on configurations by `(g • ω)(e) = ω(g⁻¹ • e)`
(Mathlib's `arrowAction`; here any action on `G.edgeSet → Bool` given by this formula). For a
positive weight `w`, the invariant dimer Gibbs measures `𝒢_inv` (`SimpleGraph.dimerGibbsInvariant`)
are the `Γ`-invariant probability measures on configurations that are dimer Gibbs
(`SimpleGraph.IsDimerGibbs`).

**The face property** (`SimpleGraph.isExtreme_dimerGibbsInvariant`). If every finite set of edges
can be moved off every finite set of edges by `Γ` (for instance when `Γ` is infinite and acts
properly, `TauCeti.Probability.exists_forall_smul_notMem_of_proper`), then `𝒢_inv` is a face of
the invariant probability measures: if `a μ₁ + b μ₂` with `a, b > 0` is an invariant dimer Gibbs
measure and `μ₁`, `μ₂` are invariant probability measures, then `μ₁` is dimer Gibbs. The proof
transports the face property of invariant Gibbs measures of a specification on a subshift
(`TauCeti.Specification.isExtreme_gibbsInvariant`) through the inclusion of the subshift `𝔛(G)` of
dimer configurations: `μ₁` and `μ₂` are carried by `𝔛(G)`, so they are the push-forwards of their
pull-backs `ν₁`, `ν₂` (`TauCeti.Subshift.map_comap_val_of_ae_mem`), which are invariant
probability measures on `𝔛(G)` (`TauCeti.Subshift.comap_val_mem_invariantMeasuresOfMeasureUnivEq`);
the pull-back of `a μ₁ + b μ₂` is
`a ν₁ + b ν₂` and is Gibbs for the dimer specification
(`SimpleGraph.IsDimerGibbs.isGibbs_comap_val`), hence so is `ν₁`, and its push-forward `μ₁` is
dimer Gibbs (`SimpleGraph.isDimerGibbs_map_val`).

Consequently an invariant dimer Gibbs measure is extreme among the invariant dimer Gibbs measures
if and only if it is ergodic (`SimpleGraph.mem_extremePoints_dimerGibbsInvariant_iff_ergodicSMul`),
by `ErgodicSMul.iff_mem_extremePoints`.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definitions 13.4-13.6 and Lemma 13.7.
* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Lemmas 3.2.1-3.2.2.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti.MeasureTheory
open scoped ENNReal

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

variable (G) in
/-- The invariant dimer Gibbs measures `𝒢_inv`: the `Γ`-invariant probability measures on
configurations that are dimer Gibbs for the weight `w`. -/
def dimerGibbsInvariant (Γ : Type*) [SMul Γ (G.edgeSet → Bool)] (w : G.edgeSet → ℝ) :
    Set (Measure (G.edgeSet → Bool)) :=
  {μ | μ ∈ invariantMeasuresOfMeasureUnivEq Γ (G.edgeSet → Bool) 1 ∧ G.IsDimerGibbs w μ}

@[simp]
theorem mem_dimerGibbsInvariant_iff {Γ : Type*} [SMul Γ (G.edgeSet → Bool)]
    {w : G.edgeSet → ℝ} {μ : Measure (G.edgeSet → Bool)} :
    μ ∈ G.dimerGibbsInvariant Γ w ↔
      μ ∈ invariantMeasuresOfMeasureUnivEq Γ (G.edgeSet → Bool) 1 ∧ G.IsDimerGibbs w μ :=
  Iff.rfl

variable [G.LocallyFinite] [Countable G.edgeSet] {Γ : Type*} [Group Γ] [MulAction Γ G.edgeSet]

/-- **The face property of invariant dimer Gibbs measures.** If every finite set of edges can be
moved off every finite set of edges by `Γ`, then for a positive weight `w` the invariant dimer
Gibbs measures form a face of the invariant probability measures on configurations, `Γ` acting on
configurations by `(g • ω)(e) = ω(g⁻¹ • e)`. -/
theorem isExtreme_dimerGibbsInvariant
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) [SMul Γ (G.edgeSet → Bool)]
    (hσ : ∀ (g : Γ) (ω : G.edgeSet → Bool) e, (g • ω) e = ω (g⁻¹ • e)) {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (hmove : ∀ F Λ : Finset G.edgeSet, ∃ g : Γ, ∀ e ∈ F, g • e ∉ Λ) :
    IsExtreme ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq Γ (G.edgeSet → Bool) 1)
      (G.dimerGibbsInvariant Γ w) where
  subset _ h := h.1
  left_mem_of_mem_openSegment := by
    rintro μ₁ hμ₁ μ₂ hμ₂ μ hμ ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hμ₁, ?_⟩
    have hemb : MeasurableEmbedding (Subtype.val : G.dimerSubshift Γ hΓ → G.edgeSet → Bool) :=
      MeasurableEmbedding.subtypeVal (G.dimerSubshift Γ hΓ).measurableSet_coe
    -- both measures are carried by dimer configurations
    have hnull := hμ.2.measure_setOf_not_isDimerConfiguration
    simp only [add_apply, smul_apply, smul_eq_mul, add_eq_zero,
      mul_eq_zero, ha.ne', hb.ne', false_or] at hnull
    have hX₁ : ∀ᵐ ω ∂μ₁, ω ∈ G.dimerSubshift Γ hΓ :=
      (ae_iff.2 hnull.1).mono fun _ => mem_dimerSubshift.2
    have hX₂ : ∀ᵐ ω ∂μ₂, ω ∈ G.dimerSubshift Γ hΓ :=
      (ae_iff.2 hnull.2).mono fun _ => mem_dimerSubshift.2
    have hmap₁ := TauCeti.Subshift.map_comap_val_of_ae_mem hX₁
    have hmap₂ := TauCeti.Subshift.map_comap_val_of_ae_mem hX₂
    set ν₁ := μ₁.comap (Subtype.val : G.dimerSubshift Γ hΓ → _)
    set ν₂ := μ₂.comap (Subtype.val : G.dimerSubshift Γ hΓ → _)
    have hν₁ := TauCeti.Subshift.comap_val_mem_invariantMeasuresOfMeasureUnivEq hσ hμ₁ hX₁
    have hν₂ := TauCeti.Subshift.comap_val_mem_invariantMeasuresOfMeasureUnivEq hσ hμ₂ hX₂
    -- the pull-back of the combination is the combination of the pull-backs, and is Gibbs
    have hcomb : (a • μ₁ + b • μ₂).comap Subtype.val = a • ν₁ + b • ν₂ := by
      rw [← hemb.comap_map (a • ν₁ + b • ν₂), Measure.map_add _ _ hemb.measurable,
        Measure.map_smul, Measure.map_smul, hmap₁, hmap₂]
      all_goals exact hemb.measurable.aemeasurable
    have hG : a • ν₁ + b • ν₂ ∈ (dimerSpecification Γ hΓ hw).gibbsInvariant :=
      TauCeti.Specification.mem_gibbsInvariant_iff.2
        ⟨convex_invariantMeasuresOfMeasureUnivEq hν₁ hν₂ ha.le hb.le hab,
          hcomb ▸ hμ.2.isGibbs_comap_val Γ hΓ hw⟩
    have h₁ := TauCeti.Specification.mem_gibbsInvariant_iff.1
      (((dimerSpecification Γ hΓ hw).isExtreme_gibbsInvariant hmove).left_mem_of_mem_openSegment
        hν₁ hν₂ hG ⟨a, b, ha, hb, hab, rfl⟩)
    have : IsProbabilityMeasure ν₁ := ⟨(mem_invariantMeasuresOfMeasureUnivEq_iff.1 hν₁).2⟩
    rw [← hmap₁]
    exact isDimerGibbs_map_val hw h₁.2

/-- **Ergodic invariant dimer Gibbs measures are the extreme ones.** For a countable group `Γ` that
moves every finite set of edges off every finite set of edges, and a positive weight, an invariant
dimer Gibbs measure is an extreme point of the invariant dimer Gibbs measures if and only if it is
ergodic. -/
theorem mem_extremePoints_dimerGibbsInvariant_iff_ergodicSMul [Countable Γ]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) [MulAction Γ (G.edgeSet → Bool)]
    (hσ : ∀ (g : Γ) (ω : G.edgeSet → Bool) e, (g • ω) e = ω (g⁻¹ • e)) {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (hmove : ∀ F Λ : Finset G.edgeSet, ∃ g : Γ, ∀ e ∈ F, g • e ∉ Λ)
    {μ : Measure (G.edgeSet → Bool)} (hμ : μ ∈ G.dimerGibbsInvariant Γ w) :
    μ ∈ extremePoints ℝ≥0∞ (G.dimerGibbsInvariant Γ w) ↔ ErgodicSMul Γ (G.edgeSet → Bool) μ := by
  have := hμ.2.isProbabilityMeasure
  have := TauCeti.measurableConstSMul_of_smul_apply hσ
  rw [(isExtreme_dimerGibbsInvariant hΓ hσ hw hmove).extremePoints_eq,
    ErgodicSMul.iff_mem_extremePoints]
  exact and_iff_right hμ

end SimpleGraph
