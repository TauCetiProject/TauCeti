/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import TauCeti.Probability.Gibbs.Dimer.Specification
import TauCeti.MeasureTheory.Group.Action
import TauCeti.MeasureTheory.Group.Arithmetic
import TauCeti.MeasureTheory.Group.CountableAction
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Action
import TauCeti.Probability.Gibbs.Extreme

/-!
# Invariant and ergodic dimer Gibbs measures

Let `G` be a locally finite graph with countably many edges, `Γ` a group acting on its edges
through graph automorphisms, and let `Γ` act on configurations by `(g • ω)(e) = ω(g⁻¹ • e)`
(Mathlib's `arrowAction`; here any action on `G.edgeSet → Bool` given by this formula). For a
positive weight `w`, the invariant dimer Gibbs measures `𝒢_inv` (`SimpleGraph.dimerGibbsInvariant`)
are the `Γ`-invariant probability measures on configurations that are dimer Gibbs
(`SimpleGraph.IsDimerGibbs`). They form a convex set (`SimpleGraph.convex_dimerGibbsInvariant`).

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
by `ErgodicSMul.iff_mem_extremePoints`; it is extreme among the invariant dimer Gibbs measures if
and only if it is extreme among all invariant probability measures
(`SimpleGraph.mem_extremePoints_dimerGibbsInvariant_iff`), and if and only if every invariant
event has measure `0` or `1`
(`SimpleGraph.mem_extremePoints_dimerGibbsInvariant_iff_measure_eq_zero_or_one`). These are the
two notions of ergodicity in the literature: extreme points of `𝒢_inv` (Gorin) and invariant Gibbs
measures with trivial invariant events (Kenyon). Conditioning an invariant dimer Gibbs measure on an
almost invariant event of positive measure gives an invariant dimer Gibbs measure
(`SimpleGraph.cond_mem_dimerGibbsInvariant`), by the face property applied to the decomposition
`μ = μ(t) μ[|t] + μ(tᶜ) μ[|tᶜ]`.

**Compactness.** The dimer Gibbs probability measures form a weakly compact set
(`SimpleGraph.isCompact_setOf_isDimerGibbs`): they are the push-forwards along the inclusion of
`𝔛(G)` of the Gibbs measures of the quasilocal specification `γ^w`, a compact set. So do the
invariant ones (`SimpleGraph.isCompact_setOf_mem_dimerGibbsInvariant`), the invariant probability
measures being weakly closed.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definitions 13.4-13.6 and Lemma 13.7.
* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Lemmas 3.2.1-3.2.2.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Section 5.3.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti.MeasureTheory
open scoped ENNReal ProbabilityTheory

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

/-- The invariant dimer Gibbs measures form a convex set. -/
theorem convex_dimerGibbsInvariant {Γ : Type*} [SMul Γ (G.edgeSet → Bool)]
    {w : G.edgeSet → ℝ} : Convex ℝ≥0∞ (G.dimerGibbsInvariant Γ w) := by
  rintro μ ⟨hμ, hμG⟩ ν ⟨hν, hνG⟩ a b ha hb hab
  obtain ⟨_, hμ0, hμc⟩ := isDimerGibbs_iff.1 hμG
  obtain ⟨_, hν0, hνc⟩ := isDimerGibbs_iff.1 hνG
  refine ⟨convex_invariantMeasuresOfMeasureUnivEq hμ hν ha hb hab, isDimerGibbs_iff.2
    ⟨⟨by simp [hab]⟩, by simp [hμ0, hν0], fun F E ω ω' hω hω' hF hE => ?_⟩⟩
  simp only [add_apply, smul_apply, smul_eq_mul, mul_add, mul_left_comm _ a, mul_left_comm _ b,
    hμc F E ω ω' hω hω' hF hE, hνc F E ω ω' hω hω' hF hE]

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

/-- **Extreme in `𝒢_inv` iff extreme in `𝔓_inv`.** If every finite set of edges can be moved off
every finite set of edges by `Γ`, then for a positive weight an invariant dimer Gibbs measure is
an extreme point of the invariant dimer Gibbs measures if and only if it is an extreme point of
all invariant probability measures on configurations. -/
theorem mem_extremePoints_dimerGibbsInvariant_iff
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) [SMul Γ (G.edgeSet → Bool)]
    (hσ : ∀ (g : Γ) (ω : G.edgeSet → Bool) e, (g • ω) e = ω (g⁻¹ • e)) {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (hmove : ∀ F Λ : Finset G.edgeSet, ∃ g : Γ, ∀ e ∈ F, g • e ∉ Λ)
    {μ : Measure (G.edgeSet → Bool)} (hμ : μ ∈ G.dimerGibbsInvariant Γ w) :
    μ ∈ extremePoints ℝ≥0∞ (G.dimerGibbsInvariant Γ w) ↔
      μ ∈ extremePoints ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq Γ (G.edgeSet → Bool) 1) := by
  rw [(isExtreme_dimerGibbsInvariant hΓ hσ hw hmove).extremePoints_eq]
  exact and_iff_right hμ

/-- **Extreme invariant dimer Gibbs measures have trivial invariant events.** For a countable group
`Γ` that moves every finite set of edges off every finite set of edges, and a positive weight, an
invariant dimer Gibbs measure is an extreme point of the invariant dimer Gibbs measures if and
only if every measurable `Γ`-invariant set of configurations has measure `0` or `1`. -/
theorem mem_extremePoints_dimerGibbsInvariant_iff_measure_eq_zero_or_one [Countable Γ]
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) [MulAction Γ (G.edgeSet → Bool)]
    (hσ : ∀ (g : Γ) (ω : G.edgeSet → Bool) e, (g • ω) e = ω (g⁻¹ • e)) {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (hmove : ∀ F Λ : Finset G.edgeSet, ∃ g : Γ, ∀ e ∈ F, g • e ∉ Λ)
    {μ : Measure (G.edgeSet → Bool)} (hμ : μ ∈ G.dimerGibbsInvariant Γ w) :
    μ ∈ extremePoints ℝ≥0∞ (G.dimerGibbsInvariant Γ w) ↔
      ∀ t : Set (G.edgeSet → Bool), MeasurableSet t → (∀ g : Γ, (fun ω => g • ω) ⁻¹' t = t) →
        μ t = 0 ∨ μ t = 1 := by
  have := hμ.2.isProbabilityMeasure
  have := (mem_invariantMeasuresOfMeasureUnivEq_iff.1 hμ.1).1
  have := TauCeti.measurableConstSMul_of_smul_apply hσ
  rw [mem_extremePoints_dimerGibbsInvariant_iff_ergodicSMul hΓ hσ hw hmove hμ,
    ergodicSMul_iff_forall_smul_invariant]
  refine forall₂_congr fun t ht => imp_congr_right fun _ => ?_
  rw [Filter.eventuallyEmptyOrUniv_iff', ae_eq_empty,
    ae_eq_univ_iff_measure_eq ht.nullMeasurableSet, measure_univ]

/-- **Conditioning on an invariant event.** If every finite set of edges can be moved off every
finite set of edges by `Γ`, then for a positive weight an invariant dimer Gibbs measure
conditioned on a measurable, almost invariant event of positive measure is an invariant dimer
Gibbs measure. -/
theorem cond_mem_dimerGibbsInvariant
    (hΓ : ∀ g : Γ, ∃ φ : G ≃g G, ∀ e, g • e = φ.mapEdgeSet e) [SMul Γ (G.edgeSet → Bool)]
    (hσ : ∀ (g : Γ) (ω : G.edgeSet → Bool) e, (g • ω) e = ω (g⁻¹ • e)) {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) (hmove : ∀ F Λ : Finset G.edgeSet, ∃ g : Γ, ∀ e ∈ F, g • e ∉ Λ)
    {μ : Measure (G.edgeSet → Bool)} (hμ : μ ∈ G.dimerGibbsInvariant Γ w)
    {t : Set (G.edgeSet → Bool)} (ht : MeasurableSet t)
    (htg : ∀ g : Γ, (fun ω => g • ω) ⁻¹' t =ᵐ[μ] t) (ht₀ : μ t ≠ 0) :
    μ[|t] ∈ G.dimerGibbsInvariant Γ w := by
  have := hμ.2.isProbabilityMeasure
  have := (mem_invariantMeasuresOfMeasureUnivEq_iff.1 hμ.1).1
  have hmem {u : Set (G.edgeSet → Bool)} (hu : MeasurableSet u)
      (hug : ∀ g : Γ, (fun ω => g • ω) ⁻¹' u =ᵐ[μ] u) (hu₀ : μ u ≠ 0) :
      μ[|u] ∈ invariantMeasuresOfMeasureUnivEq Γ (G.edgeSet → Bool) 1 :=
    mem_invariantMeasuresOfMeasureUnivEq_iff.2
      ⟨SMulInvariantMeasure.cond hu hug,
        (ProbabilityTheory.cond_isProbabilityMeasure hu₀).measure_univ⟩
  rcases eq_or_ne (μ tᶜ) 0 with hc | hc
  · -- `t` has full measure, so conditioning on it does not change `μ`
    have h1 : μ t = 1 := (prob_compl_eq_zero_iff ht).1 hc
    rwa [ProbabilityTheory.cond, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc), h1, inv_one,
      one_smul]
  · -- otherwise `μ = μ(t) μ[|t] + μ(tᶜ) μ[|tᶜ]` is a proper convex combination
    have htc : ∀ g : Γ, (fun ω => g • ω) ⁻¹' tᶜ =ᵐ[μ] tᶜ := fun g => by
      rw [preimage_compl]
      exact (htg g).compl
    refine (isExtreme_dimerGibbsInvariant hΓ hσ hw hmove).left_mem_of_mem_openSegment
      (hmem ht htg ht₀) (hmem ht.compl htc hc) hμ
      ⟨μ t, μ tᶜ, pos_iff_ne_zero.2 ht₀, pos_iff_ne_zero.2 hc, prob_add_prob_compl ht, ?_⟩
    ext u -
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [mul_comm (μ t), mul_comm (μ tᶜ)]
    exact ProbabilityTheory.cond_add_cond_compl_eq ht μ

omit [Group Γ] [MulAction Γ G.edgeSet] in
/-- **Dimer Gibbs measures form a weakly compact set.** For a positive weight, the dimer Gibbs
probability measures on configurations form a weakly compact set: they are the push-forwards along
the inclusion of the dimer configurations of the Gibbs measures of the quasilocal specification
`γ^w`, taken here for the action of the automorphism group of `G`. -/
theorem isCompact_setOf_isDimerGibbs {w : G.edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    IsCompact {μ : ProbabilityMeasure (G.edgeSet → Bool) | G.IsDimerGibbs w μ} := by
  have hΓ := Iso.exists_smul_eq_mapEdgeSet (G := G)
  have key : {μ : ProbabilityMeasure (G.edgeSet → Bool) | G.IsDimerGibbs w μ} =
      (fun ν : ProbabilityMeasure (G.dimerSubshift (G ≃g G) hΓ) =>
        ν.map Subtype.val) ''
        {ν | (dimerSpecification (G ≃g G) hΓ hw).IsGibbs (ν : Measure _)} := by
    ext μ
    simp only [mem_ofPred_eq, mem_image]
    rw [isDimerGibbs_iff_exists_isGibbs (G ≃g G) hΓ hw]
    constructor
    · rintro ⟨ν, hν, hG, hmap⟩
      exact ⟨⟨ν, hν⟩, hG, Subtype.ext hmap⟩
    · rintro ⟨ν, hG, rfl⟩
      exact ⟨ν, inferInstance, hG, rfl⟩
  rw [key]
  exact (isCompact_setOf_isGibbs_dimerSpecification _ hΓ hw).image
    (ProbabilityMeasure.continuous_map continuous_subtypeVal)

/-- **Invariant dimer Gibbs measures form a weakly compact set.** For a positive weight, the
invariant dimer Gibbs measures `𝒢_inv` form a weakly compact set of probability measures on
configurations, `Γ` acting on configurations by `(g • ω)(e) = ω(g⁻¹ • e)`. -/
theorem isCompact_setOf_mem_dimerGibbsInvariant [SMul Γ (G.edgeSet → Bool)]
    (hσ : ∀ (g : Γ) (ω : G.edgeSet → Bool) e, (g • ω) e = ω (g⁻¹ • e)) {w : G.edgeSet → ℝ}
    (hw : ∀ e, 0 < w e) :
    IsCompact {μ : ProbabilityMeasure (G.edgeSet → Bool) |
      (μ : Measure (G.edgeSet → Bool)) ∈ G.dimerGibbsInvariant Γ w} := by
  have : ContinuousConstSMul Γ (G.edgeSet → Bool) := ⟨fun g => by
    rw [show (fun ω : G.edgeSet → Bool => g • ω) = fun ω e => ω (g⁻¹ • e) from
      funext fun ω => funext (hσ g ω)]
    exact continuous_pi fun e => continuous_apply _⟩
  have key : {μ : ProbabilityMeasure (G.edgeSet → Bool) |
      (μ : Measure (G.edgeSet → Bool)) ∈ G.dimerGibbsInvariant Γ w} =
      {μ : ProbabilityMeasure (G.edgeSet → Bool) |
        SMulInvariantMeasure Γ _ (μ : Measure (G.edgeSet → Bool))} ∩
        {μ | G.IsDimerGibbs w μ} := by
    ext μ
    simp only [mem_dimerGibbsInvariant_iff, mem_invariantMeasuresOfMeasureUnivEq_iff,
      measure_univ, and_true, mem_inter_iff, mem_ofPred_eq]
  rw [key]
  exact (isCompact_setOf_isDimerGibbs hw).inter_left
    ProbabilityMeasure.isClosed_setOf_smulInvariantMeasure

end SimpleGraph
