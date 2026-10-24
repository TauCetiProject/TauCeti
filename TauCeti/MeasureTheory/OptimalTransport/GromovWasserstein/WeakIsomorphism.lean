/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic

/-!
# Weak isomorphism of measured kernels

Two measured kernels are weakly isomorphic when a coupling of their measures makes their
pullbacks equal almost everywhere on the square of the coupling. For probability measures this
is equivalently a common probability parametrization, in either of two regimes: a.e. measurable
kernels into a measurable target with measurable equality, or a.e. strongly measurable kernels
with extended metric values. The coordinate projections give a canonical parametrizing space,
and two measure-preserving maps with equal pulled-back kernels give an exact coupling.

The relation is defined for raw measures and kernels with arbitrary target. Symmetry and
invariance under a.e. changes require only a sigma-finite first measure. The exact coupling then
is sigma-finite, although the second measure need not be. Common-space introduction,
reflexivity and transitivity are available in both regimes above. The measurable-target API
requires no topology or essentially separable range; the extended metric API requires no
measurable structure on the target. Transitivity uses gluing: an explicit gluing hypothesis
needs only a sigma-finite middle measure, while a finite middle measure and a standard Borel
last carrier ensure such a gluing without topology on the other carriers.

For an extended metric target and every nonzero exponent, an exact coupling is precisely a
coupling of zero distortion. Weakly isomorphic kernels have Gromov–Wasserstein distance zero
whenever their target discrepancy vanishes on the diagonal; no topology, symmetry or triangle
inequality is needed for this implication. The converse requires an attainment theorem and is
not asserted here.

Raw kernels admit pullback along a transport map whose target carrier has measurable equality
and whose source measure is s-finite. The identity case gives reflexivity under measurable
carrier equality. These laws require no structure on the kernel values. The extended-metric
pullback and reflexivity laws use a.e. strong measurability without measurable carrier equality.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Definition 28, for weak isomorphism via a common
  probability parametrization. The coupling formulation here uses the paired pushforward and
  its coordinate projections. No Lean code is taken from this source.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X Y W Ω Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MeasurableSpace Ω] {μ : Measure X} {ν : Measure Y} {ρ : Measure W}
  {ωX ωX' : X × X → Z} {ωY ωY' : Y × Y → Z} {ωW : W × W → Z}

/-- Two measured kernels are **weakly isomorphic** if some coupling identifies their kernels
almost everywhere on its square. For probability measures the coupling itself is a common
probability parametrizing space, with the two coordinate projections as parametrizing maps. -/
def AreWeaklyIsomorphicKernels (μ : Measure X) (ωX : X × X → Z) (ν : Measure Y)
    (ωY : Y × Y → Z) : Prop :=
  ∃ π : Measure (X × Y), IsCoupling π μ ν ∧
    (fun q : (X × Y) × (X × Y) ↦ ωX (q.1.1, q.2.1)) =ᵐ[π.prod π]
      (fun q ↦ ωY (q.1.2, q.2.2))

/-- A coupling that identifies the pulled-back kernels almost everywhere gives a weak
isomorphism. This constructs weak isomorphisms without unfolding the predicate downstream. -/
theorem areWeaklyIsomorphicKernels_of_isCoupling {π : Measure (X × Y)}
    (hπ : IsCoupling π μ ν)
    (heq : (fun q : (X × Y) × (X × Y) ↦ ωX (q.1.1, q.2.1)) =ᵐ[π.prod π]
      (fun q ↦ ωY (q.1.2, q.2.2))) : AreWeaklyIsomorphicKernels μ ωX ν ωY :=
  ⟨π, hπ, heq⟩

/-- A raw kernel and its pullback along a transport map are weakly isomorphic when the target
carrier has measurable equality. The graph plan supplies the exact coupling, so neither
structure on the kernel target nor measurability of the kernel is
required. In particular this permits duplication of a measured carrier. -/
theorem areWeaklyIsomorphicKernels_comp_prodMap_of_hasLaw [MeasurableEq Y]
    {f : X → Y} (ωY : Y × Y → Z) (hf : ProbabilityTheory.HasLaw f ν μ) :
    AreWeaklyIsomorphicKernels μ (ωY ∘ Prod.map f f) ν ωY := by
  refine areWeaklyIsomorphicKernels_of_isCoupling (isCoupling_graphPlan hf) ?_
  have hgraph := ae_snd_eq_graphPlan hf.aemeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgraph,
    Measure.quasiMeasurePreserving_snd.ae hgraph] with q hq₁ hq₂
  simp only [Function.comp_apply, Prod.map_apply, hq₁, hq₂]

/-- Every raw kernel on a measure with measurable carrier equality is weakly
isomorphic to itself. No structure or measurability is required of its values. -/
theorem areWeaklyIsomorphicKernels_refl_of_measurableEq [MeasurableEq X]
    (ωX : X × X → Z) : AreWeaklyIsomorphicKernels μ ωX μ ωX := by
  simpa using areWeaklyIsomorphicKernels_comp_prodMap_of_hasLaw ωX
    (ProbabilityTheory.HasLaw.id (μ := μ))

/-- Extract an exact coupling from a weak isomorphism, without unfolding the predicate in an
importing module. Neither construction nor extraction requires structure on the target. -/
theorem AreWeaklyIsomorphicKernels.exists_isCoupling
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) :
    ∃ π : Measure (X × Y), IsCoupling π μ ν ∧
      (fun q : (X × Y) × (X × Y) ↦ ωX (q.1.1, q.2.1)) =ᵐ[π.prod π]
        (fun q ↦ ωY (q.1.2, q.2.2)) :=
  h

/-- A weak isomorphism of probability kernels admits a common probability parametrization on
the canonical carrier `X × Y`. -/
theorem AreWeaklyIsomorphicKernels.exists_probability_parametrization [IsProbabilityMeasure μ]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) :
    ∃ γ : Measure (X × Y), IsProbabilityMeasure γ ∧
      MeasurePreserving Prod.fst γ μ ∧ MeasurePreserving Prod.snd γ ν ∧
      (fun q : (X × Y) × (X × Y) ↦ ωX (q.1.1, q.2.1)) =ᵐ[γ.prod γ]
        (fun q ↦ ωY (q.1.2, q.2.2)) := by
  obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
  exact ⟨π, hπ.isProbabilityMeasure, hπ.measurePreserving_fst, hπ.measurePreserving_snd, heq⟩

/-- Exchanging the two kernels preserves weak isomorphism when the first measure is sigma-finite.
No measurability of the target is needed: the coordinate swap is a measurable equivalence. -/
protected theorem AreWeaklyIsomorphicKernels.symm [SigmaFinite μ]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) :
    AreWeaklyIsomorphicKernels ν ωY μ ωX := by
  obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
  have : SigmaFinite π := hπ.measurePreserving_fst.sigmaFinite
  refine areWeaklyIsomorphicKernels_of_isCoupling hπ.swap ?_
  rw [Measure.map_prod_map π π measurable_swap measurable_swap]
  have he : MeasurableEmbedding (Prod.map (Prod.swap : X × Y → Y × X) Prod.swap) :=
    (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding.prodMap
      (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding
  exact he.ae_map_iff.mpr heq.symm

/-- Almost-everywhere changes of the kernels preserve weak isomorphism when the first measure
is sigma-finite. -/
theorem areWeaklyIsomorphicKernels_congr_ae [SigmaFinite μ]
    (hX : ωX =ᵐ[μ.prod μ] ωX') (hY : ωY =ᵐ[ν.prod ν] ωY') :
    AreWeaklyIsomorphicKernels μ ωX ν ωY ↔ AreWeaklyIsomorphicKernels μ ωX' ν ωY' := by
  have transfer {a a' : X × X → Z} {b b' : Y × Y → Z}
      (ha : a =ᵐ[μ.prod μ] a') (hb : b =ᵐ[ν.prod ν] b')
      (h : AreWeaklyIsomorphicKernels μ a ν b) : AreWeaklyIsomorphicKernels μ a' ν b' := by
    obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
    have : SigmaFinite π := hπ.measurePreserving_fst.sigmaFinite
    have ha' := (hπ.measurePreserving_fst.prod hπ.measurePreserving_fst).quasiMeasurePreserving
      |>.ae_eq_comp ha
    have hb' := (hπ.measurePreserving_snd.prod hπ.measurePreserving_snd).quasiMeasurePreserving
      |>.ae_eq_comp hb
    exact areWeaklyIsomorphicKernels_of_isCoupling hπ (ha'.symm.trans (heq.trans hb'))
  exact ⟨transfer hX hY, transfer hX.symm hY.symm⟩

private theorem areWeaklyIsomorphicKernels_of_common_parametrization_of_nullMeasurableSet
    {γ : Measure Ω} [SFinite γ] {f : Ω → X} {g : Ω → Y}
    (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hmeas : NullMeasurableSet
      {q : (X × Y) × (X × Y) | ωX (q.1.1, q.2.1) = ωY (q.1.2, q.2.2)}
      ((γ.map fun w ↦ (f w, g w)).prod (γ.map fun w ↦ (f w, g w))))
    (heq : (fun q : Ω × Ω ↦ ωX (f q.1, f q.2)) =ᵐ[γ.prod γ]
      (fun q ↦ ωY (g q.1, g q.2))) : AreWeaklyIsomorphicKernels μ ωX ν ωY := by
  have hfg : MeasurePreserving (fun w ↦ (f w, g w)) γ (γ.map fun w ↦ (f w, g w)) :=
    ⟨hf.measurable.prodMk hg.measurable, rfl⟩
  refine areWeaklyIsomorphicKernels_of_isCoupling
    (isCoupling_map_prodMk_of_measurePreserving hf hg) ?_
  have hpre := (hfg.prod hfg).measure_preimage hmeas.compl
  simp only [Set.compl_ofPred] at hpre
  rw [Filter.EventuallyEq, ae_iff, ← hpre]
  exact ae_iff.mp heq

/-- Exact couplings that admit a gluing give a common sigma-finite parametrization of the
outer kernels. No structure or measurability is required of any kernel or its target. -/
theorem AreWeaklyIsomorphicKernels.exists_common_parametrization_of_exists_glue [SigmaFinite ν]
    (hXY : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hYW : AreWeaklyIsomorphicKernels ν ωY ρ ωW)
    (hglue : ∀ π : Measure (X × Y), ∀ σ : Measure (Y × W),
      IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    ∃ γ : Measure (X × Y × W), SigmaFinite γ ∧
      MeasurePreserving Prod.fst γ μ ∧ MeasurePreserving (Prod.snd ∘ Prod.snd) γ ρ ∧
      (fun q : (X × Y × W) × (X × Y × W) ↦ ωX (q.1.1, q.2.1)) =ᵐ[γ.prod γ]
        (fun q ↦ ωW (q.1.2.2, q.2.2.2)) := by
  obtain ⟨π, hπ, heqXY⟩ := hXY.exists_isCoupling
  obtain ⟨σ, hσ, heqYW⟩ := hYW.exists_isCoupling
  obtain ⟨γ, hγπ, hγσ⟩ := hglue π σ hπ hσ
  have hleft : MeasurePreserving (Prod.map id Prod.fst) γ π :=
    ⟨measurable_id.prodMap measurable_fst, hγπ⟩
  have hright : MeasurePreserving Prod.snd γ σ := ⟨measurable_snd, hγσ⟩
  have : SigmaFinite π := hπ.measurePreserving_snd.sigmaFinite
  have : SigmaFinite γ := hleft.sigmaFinite
  have heqXY' := (hleft.prod hleft).quasiMeasurePreserving.ae_eq_comp heqXY
  have heqYW' := (hright.prod hright).quasiMeasurePreserving.ae_eq_comp heqYW
  exact ⟨γ, inferInstance, hπ.measurePreserving_fst.comp hleft,
    hσ.measurePreserving_snd.comp hright, heqXY'.trans heqYW'⟩

section MeasurableEq

variable [MeasurableSpace Z] [MeasurableEq Z]

/-- A common s-finite parametrization with equal pulled-back a.e. measurable kernels gives a
weak isomorphism. A measurable diagonal in the target suffices; no topology is needed. -/
theorem areWeaklyIsomorphicKernels_of_common_parametrization_of_aemeasurable
    {γ : Measure Ω} [SFinite γ] {f : Ω → X} {g : Ω → Y}
    (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωY : AEMeasurable ωY (ν.prod ν))
    (heq : (fun q : Ω × Ω ↦ ωX (f q.1, f q.2)) =ᵐ[γ.prod γ]
      (fun q ↦ ωY (g q.1, g q.2))) : AreWeaklyIsomorphicKernels μ ωX ν ωY := by
  have hπ := isCoupling_map_prodMk_of_measurePreserving hf hg
  exact areWeaklyIsomorphicKernels_of_common_parametrization_of_nullMeasurableSet hf hg
    (nullMeasurableSet_eq_fun
      (hωX.comp_quasiMeasurePreserving (hπ.measurePreserving_fst.prod
        hπ.measurePreserving_fst).quasiMeasurePreserving)
      (hωY.comp_quasiMeasurePreserving (hπ.measurePreserving_snd.prod
        hπ.measurePreserving_snd).quasiMeasurePreserving)) heq

/-- Pullback along a measure-preserving map preserves weak isomorphism for a.e. measurable
kernels whose target has measurable equality. -/
theorem areWeaklyIsomorphicKernels_comp_prodMap_of_aemeasurable [SFinite μ] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (hωY : AEMeasurable ωY (ν.prod ν)) :
    AreWeaklyIsomorphicKernels μ (ωY ∘ Prod.map f f) ν ωY :=
  areWeaklyIsomorphicKernels_of_common_parametrization_of_aemeasurable
    (MeasurePreserving.id μ) hf
    (hωY.comp_quasiMeasurePreserving (hf.prod hf).quasiMeasurePreserving) hωY
    (.of_forall fun _ ↦ rfl)

/-- Every a.e. measurable kernel into a target with measurable equality is weakly isomorphic
to itself over an s-finite measure. -/
theorem areWeaklyIsomorphicKernels_refl_of_aemeasurable [SFinite μ]
    (hωX : AEMeasurable ωX (μ.prod μ)) : AreWeaklyIsomorphicKernels μ ωX μ ωX :=
  areWeaklyIsomorphicKernels_of_common_parametrization_of_aemeasurable
    (MeasurePreserving.id μ) (MeasurePreserving.id μ) hωX hωX (.of_forall fun _ ↦ rfl)

/-- Weak isomorphisms compose when their exact couplings admit a gluing and their outer
kernels are a.e. measurable into a target with measurable equality. -/
theorem AreWeaklyIsomorphicKernels.trans_of_exists_glue_of_aemeasurable [SigmaFinite ν]
    (hXY : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hYW : AreWeaklyIsomorphicKernels ν ωY ρ ωW)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωW : AEMeasurable ωW (ρ.prod ρ))
    (hglue : ∀ π : Measure (X × Y), ∀ σ : Measure (Y × W),
      IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    AreWeaklyIsomorphicKernels μ ωX ρ ωW := by
  obtain ⟨γ, hγ, hX, hW, heq⟩ :=
    hXY.exists_common_parametrization_of_exists_glue hYW hglue
  exact areWeaklyIsomorphicKernels_of_common_parametrization_of_aemeasurable hX hW hωX hωW heq

/-- Weak isomorphisms of a.e. measurable kernels are transitive when the target has measurable
equality, the last carrier is standard Borel, and the middle measure is finite. -/
theorem AreWeaklyIsomorphicKernels.trans_of_aemeasurable [StandardBorelSpace W]
    [IsFiniteMeasure ν] (hXY : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hYW : AreWeaklyIsomorphicKernels ν ωY ρ ωW)
    (hωX : AEMeasurable ωX (μ.prod μ)) (hωW : AEMeasurable ωW (ρ.prod ρ)) :
    AreWeaklyIsomorphicKernels μ ωX ρ ωW :=
  hXY.trans_of_exists_glue_of_aemeasurable hYW hωX hωW fun π σ hπ hσ ↦
    have : IsFiniteMeasure σ := hσ.isFiniteMeasure
    Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm)

end MeasurableEq

section EDist

variable [EDist Z]

/-- Weakly isomorphic kernels have zero Gromov–Wasserstein distance when self-discrepancies
vanish. No topology, symmetry or triangle inequality is needed, and the exponent may be zero. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_eq_zero
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) (hself : ∀ z : Z, edist z z = 0) (p : ℝ≥0∞) :
    gromovWassersteinEDist p μ ωX ν ωY = 0 := by
  obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
  refine nonpos_iff_eq_zero.mp ((gromovWassersteinEDist_le hπ p ωX ωY).trans_eq ?_)
  rw [gromovWassersteinDistortion_def]
  have hzero : (fun q : (X × Y) × (X × Y) ↦
      edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) =ᵐ[π.prod π] 0 := by
    filter_upwards [heq] with q hq
    simpa only [hq, Pi.zero_apply] using hself (ωY (q.1.2, q.2.2))
  rw [eLpNorm_congr_ae hzero, eLpNorm_zero]

end EDist

section EMetricSpace

variable [EMetricSpace Z] {p : ℝ≥0∞}

/-- Weak isomorphism is equivalent to the existence of a zero-distortion coupling at any
nonzero exponent, including `∞`. This does not assert attainment of the distance infimum. -/
theorem areWeaklyIsomorphicKernels_iff_exists_distortion_eq_zero (hp : p ≠ 0) :
    AreWeaklyIsomorphicKernels μ ωX ν ωY ↔
      ∃ π : Measure (X × Y), IsCoupling π μ ν ∧
        gromovWassersteinDistortion p ωX ωY π = 0 := by
  constructor
  · intro h
    obtain ⟨π, hπ, heq⟩ := h.exists_isCoupling
    exact ⟨π, hπ, (gromovWassersteinDistortion_eq_zero_iff hp).mpr heq⟩
  · rintro ⟨π, hπ, hzero⟩
    exact areWeaklyIsomorphicKernels_of_isCoupling hπ
      ((gromovWassersteinDistortion_eq_zero_iff hp).mp hzero)

/-- A common s-finite parametrizing measure with equal pulled-back kernels gives a weak
isomorphism. The witness coupling is the pushforward along the paired parametrizing maps. -/
theorem areWeaklyIsomorphicKernels_of_common_parametrization {γ : Measure Ω} [SFinite γ]
    {f : Ω → X} {g : Ω → Y} (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (heq : (fun q : Ω × Ω ↦ ωX (f q.1, f q.2)) =ᵐ[γ.prod γ]
      (fun q ↦ ωY (g q.1, g q.2))) : AreWeaklyIsomorphicKernels μ ωX ν ωY := by
  have hπ := isCoupling_map_prodMk_of_measurePreserving hf hg
  exact areWeaklyIsomorphicKernels_of_common_parametrization_of_nullMeasurableSet hf hg
    ((hωX.comp_quasiMeasurePreserving (hπ.measurePreserving_fst.prod
      hπ.measurePreserving_fst).quasiMeasurePreserving).nullMeasurableSet_eq_fun
      (hωY.comp_quasiMeasurePreserving (hπ.measurePreserving_snd.prod
        hπ.measurePreserving_snd).quasiMeasurePreserving)) heq

/-- A measured kernel and its pullback along a measure-preserving map are weakly isomorphic.
In particular this permits duplication of a measured carrier without changing its kernel. -/
theorem areWeaklyIsomorphicKernels_comp_prodMap [SFinite μ] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    AreWeaklyIsomorphicKernels μ (ωY ∘ Prod.map f f) ν ωY :=
  areWeaklyIsomorphicKernels_of_common_parametrization (MeasurePreserving.id μ) hf
    (hωY.comp_quasiMeasurePreserving (hf.prod hf).quasiMeasurePreserving) hωY
    (.of_forall fun _ ↦ rfl)

/-- Every a.e. strongly measurable kernel on an s-finite measure is weakly isomorphic to itself. -/
theorem areWeaklyIsomorphicKernels_refl [SFinite μ]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) : AreWeaklyIsomorphicKernels μ ωX μ ωX :=
  areWeaklyIsomorphicKernels_of_common_parametrization (MeasurePreserving.id μ)
    (MeasurePreserving.id μ) hωX hωX (.of_forall fun _ ↦ rfl)

/-- Weak isomorphisms compose whenever their exact couplings admit a gluing. Only the outer
kernels need a.e. strong measurability; equality of their pullbacks passes through the middle
kernel on the common glued space. The middle measure need only be sigma-finite. -/
theorem AreWeaklyIsomorphicKernels.trans_of_exists_glue [SigmaFinite ν]
    (hXY : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hYW : AreWeaklyIsomorphicKernels ν ωY ρ ωW)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωW : AEStronglyMeasurable ωW (ρ.prod ρ))
    (hglue : ∀ π : Measure (X × Y), ∀ σ : Measure (Y × W),
      IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    AreWeaklyIsomorphicKernels μ ωX ρ ωW := by
  obtain ⟨γ, hγ, hX, hW, heq⟩ :=
    hXY.exists_common_parametrization_of_exists_glue hYW hglue
  exact areWeaklyIsomorphicKernels_of_common_parametrization hX hW hωX hωW heq

/-- Weak isomorphisms are transitive when the last carrier is standard Borel and the middle
measure is finite. The other carriers need no topology or standard Borel structure. -/
protected theorem AreWeaklyIsomorphicKernels.trans [StandardBorelSpace W] [IsFiniteMeasure ν]
    (hXY : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hYW : AreWeaklyIsomorphicKernels ν ωY ρ ωW)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) :
    AreWeaklyIsomorphicKernels μ ωX ρ ωW :=
  hXY.trans_of_exists_glue hYW hωX hωW fun π σ hπ hσ ↦
    have : IsFiniteMeasure σ := hσ.isFiniteMeasure
    Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm)

end EMetricSpace

end TauCeti
