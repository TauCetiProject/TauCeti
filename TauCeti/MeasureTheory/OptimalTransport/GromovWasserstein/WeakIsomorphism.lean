/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic

/-!
# Weak isomorphism of measured kernels

Two measured kernels are weakly isomorphic when a coupling of their measures makes their
pullbacks equal almost everywhere on the square of the coupling. For a.e. strongly measurable
kernels with extended metric values and probability measures, this is equivalently a common
probability parametrization: the coordinate projections give a canonical parametrizing space,
and two measure-preserving maps with equal pulled-back kernels give an exact coupling.

The relation is defined for raw measures and kernels with arbitrary target. Its common-space
introduction, reflexivity and transitivity are proved for a.e. strongly measurable kernels with
values in an extended metric space. Transitivity uses gluing; it requires a finite middle measure
and a standard Borel outer carrier, rather than a topology on every carrier.

For an extended metric target and every nonzero exponent, an exact coupling is precisely a
coupling of zero distortion. Consequently weakly isomorphic kernels with a pseudo extended metric
target have Gromov–Wasserstein distance zero. The converse requires an attainment theorem and
is not asserted here.

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

/-- The exact-coupling characterization supplies both introduction and elimination for weak
isomorphism, without unfolding the predicate in an importing module. -/
theorem areWeaklyIsomorphicKernels_iff :
    AreWeaklyIsomorphicKernels μ ωX ν ωY ↔
      ∃ π : Measure (X × Y), IsCoupling π μ ν ∧
        (fun q : (X × Y) × (X × Y) ↦ ωX (q.1.1, q.2.1)) =ᵐ[π.prod π]
          (fun q ↦ ωY (q.1.2, q.2.2)) :=
  (Iff.rfl)

/-- A weak isomorphism of probability kernels admits a common probability parametrization on
the canonical carrier `X × Y`. -/
theorem AreWeaklyIsomorphicKernels.exists_probability_parametrization [IsProbabilityMeasure μ]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) :
    ∃ γ : Measure (X × Y), IsProbabilityMeasure γ ∧
      MeasurePreserving Prod.fst γ μ ∧ MeasurePreserving Prod.snd γ ν ∧
      (fun q : (X × Y) × (X × Y) ↦ ωX (q.1.1, q.2.1)) =ᵐ[γ.prod γ]
        (fun q ↦ ωY (q.1.2, q.2.2)) := by
  obtain ⟨π, hπ, heq⟩ := areWeaklyIsomorphicKernels_iff.mp h
  exact ⟨π, hπ.isProbabilityMeasure, hπ.measurePreserving_fst, hπ.measurePreserving_snd, heq⟩

/-- Exchanging the two kernels preserves weak isomorphism. No measurability of the target is
needed: the coordinate swap is a measurable equivalence. -/
protected theorem AreWeaklyIsomorphicKernels.symm [IsFiniteMeasure μ]
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) :
    AreWeaklyIsomorphicKernels ν ωY μ ωX := by
  obtain ⟨π, hπ, heq⟩ := areWeaklyIsomorphicKernels_iff.mp h
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  refine areWeaklyIsomorphicKernels_iff.mpr ⟨π.map Prod.swap, hπ.swap, ?_⟩
  rw [Measure.map_prod_map π π measurable_swap measurable_swap]
  have he : MeasurableEmbedding (Prod.map (Prod.swap : X × Y → Y × X) Prod.swap) :=
    (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding.prodMap
      (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding
  exact he.ae_map_iff.mpr heq.symm

/-- Almost-everywhere changes of the kernels preserve weak isomorphism. -/
theorem areWeaklyIsomorphicKernels_congr_ae [IsFiniteMeasure μ]
    (hX : ωX =ᵐ[μ.prod μ] ωX') (hY : ωY =ᵐ[ν.prod ν] ωY') :
    AreWeaklyIsomorphicKernels μ ωX ν ωY ↔ AreWeaklyIsomorphicKernels μ ωX' ν ωY' := by
  have transfer {a a' : X × X → Z} {b b' : Y × Y → Z}
      (ha : a =ᵐ[μ.prod μ] a') (hb : b =ᵐ[ν.prod ν] b')
      (h : AreWeaklyIsomorphicKernels μ a ν b) : AreWeaklyIsomorphicKernels μ a' ν b' := by
    obtain ⟨π, hπ, heq⟩ := areWeaklyIsomorphicKernels_iff.mp h
    have : IsFiniteMeasure π := hπ.isFiniteMeasure
    have ha' := (hπ.measurePreserving_fst.prod hπ.measurePreserving_fst).quasiMeasurePreserving
      |>.ae_eq_comp ha
    have hb' := (hπ.measurePreserving_snd.prod hπ.measurePreserving_snd).quasiMeasurePreserving
      |>.ae_eq_comp hb
    exact areWeaklyIsomorphicKernels_iff.mpr ⟨π, hπ, ha'.symm.trans (heq.trans hb')⟩
  exact ⟨transfer hX hY, transfer hX.symm hY.symm⟩

section PseudoEMetricSpace

variable [PseudoEMetricSpace Z]

/-- Weakly isomorphic kernels have zero Gromov–Wasserstein distance at every exponent.
This implication also holds at exponent zero. -/
theorem AreWeaklyIsomorphicKernels.gromovWassersteinEDist_eq_zero
    (h : AreWeaklyIsomorphicKernels μ ωX ν ωY) (p : ℝ≥0∞) :
    gromovWassersteinEDist p μ ωX ν ωY = 0 := by
  obtain ⟨π, hπ, heq⟩ := areWeaklyIsomorphicKernels_iff.mp h
  refine nonpos_iff_eq_zero.mp ((gromovWassersteinEDist_le hπ p ωX ωY).trans_eq ?_)
  rw [gromovWassersteinDistortion_def]
  have hzero : (fun q : (X × Y) × (X × Y) ↦
      edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) =ᵐ[π.prod π] 0 := by
    filter_upwards [heq] with q hq
    simp [hq]
  rw [eLpNorm_congr_ae hzero, eLpNorm_zero]

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace Z] {p : ℝ≥0∞}

/-- Weak isomorphism is equivalent to the existence of a zero-distortion coupling at any
nonzero exponent, including `∞`. This does not assert attainment of the distance infimum. -/
theorem areWeaklyIsomorphicKernels_iff_exists_distortion_eq_zero (hp : p ≠ 0) :
    AreWeaklyIsomorphicKernels μ ωX ν ωY ↔
      ∃ π : Measure (X × Y), IsCoupling π μ ν ∧
        gromovWassersteinDistortion p ωX ωY π = 0 := by
  simp only [areWeaklyIsomorphicKernels_iff, gromovWassersteinDistortion_eq_zero_iff hp]

/-- A common s-finite parametrizing measure with equal pulled-back kernels gives a weak
isomorphism. The witness coupling is the pushforward along the paired parametrizing maps. -/
theorem areWeaklyIsomorphicKernels_of_common_parametrization {γ : Measure Ω} [SFinite γ]
    {f : Ω → X} {g : Ω → Y} (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (heq : (fun q : Ω × Ω ↦ ωX (f q.1, f q.2)) =ᵐ[γ.prod γ]
      (fun q ↦ ωY (g q.1, g q.2))) : AreWeaklyIsomorphicKernels μ ωX ν ωY := by
  refine (areWeaklyIsomorphicKernels_iff_exists_distortion_eq_zero (p := ∞) ENNReal.top_ne_zero).mpr
    ⟨γ.map (fun w ↦ (f w, g w)), isCoupling_map_prodMk_of_measurePreserving hf hg, ?_⟩
  rw [gromovWassersteinDistortion_map_prodMk hf hg hωX hωY, eLpNorm_eq_zero_iff
    ENNReal.top_ne_zero]
  filter_upwards [heq] with q hq
  simp [hq]

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
kernel on the common glued space. -/
theorem AreWeaklyIsomorphicKernels.trans_of_exists_glue [IsFiniteMeasure ν]
    (hXY : AreWeaklyIsomorphicKernels μ ωX ν ωY)
    (hYW : AreWeaklyIsomorphicKernels ν ωY ρ ωW)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωW : AEStronglyMeasurable ωW (ρ.prod ρ))
    (hglue : ∀ π : Measure (X × Y), ∀ σ : Measure (Y × W),
      IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    AreWeaklyIsomorphicKernels μ ωX ρ ωW := by
  obtain ⟨π, hπ, heqXY⟩ := areWeaklyIsomorphicKernels_iff.mp hXY
  obtain ⟨σ, hσ, heqYW⟩ := areWeaklyIsomorphicKernels_iff.mp hYW
  obtain ⟨γ, hγπ, hγσ⟩ := hglue π σ hπ hσ
  have hleft : MeasurePreserving (Prod.map id Prod.fst) γ π :=
    ⟨measurable_id.prodMap measurable_fst, hγπ⟩
  have hright : MeasurePreserving Prod.snd γ σ := ⟨measurable_snd, hγσ⟩
  have : IsFiniteMeasure π := hπ.isFiniteMeasure_of_right
  have : IsFiniteMeasure (γ.map (Prod.map id Prod.fst)) := by rw [hγπ]; infer_instance
  have : IsFiniteMeasure γ := MeasureTheory.Measure.isFiniteMeasure_of_map
    hleft.measurable.aemeasurable
  have hX := hπ.measurePreserving_fst.comp hleft
  have hW := hσ.measurePreserving_snd.comp hright
  have heqXY' := (hleft.prod hleft).quasiMeasurePreserving.ae_eq_comp heqXY
  have heqYW' := (hright.prod hright).quasiMeasurePreserving.ae_eq_comp heqYW
  exact areWeaklyIsomorphicKernels_of_common_parametrization hX hW hωX hωW
    (heqXY'.trans heqYW')

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
