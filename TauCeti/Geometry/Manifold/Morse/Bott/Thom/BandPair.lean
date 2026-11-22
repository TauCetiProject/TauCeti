/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
import TauCeti.Geometry.Manifold.Morse.Deformation.Cohomology

/-!
# Thom pair identifications for cobordism bands and preconnected Morse–Bott submanifolds

This file records corollaries of
`IsNondegenerateCriticalSubmanifold.nonempty_singularHomology_sublevelPair_iso_thomPair`
and `IsNondegenerateCriticalSubmanifold.nonempty_singularCohomology_sublevelPair_iso_thomPair`
from `TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair`:

* For a preconnected critical submanifold `S`, the Morse index is constant, so the relative
  homology and cohomology across the band are those of the Thom pair of rank
  `manifoldMorseIndex I f (i s₀)`
  (`nonempty_singularHomology_sublevelPair_iso_thomPair_of_preconnectedSpace`,
  `nonempty_singularCohomology_sublevelPair_iso_thomPair_of_preconnectedSpace`).
* Because the lower boundary level `a` is regular, the cobordism band pair `(f⁻¹[a, b], f⁻¹(a))`
  (`TauCeti.bandPair`) also has the relative homology and cohomology of the Thom pair
  (`nonempty_singularHomology_bandPair_iso_thomPair`,
  `nonempty_singularCohomology_bandPair_iso_thomPair`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' P : Type*} {S : Type u} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Relative homology across a connected compact Morse–Bott submanifold.** On a connected
compact Morse–Bott submanifold the Morse index is constant, so the relative homology of any
compact isolated band around its level is that of the Thom pair of its negative normal bundle of
rank `manifoldMorseIndex I f (i s₀)`. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair_of_preconnectedSpace
    [PreconnectedSpace S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) (s₀ : S)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
      (thomPair (Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
        fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s).singularHomology R n) :=
  h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact hcrit hdim g
    (fun s ↦ (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀)
    R n

/-- **Relative homology of a compact cobordism across a Morse–Bott submanifold.** Under the
hypotheses of `nonempty_singularHomology_sublevelPair_iso_thomPair`, the lower level `a` is
regular, so the band pair `(f⁻¹[a, b], f⁻¹(a))` also has the relative homology of the Thom pair
`(ν⁻, ν⁻₀)`. -/
theorem nonempty_singularHomology_bandPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((bandPair f (hac.trans hcb).le).singularHomology R n ≅
      (thomPair (Fin r → ℝ)
        fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s).singularHomology R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have ha : IsRegularValue I 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hxc, hx⟩ ↦ by
      obtain ⟨s, rfl⟩ := hcrit ⟨hxc, le_of_eq hx.symm, hx.le.trans (hac.trans hcb).le⟩
      exact hac.ne (hx.symm.trans (hc s))
  have := isIso_singularHomologyMap_bandPairInclusion hfs (hac.trans hcb).le hcompact ha R n
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
    hcrit hdim g hr R n
  exact ⟨asIso (TopPair.singularHomologyMap (bandPairInclusion f (hac.trans hcb).le) R n) ≪≫ e⟩

/-- **Relative cohomology across a connected compact Morse–Bott submanifold.** On a connected
compact Morse–Bott submanifold the Morse index is constant, so the relative cohomology of any
compact isolated band around its level is that of the Thom pair of its negative normal bundle of
rank `manifoldMorseIndex I f (i s₀)`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_thomPair_of_preconnectedSpace
    [PreconnectedSpace S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) (s₀ : S)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (N : C) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularCohomology R k N n ≅
      (thomPair (Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
        fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s).singularCohomology
        R k N n) :=
  h.nonempty_singularCohomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact hcrit hdim g
    (fun s ↦ (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀)
    R k N n

/-- **Relative cohomology of a compact cobordism across a Morse–Bott submanifold.** Under the
hypotheses of `nonempty_singularCohomology_sublevelPair_iso_thomPair`, the lower level `a` is
regular, so the band pair `(f⁻¹[a, b], f⁻¹(a))` also has the relative cohomology of the Thom pair
`(ν⁻, ν⁻₀)`. -/
theorem nonempty_singularCohomology_bandPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    {C : Type w} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (N : C) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((bandPair f (hac.trans hcb).le).singularCohomology R k N n ≅
      (thomPair (Fin r → ℝ)
        fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s).singularCohomology
        R k N n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have ha : IsRegularValue I 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hxc, hx⟩ ↦ by
      obtain ⟨s, rfl⟩ := hcrit ⟨hxc, le_of_eq hx.symm, hx.le.trans (hac.trans hcb).le⟩
      exact hac.ne (hx.symm.trans (hc s))
  have := isIso_singularCohomologyMap_bandPairInclusion hfs (hac.trans hcb).le hcompact ha R k N n
  obtain ⟨e⟩ := h.nonempty_singularCohomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
    hcrit hdim g hr R k N n
  exact ⟨(asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
    (bandPairInclusion f (hac.trans hcb).le) n)).symm ≪≫ e⟩

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
