/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.Limits.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.WithTopology

/-!
# Maps into limits of spectral spaces

Spectrality of a map from a compact quasiseparated space into a limit of spectral spaces can be
checked on the coordinate maps. No filteredness assumption is needed for this assertion: finite
intersections of inverse images of compact opens form a basis of the limit topology.

For a cofiltered diagram, a map from a compact, quasi-sober, quasiseparated prespectral space
into its limit is generalizing if all its coordinate maps are generalizing and spectral. To lift a
generalization, consider the sets of lifts at each coordinate inside the constructible space of the
source. They are nonempty compact
closed sets, directed by reverse inclusion. A point in their intersection gives the required
simultaneous lift. Thus a surjective such map is a quotient map.

The results use arbitrary limiting cones, so they apply without transporting to a particular
compatible-locus model of the limit.

## References

* P. Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.11 and its proof.
-/

public section

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace TopCat

universe v u w

variable {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{max v u})
  [∀ j, SpectralSpace (F.obj j)]
  (hF : ∀ {i j} (a : i ⟶ j), IsSpectralMap (F.map a))
  (c : Cone F) (hc : IsLimit c)

include hc

include hF in
/-- A map from a compact quasiseparated space to a limit of spectral spaces is spectral exactly
when all its coordinate maps are spectral. This holds for arbitrary small diagrams. -/
theorem isSpectralMap_of_isLimit_iff {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : Y → c.pt) :
    IsSpectralMap f ↔ ∀ j, IsSpectralMap (c.π.app j ∘ f) := by
  constructor
  · intro hf j
    exact (isSpectralMap_of_isLimit_π F hF c hc j).comp hf
  · intro h
    have hB := IsTopologicalBasis.iInf_induced (β := c.pt)
      (fun j ↦ PrespectralSpace.isTopologicalBasis (X := F.obj j))
      (fun j ↦ (c.π.app j : c.pt → F.obj j))
    rw [← induced_of_isLimit c hc] at hB
    have hopen : ∀ U ∈ {S | ∃ (U : ∀ j, Set (F.obj j)) (s : Finset J),
        (∀ j ∈ s, IsOpen (U j) ∧ IsCompact (U j)) ∧ S = ⋂ j ∈ s, c.π.app j ⁻¹' U j},
        IsOpen (f ⁻¹' U) := by
      rintro _ ⟨U, s, hU, rfl⟩
      simp only [preimage_iInter]
      exact isOpen_biInter_finset fun j hj ↦ (hU j hj).1.preimage (h j).continuous
    refine TauCeti.isSpectralMap_of_isTopologicalBasis hB
      (hB.continuous_iff.mpr hopen) ?_
    rintro _ ⟨U, s, hU, rfl⟩
    simp only [preimage_iInter]
    -- Quasiseparatedness controls nonempty intersections; compactness controls the empty one.
    simpa only [sInter_image, Finset.mem_coe, preimage_comp] using
      (QuasiSeparatedSpace.isCompact_sInter
        (s.finite_toSet.image (fun j ↦ (c.π.app j ∘ f) ⁻¹' U j))
        (by rintro _ ⟨j, hj, rfl⟩; exact Or.inl ((hU j hj).1.preimage (h j).continuous))
        (by
          rintro _ ⟨j, hj, rfl⟩
          exact (h j).isCompact_preimage_of_isOpen (hU j hj).1 (hU j hj).2))

/-- For a cofiltered limit of spectral spaces, generalizing spectral coordinate maps lift
simultaneously: the induced map into the limit is generalizing. The source need only be compact,
quasi-sober, quasiseparated and prespectral. -/
theorem generalizingMap_of_isLimit [IsCofiltered J] {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [QuasiSober Y] [PrespectralSpace Y] [QuasiSeparatedSpace Y] (f : Y → c.pt)
    (hs : ∀ j, IsSpectralMap (c.π.app j ∘ f))
    (hg : ∀ j, GeneralizingMap (c.π.app j ∘ f)) : GeneralizingMap f := by
  intro y z hz
  let t : J → Set (WithConstructibleTopology Y) := fun j ↦
    {y' | WithTopology.ofTopology y' ⤳ y ∧
      c.π.app j (f (WithTopology.ofTopology y')) = c.π.app j z}
  have hclosed (j : J) : IsClosed (t j) := by
    have hgen : IsClosed (WithTopology.ofTopology ⁻¹' {y' : Y | y' ⤳ y} :
        Set (WithConstructibleTopology Y)) := by
      rw [WithConstructibleTopology.isClosed_iff]
      exact TauCeti.isProConstructible_iff_isClosed.mp
        (TauCeti.isProConstructible_setOfPred_specializes y)
    have hfiber : IsClosed {y' : WithConstructibleTopology Y |
        c.π.app j (f (WithTopology.ofTopology y')) = c.π.app j z} := by
      simpa only [Function.comp_apply, WithTopology.toTopology_inj] using
        (isClosed_eq (hs j).continuous_withConstructibleTopology
          (continuous_const (y := WithTopology.toTopology _ (c.π.app j z))))
    exact hgen.inter hfiber
  have hnonempty (j : J) : (t j).Nonempty := by
    obtain ⟨y', hy', heq⟩ := hg j (hz.map (c.π.app j).hom.continuous)
    exact ⟨WithTopology.toTopology _ y', hy', heq⟩
  have hmono {i j : J} (a : i ⟶ j) : t i ⊆ t j := by
    intro y' hy'
    refine ⟨hy'.1, ?_⟩
    have hn (x : c.pt) : F.map a (c.π.app i x) = c.π.app j x :=
      ConcreteCategory.congr_hom (c.w a) x
    rw [← hn, hy'.2, hn]
  have : Nonempty J := IsCofiltered.nonempty
  obtain ⟨y', hy'⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun i j ↦ ⟨IsCofiltered.min i j, hmono (IsCofiltered.minToLeft i j),
      hmono (IsCofiltered.minToRight i j)⟩)
    hnonempty (fun j ↦ (hclosed j).isCompact) hclosed
  have hall := mem_iInter.mp hy'
  refine ⟨WithTopology.ofTopology y', (hall (Classical.choice inferInstance)).1, ?_⟩
  exact ConcreteCategory.congr_hom (hc.hom_ext
    (f' := TopCat.ofHom ⟨fun _ : PUnit ↦ z, continuous_const⟩)
    (f := TopCat.ofHom ⟨fun _ : PUnit ↦ f (WithTopology.ofTopology y'), continuous_const⟩)
    (fun j ↦ by ext; exact (hall j).2)) PUnit.unit

include hF in
/-- A surjective map into a cofiltered limit of spectral spaces is a quotient map if all its
coordinate maps are generalizing and spectral. The source need only be compact, quasi-sober,
quasiseparated and prespectral. -/
theorem isQuotientMap_of_isLimit [IsCofiltered J] {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [QuasiSober Y] [PrespectralSpace Y] [QuasiSeparatedSpace Y]
    (f : Y → c.pt) (hf : Function.Surjective f)
    (hs : ∀ j, IsSpectralMap (c.π.app j ∘ f))
    (hg : ∀ j, GeneralizingMap (c.π.app j ∘ f)) : IsQuotientMap f := by
  have := spectralSpace_of_isLimit F hF c hc
  exact ((isSpectralMap_of_isLimit_iff F hF c hc f).mpr hs).isQuotientMap_of_generalizingMap
    (generalizingMap_of_isLimit F c hc f hs hg) hf

end TopCat
