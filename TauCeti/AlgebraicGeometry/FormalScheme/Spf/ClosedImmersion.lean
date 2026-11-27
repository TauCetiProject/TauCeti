/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.RingTheory.AdicRing.CompletedAway.Quotient

import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Quotient inclusions of affine formal spectra

For a noetherian adic ring `A` and an arbitrary ideal `J`, the map
`Spf (A ⧸ J) ⟶ Spf A` embeds the source onto the open primes of `A` containing `J`.
On basic opens the map is the quotient by the extended ideal in the completed localization.
In particular it is surjective on stalks. These descriptions give the affine local model
for closed formal subschemes.

See EGA I, Ch. I, §§10.10 and 10.14.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace TauCeti.FormalScheme.Spf

universe u

section ClosedEmbedding

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]

/-- A continuous surjective ring homomorphism induces a closed embedding of the underlying
spaces of the formal spectra. -/
theorem isClosedEmbedding_map_base_of_surjective (φ : A →+* B) (hφ : Continuous φ)
    (hs : Function.Surjective φ) : IsClosedEmbedding (map φ hφ).base := by
  refine IsClosedEmbedding.of_comp (g := (Subtype.val : carrier A → PrimeSpectrum A))
    IsEmbedding.subtypeVal ?_
  have hbase : Subtype.val ∘ (map φ hφ).base = PrimeSpectrum.comap φ ∘ Subtype.val := by
    rw [map_base]
    exact funext (coe_comap_apply φ hφ)
  rw [hbase]
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective B φ hs).comp
    (isClosed_carrier (IsAdicRing.ideal_spec B).2.1).isClosedEmbedding_subtypeVal

end ClosedEmbedding

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [IsNoetherianRing A] (J : Ideal A)

local notation "qmap" => map (Ideal.Quotient.mk J)
  (IsOpenQuotientMap.continuous (QuotientRing.isOpenQuotientMap_mk J))

/-- The image of the formal quotient map consists of the open primes that contain the ideal. -/
theorem range_map_quotientMk_base :
    Set.range (qmap).base = Subtype.val ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) := by
  let φ := Ideal.Quotient.mk J
  have hφ := (QuotientRing.isOpenQuotientMap_mk J).continuous
  have hrange := _root_.range_comap_of_surjective (A ⧸ J) φ
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker (I := J)] at hrange
  rw [map_base]
  ext p
  simp only [← hrange]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.val, (coe_comap_apply φ hφ q).symm⟩
  · rintro ⟨q, hq⟩
    have hopen : q ∈ carrier (A ⧸ J) := by
      apply (mem_carrier (p := q)).mpr
      apply (QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.isOpen_preimage.mp
      have hs : IsOpen ((PrimeSpectrum.comap φ q).asIdeal : Set A) := by
        rw [hq]
        exact mem_carrier.mp p.property
      simpa only [PrimeSpectrum.comap_asIdeal, Ideal.coe_comap] using hs
    exact ⟨⟨q, hopen⟩, Subtype.ext ((coe_comap_apply φ hφ ⟨q, hopen⟩).trans hq)⟩

/-- The preimage of a principal open under a formal quotient map is the principal open of
the image of its defining element. -/
theorem map_quotientMk_preimage_basicOpen (f : A) :
    (Opens.map (qmap).base).obj (basicOpen f) = basicOpen (Ideal.Quotient.mk J f) := by
  rw [map_base]
  exact comap_basicOpen _ _ _

/-- Over a principal open, the formal quotient map is quotient by the extension of `J`
under the identifications of sections with completed localizations. -/
theorem map_quotientMk_appLE_basicOpen (f : A) :
    (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f).inv ≫
        (qmap).toHom.appLE (basicOpen f) (basicOpen (Ideal.Quotient.mk J f))
          (map_quotientMk_preimage_basicOpen J f).ge ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec (A ⧸ J)).2.1
          (IsAdicRing.ideal_spec (A ⧸ J)).1 (Ideal.Quotient.mk J f)).hom =
      CommRingCat.ofHom ((AdicRing.CompletedAway.quotientEquiv J f).toRingHom.comp
        (Ideal.Quotient.mk _)) := by
  apply map_appLE_basicOpen
  · exact (AdicRing.CompletedAway.continuous_quotientEquiv J f).comp
      (QuotientRing.isOpenQuotientMap_mk _).continuous
  · refine RingHom.ext fun a ↦ ?_
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Ideal.Quotient.mk_algebraMap] using
      AdicRing.CompletedAway.quotientEquiv_algebraMap J f a

/-- The formal quotient map is surjective on sections over every principal open. -/
theorem map_quotientMk_appLE_basicOpen_surjective (f : A) :
    Function.Surjective ((qmap).toHom.appLE (basicOpen f) (basicOpen (Ideal.Quotient.mk J f))
      (map_quotientMk_preimage_basicOpen J f).ge) := by
  let eA := basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
  let eB := basicOpenSectionsIso (IsAdicRing.ideal_spec (A ⧸ J)).2.1
    (IsAdicRing.ideal_spec (A ⧸ J)).1 (Ideal.Quotient.mk J f)
  have h : Function.Surjective ((AdicRing.CompletedAway.quotientEquiv J f).toRingHom.comp
      (Ideal.Quotient.mk _)) :=
    (AdicRing.CompletedAway.quotientEquiv J f).surjective.comp Ideal.Quotient.mk_surjective
  intro y
  obtain ⟨x, hx⟩ := h (eB.hom y)
  refine ⟨eA.inv x, (ConcreteCategory.bijective_of_isIso eB.hom).1 ?_⟩
  exact (ConcreteCategory.congr_hom (map_quotientMk_appLE_basicOpen J f) x).trans hx

/-- The map of local rings induced by a formal quotient inclusion is surjective. -/
theorem map_quotientMk_stalkMap_surjective (q : Spf (A ⧸ J)) :
    Function.Surjective ((qmap).stalkMap q) := by
  intro x
  obtain ⟨U, hq, t, rfl⟩ := (Spf (A ⧸ J)).presheaf.exists_germ_eq x
  obtain ⟨b, hb, hbU⟩ := exists_basicOpen_le hq
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) b
  let p := (qmap).base q
  have hp : p ∈ basicOpen f := (map_quotientMk_preimage_basicOpen J f).ge hb
  obtain ⟨s, hs⟩ := map_quotientMk_appLE_basicOpen_surjective J f
    ((Spf (A ⧸ J)).presheaf.map (homOfLE hbU).op t)
  refine ⟨(Spf A).presheaf.germ (basicOpen f) p hp s, ?_⟩
  have hpre := (map_quotientMk_preimage_basicOpen J f).ge
  erw [LocallyRingedSpace.stalkMap_germ_apply (qmap) (basicOpen f) q hp s,
    ← (Spf (A ⧸ J)).presheaf.germ_res_apply (homOfLE hpre) q hb,
    ← CommRingCat.comp_apply ((qmap).c.app (op (basicOpen f)))
      ((Spf (A ⧸ J)).presheaf.map (homOfLE hpre).op) s,
    ← PresheafedSpace.Hom.appLE_def (qmap).toHom (basicOpen f) (basicOpen _) hpre, hs]
  exact (Spf (A ⧸ J)).presheaf.germ_res_apply (homOfLE hbU) q hb t

end TauCeti.FormalScheme.Spf
