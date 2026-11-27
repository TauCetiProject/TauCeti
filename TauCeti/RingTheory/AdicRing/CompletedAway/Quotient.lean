/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedAway
public import TauCeti.RingTheory.AdicRing.Quotient

/-!
# Quotients of completed localizations

For a noetherian adic ring, taking a quotient commutes with completed localization.
The comparison identifies the quotient of the basic-open sections on the ambient formal
spectrum with the basic-open sections on the formal spectrum of the quotient.

See EGA I, Ch. 0, §7.6, and Ch. I, §10.14.
-/

public section

namespace TauCeti.AdicRing.CompletedAway

open Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [IsNoetherianRing A] (J : Ideal A) (f : A)

private noncomputable def quotientForward :
    (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) →+*
      CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f) := by
  let u := (algebraMap (A ⧸ J) (CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f))).comp
    (Ideal.Quotient.mk J)
  have hu : Continuous u := (continuous_algebraMap _ _).comp
    (QuotientRing.isOpenQuotientMap_mk J).continuous
  have huf : IsUnit (u f) := isUnit_algebraMap_self _ _
  refine Ideal.Quotient.lift _ (lift u hu huf) fun a ha ↦ ?_
  have hJ : J.map (algebraMap A (CompletedAway A f)) ≤ RingHom.ker (lift u hu huf) :=
    Ideal.map_le_iff_le_comap.mpr fun b hb ↦ RingHom.mem_ker.mpr (by
      rw [lift_algebraMap]
      simp only [u, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero])
  exact RingHom.mem_ker.mp (hJ ha)

private theorem continuous_quotientForward : Continuous (quotientForward J f) :=
  (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
    (continuous_lift _ _ _)

private theorem quotientForward_algebraMap (a : A) :
    quotientForward J f (Ideal.Quotient.mk _ (algebraMap A (CompletedAway A f) a)) =
      algebraMap (A ⧸ J) (CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f))
        (Ideal.Quotient.mk J a) := by
  simp only [quotientForward, Ideal.Quotient.lift_mk, lift_algebraMap, RingHom.comp_apply]

private noncomputable local instance : UniformSpace
    (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) :=
  IsTopologicalAddGroup.rightUniformSpace _

private local instance : IsUniformAddGroup
    (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) :=
  isUniformAddGroup_of_addCommGroup

private noncomputable def quotientBackward :
    CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f) →+*
      (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) :=
  lift (Ideal.quotientMap _ (algebraMap A (CompletedAway A f)) Ideal.le_comap_map)
    ((QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.continuous_iff.mpr
      ((QuotientRing.isOpenQuotientMap_mk _).continuous.comp (continuous_algebraMap A f)))
    (by
      rw [Ideal.quotientMap_mk]
      exact (isUnit_algebraMap_self A f).map (Ideal.Quotient.mk _))

private theorem continuous_quotientBackward : Continuous (quotientBackward J f) :=
  continuous_lift _ _ _

private theorem quotientBackward_algebraMap (a : A) :
    quotientBackward J f
        (algebraMap (A ⧸ J) (CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f))
          (Ideal.Quotient.mk J a)) =
      Ideal.Quotient.mk _ (algebraMap A (CompletedAway A f) a) := by
  rw [quotientBackward, lift_algebraMap, Ideal.quotientMap_mk]

/-- Completing the localization of `A ⧸ J` away from the image of `f` gives the quotient of
the completed localization of `A` at `f` by the extension of `J`. -/
noncomputable def quotientEquiv :
    (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) ≃+*
      CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f) :=
  RingEquiv.ofRingHom (quotientForward J f) (quotientBackward J f) (by
    apply ringHom_ext (A ⧸ J) (Ideal.Quotient.mk J f)
      ((continuous_quotientForward J f).comp (continuous_quotientBackward J f)) continuous_id
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply, quotientBackward_algebraMap, quotientForward_algebraMap,
        RingHom.id_apply]) (by
    have hπ := (QuotientRing.isOpenQuotientMap_mk
      (J.map (algebraMap A (CompletedAway A f)))).continuous
    apply Ideal.Quotient.ringHom_ext
    apply ringHom_ext A f
      (((continuous_quotientBackward J f).comp (continuous_quotientForward J f)).comp hπ) hπ
    exact RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply, quotientForward_algebraMap, quotientBackward_algebraMap])

/-- The forward quotient comparison is continuous for the quotient topology. -/
theorem continuous_quotientEquiv : Continuous (quotientEquiv J f) :=
  continuous_quotientForward J f

/-- The inverse quotient comparison is continuous. -/
theorem continuous_quotientEquiv_symm : Continuous (quotientEquiv J f).symm :=
  continuous_quotientBackward J f

/-- The quotient comparison takes the class of a coefficient to its image in the completed
localization of the quotient. -/
@[simp]
theorem quotientEquiv_algebraMap (a : A) :
    quotientEquiv J f
        (algebraMap A (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) a) =
      algebraMap (A ⧸ J) (CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f))
        (Ideal.Quotient.mk J a) := by
  rw [← Ideal.Quotient.mk_algebraMap]
  exact quotientForward_algebraMap J f a

/-- The inverse quotient comparison takes a localized coefficient to its class in the quotient
of the completed localization. -/
@[simp]
theorem quotientEquiv_symm_algebraMap (a : A) :
    (quotientEquiv J f).symm
        (algebraMap (A ⧸ J) (CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f))
          (Ideal.Quotient.mk J a)) =
      algebraMap A (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) a :=
  (RingEquiv.symm_apply_eq _).2 (quotientEquiv_algebraMap J f a).symm

end TauCeti.AdicRing.CompletedAway
