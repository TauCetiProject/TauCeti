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

/-- Completing the localization of `A ⧸ J` away from the image of `f` gives the quotient of
the completed localization of `A` at `f` by the extension of `J`. -/
noncomputable def quotientEquiv :
    (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) ≃+*
      CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f) := by
  let S := CompletedAway A f
  let T := CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f)
  let π : S →+* S ⧸ J.map (algebraMap A S) := Ideal.Quotient.mk _
  let u : A →+* T := (algebraMap (A ⧸ J) T).comp (Ideal.Quotient.mk J)
  have hu : Continuous u := (continuous_algebraMap _ _).comp
    (QuotientRing.isOpenQuotientMap_mk J).continuous
  have huf : IsUnit (u f) := isUnit_algebraMap_self _ _
  let g := lift u hu huf
  have hJ : J.map (algebraMap A S) ≤ RingHom.ker g :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ RingHom.mem_ker.mpr (by
      rw [lift_algebraMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
  let gQuot : S ⧸ J.map (algebraMap A S) →+* T :=
    Ideal.Quotient.lift _ g fun _ hx ↦ RingHom.mem_ker.mp (hJ hx)
  have hgQuot : Continuous gQuot :=
    (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
      (continuous_lift u hu huf)
  let v : A ⧸ J →+* S ⧸ J.map (algebraMap A S) :=
    Ideal.quotientMap _ (algebraMap A S) Ideal.le_comap_map
  have hπ : Continuous π := (QuotientRing.isOpenQuotientMap_mk _).continuous
  have hv : Continuous v := (QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.continuous_iff.mpr
    (hπ.comp (continuous_algebraMap A f))
  have hvf : IsUnit (v (Ideal.Quotient.mk J f)) :=
    (isUnit_algebraMap_self A f).map π
  letI := IsTopologicalAddGroup.rightUniformSpace (S ⧸ J.map (algebraMap A S))
  letI : IsUniformAddGroup (S ⧸ J.map (algebraMap A S)) :=
    isUniformAddGroup_of_addCommGroup
  let h := lift v hv hvf
  have hh := continuous_lift v hv hvf
  have hforward (a : A) : gQuot (π (algebraMap A S a)) = u a :=
    (Ideal.Quotient.lift_mk _ _ _).trans (lift_algebraMap u hu huf a)
  have hback (a : A) : h (algebraMap (A ⧸ J) T (Ideal.Quotient.mk J a)) =
      π (algebraMap A S a) :=
    (lift_algebraMap v hv hvf _).trans Ideal.quotientMap_mk
  refine RingEquiv.ofRingHom gQuot h ?_ ?_
  · apply ringHom_ext (A ⧸ J) (Ideal.Quotient.mk J f) (hgQuot.comp hh) continuous_id
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun a ↦ (congrArg gQuot (hback a)).trans (hforward a)
  · apply Ideal.Quotient.ringHom_ext
    apply ringHom_ext A f ((hh.comp hgQuot).comp hπ) hπ
    exact RingHom.ext fun a ↦ (congrArg h (hforward a)).trans (hback a)

/-- The forward quotient comparison is continuous for the quotient topology. -/
theorem continuous_quotientEquiv : Continuous (quotientEquiv J f) := by
  unfold quotientEquiv
  exact (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
    (continuous_lift _ _ _)

/-- The inverse quotient comparison is continuous. -/
theorem continuous_quotientEquiv_symm : Continuous (quotientEquiv J f).symm := by
  let S := CompletedAway A f
  let := IsTopologicalAddGroup.rightUniformSpace (S ⧸ J.map (algebraMap A S))
  let : IsUniformAddGroup (S ⧸ J.map (algebraMap A S)) :=
    isUniformAddGroup_of_addCommGroup
  unfold quotientEquiv
  exact continuous_lift _ _ _

/-- The quotient comparison takes the class of a coefficient to its image in the completed
localization of the quotient. -/
@[simp]
theorem quotientEquiv_algebraMap (a : A) :
    quotientEquiv J f
        (algebraMap A (CompletedAway A f ⧸ J.map (algebraMap A (CompletedAway A f))) a) =
      algebraMap (A ⧸ J) (CompletedAway (A ⧸ J) (Ideal.Quotient.mk J f))
        (Ideal.Quotient.mk J a) := by
  unfold quotientEquiv
  rw [← Ideal.Quotient.mk_algebraMap, RingEquiv.ofRingHom_apply, Ideal.Quotient.lift_mk,
    lift_algebraMap]
  rfl

end TauCeti.AdicRing.CompletedAway
