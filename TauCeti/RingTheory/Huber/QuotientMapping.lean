/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Quotient mappings of Huber pairs

A quotient mapping of Huber pairs is an open surjection on the underlying topological rings,
with target plus ring the integral closure of the image of the source plus ring. These are the
quotient maps used in presentations of affinoid algebras topologically of finite type.

`Pair.Hom.IsQuotientMapping` records both conditions. Canonical quotient-pair maps are quotient
mappings, and quotient mappings compose. The first isomorphism theorem identifies the target
with the quotient pair by the kernel: `IsQuotientMapping.quotientKerInverse` is inverse to the
canonical factorisation, as a continuous morphism preserving the plus rings in both directions.
No completeness or separation hypothesis is needed for these statements. The inverse uses
Mathlib's `RingHom.quotientKerEquivOfSurjective` and the topological refinement
`RingHom.isHomeomorph_kerLift`; the new content is preservation of the quotient plus ring.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 7.22 and 8.42.
-/

public section

open Topology

namespace TauCeti.Huber.Pair.Hom

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- A quotient mapping of Huber pairs is an open quotient map of underlying rings whose target
plus ring is the integral closure of the image of the source plus ring. -/
structure IsQuotientMapping (f : Hom S T) : Prop where
  /-- The underlying ring map is continuous, open and surjective. -/
  isOpenQuotientMap : IsOpenQuotientMap f.toRingHom
  /-- The plus ring has the quotient-pair integral closure. -/
  plus_eq : T.plus = (integralClosure (S.plus.map f.toRingHom) B).toSubring

/-- Characterisation of quotient mappings by the underlying topology and plus ring. -/
theorem isQuotientMapping_iff (f : Hom S T) :
    IsQuotientMapping f ↔ IsOpenQuotientMap f.toRingHom ∧
      T.plus = (integralClosure (S.plus.map f.toRingHom) B).toSubring :=
  ⟨fun h ↦ ⟨h.isOpenQuotientMap, h.plus_eq⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Membership in the target plus ring is integrality over the image of the source plus ring. -/
theorem IsQuotientMapping.mem_plus_iff {f : Hom S T} (hf : IsQuotientMapping f) {b : B} :
    b ∈ T.plus ↔ IsIntegral (S.plus.map f.toRingHom) b := by
  rw [hf.plus_eq, Subalgebra.mem_toSubring, mem_integralClosure_iff]

/-- A pair morphism that is an open quotient map is a quotient mapping if every target plus
ring element is integral over the image plus ring. The other inclusion is automatic. -/
theorem isQuotientMapping_iff_isIntegral (f : Hom S T) :
    IsQuotientMapping f ↔ IsOpenQuotientMap f.toRingHom ∧
      ∀ b ∈ T.plus, IsIntegral (S.plus.map f.toRingHom) b := by
  constructor
  · intro hf
    exact ⟨hf.isOpenQuotientMap, fun _ hb ↦ hf.mem_plus_iff.mp hb⟩
  · rintro ⟨hopen, hint⟩
    refine ⟨hopen, le_antisymm (fun b hb ↦ hint b hb) ?_⟩
    let := T.isRingOfIntegralElements.isIntegrallyClosedIn
    apply Subring.integralClosure_subring_le_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact f.map_mem_plus a ha

/-- The identity of a Huber pair is a quotient mapping. -/
@[simp]
theorem isQuotientMapping_id (S : Pair A) : IsQuotientMapping (id S) := by
  apply (isQuotientMapping_iff_isIntegral _).mpr
  refine ⟨?_, fun a ha ↦ ?_⟩
  · simpa only [toRingHom_id, RingHom.coe_id] using (IsOpenQuotientMap.id (X := A))
  · rw [toRingHom_id, Subring.map_id]
    exact isIntegral_algebraMap (R := S.plus) (x := ⟨a, ha⟩)

/-- The canonical map to a quotient Huber pair is a quotient mapping, even when the ideal
is not closed. -/
@[simp]
theorem isQuotientMapping_quotientHom (S : Pair A) (J : Ideal A) :
    IsQuotientMapping (Pair.quotientHom S J) := by
  refine ⟨?_, ?_⟩
  · rw [toRingHom_quotientHom]
    exact QuotientRing.isOpenQuotientMap_mk J
  · rw [toRingHom_quotientHom, Pair.quotient_plus]

/-- Quotient mappings of Huber pairs compose. In particular, successive quotient presentations
have the same integral closure condition as their composite presentation. -/
theorem IsQuotientMapping.comp {f : Hom S T} {g : Hom T U}
    (hg : IsQuotientMapping g) (hf : IsQuotientMapping f) : IsQuotientMapping (g.comp f) := by
  apply (isQuotientMapping_iff_isIntegral _).mpr
  refine ⟨?_, fun c hc ↦ ?_⟩
  · simpa only [toRingHom_comp, RingHom.coe_comp] using
      hg.isOpenQuotientMap.comp hf.isOpenQuotientMap
  · let R := S.plus.map (g.comp f).toRingHom
    let V := (integralClosure R C).toSubring
    have hmap : T.plus.map g.toRingHom ≤ V := by
      rintro _ ⟨b, hb, rfl⟩
      have hR : (S.plus.map f.toRingHom).map g.toRingHom = R := by
        simp only [R, toRingHom_comp, Subring.map_map]
      let φ : S.plus.map f.toRingHom →+* R :=
        g.toRingHom.restrict _ R fun b hb ↦ hR ▸ Subring.mem_map.mpr ⟨b, hb, rfl⟩
      exact (hf.mem_plus_iff.mp hb).map_of_comp_eq φ g.toRingHom (by ext; rfl)
    have hcl : (integralClosure (T.plus.map g.toRingHom) C).toSubring ≤ V :=
      Subring.integralClosure_subring_le_iff.mpr hmap
    exact hcl (hg.mem_plus_iff.mp hc)

/-- For a quotient mapping, the inverse of the first-isomorphism-theorem ring equivalence
is a continuous morphism of Huber pairs. The source of the inverse is the target pair, and its
target is the canonical quotient pair by the kernel. -/
noncomputable def IsQuotientMapping.quotientKerInverse {f : Hom S T}
    (hf : IsQuotientMapping f) : Hom T (S.quotient (RingHom.ker f.toRingHom)) where
  toRingHom := (RingHom.quotientKerEquivOfSurjective hf.isOpenQuotientMap.surjective).symm
  continuous_toRingHom := by
    let e := RingHom.quotientKerEquivOfSurjective hf.isOpenQuotientMap.surjective
    have he : (e : A ⧸ RingHom.ker f.toRingHom → B) = RingHom.kerLift f.toRingHom := by
      funext x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [e, RingHom.quotientKerEquivOfSurjective_apply_mk, RingHom.kerLift_mk]
    have hhome : IsHomeomorph e := he ▸
      f.toRingHom.isHomeomorph_kerLift hf.isOpenQuotientMap.isQuotientMap
    exact e.toEquiv.toHomeomorphOfContinuousOpen hhome.continuous hhome.isOpenMap
      |>.symm.continuous
  map_mem_plus := by
    intro b hb
    let e := RingHom.quotientKerEquivOfSurjective hf.isOpenQuotientMap.surjective
    let R := S.plus.map f.toRingHom
    let Q := S.plus.map (Ideal.Quotient.mk (RingHom.ker f.toRingHom))
    let φ : R →+* Q := e.symm.toRingHom.restrict R Q fun b hb ↦ by
      obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hb
      simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingHom.quotientKerEquivOfSurjective_symm_apply]
      exact Subring.mem_map.mpr ⟨a, ha, rfl⟩
    rw [Pair.quotient_plus, Subalgebra.mem_toSubring, mem_integralClosure_iff]
    exact (hf.mem_plus_iff.mp hb).map_of_comp_eq φ e.symm.toRingHom (by ext; rfl)

/-- The underlying ring homomorphism of the inverse is the inverse first-isomorphism-theorem
ring equivalence. -/
@[simp]
theorem IsQuotientMapping.toRingHom_quotientKerInverse {f : Hom S T}
    (hf : IsQuotientMapping f) :
    hf.quotientKerInverse.toRingHom =
      (RingHom.quotientKerEquivOfSurjective hf.isOpenQuotientMap.surjective).symm.toRingHom :=
  (rfl)

/-- The factorisation through the kernel quotient followed by its inverse is the identity. -/
@[simp]
theorem IsQuotientMapping.quotientKerInverse_comp_quotientLift {f : Hom S T}
    (hf : IsQuotientMapping f) :
    hf.quotientKerInverse.comp (f.quotientLift (RingHom.ker f.toRingHom) le_rfl) =
      id (S.quotient (RingHom.ker f.toRingHom)) := by
  apply Hom.ext
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp

/-- The inverse followed by the factorisation through the kernel quotient is the identity. -/
@[simp]
theorem IsQuotientMapping.quotientLift_comp_quotientKerInverse {f : Hom S T}
    (hf : IsQuotientMapping f) :
    (f.quotientLift (RingHom.ker f.toRingHom) le_rfl).comp hf.quotientKerInverse = id T := by
  apply Hom.ext
  ext b
  obtain ⟨a, rfl⟩ := hf.isOpenQuotientMap.surjective b
  simp

end TauCeti.Huber.Pair.Hom
