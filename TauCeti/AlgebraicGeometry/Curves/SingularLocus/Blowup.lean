/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
public import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Blowing up the singular subscheme of a relative curve

For a syntomic relative curve over an arbitrary commutative ring, blowing up the singular
subscheme is an isomorphism over the smooth locus. Thus modifications obtained by blowing up
the singular subscheme preserve the smooth part of the curve: two points of the blowup with the
same smooth image are equal, and exactly one point of the blowup lies over each smooth point.

## Main results

* `AlgebraicGeometry.Scheme.isIso_blowupToBase_singularLocus_restrict_smoothLocus`: the blowup is
  an isomorphism over the smooth locus.
* `AlgebraicGeometry.Scheme.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus` and
  `AlgebraicGeometry.Scheme.natCard_preimage_blowupToBase_singularLocus_eq_one_of_mem_smoothLocus`:
  one point of the blowup lies over each smooth point.

## References

* The Stacks Project, Lemma 31.32.4, Tag 02OG (blowups away from their centre).
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Blowing up the singular subscheme of a syntomic relative curve changes nothing over its
smooth locus. -/
theorem isIso_blowupToBase_singularLocus_restrict_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    IsIso ((X.singularLocus R).blowupToBase ∣_ (X ↘ Spec (.of R)).smoothLocus) := by
  apply IdealSheafData.isIso_blowupToBase_restrict_of_disjoint_support
  rw [X.support_singularLocus_eq_compl_smoothLocus]
  exact disjoint_compl_right

/-- **Blowing up the singular subscheme is injective over the smooth locus.** Two points of the
blowup of a syntomic relative curve along its singular subscheme with the same smooth image are
equal. -/
theorem eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] {b b' : (X.singularLocus R).blowup}
    (h : (X.singularLocus R).blowupToBase b = (X.singularLocus R).blowupToBase b')
    (hb : (X.singularLocus R).blowupToBase b ∈ (X ↘ Spec (.of R)).smoothLocus) : b = b' := by
  let U := (X ↘ Spec (.of R)).smoothLocus
  let f := (X.singularLocus R).blowupToBase
  have := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := R)
  have hb' : f b' ∈ U := h ▸ hb
  have := (f ∣_ U).homeomorph.injective (a₁ := ⟨b, hb⟩) (a₂ := ⟨b', hb'⟩)
    (Subtype.ext ((morphismRestrict_base_coe f U ⟨b, hb⟩).trans
      (h.trans (morphismRestrict_base_coe f U ⟨b', hb'⟩).symm)))
  exact congr(($this).val)

/-- **One point of the blowup lies over each smooth point.** Blowing up the singular subscheme of
a syntomic relative curve changes nothing over its smooth locus. -/
theorem natCard_preimage_blowupToBase_singularLocus_eq_one_of_mem_smoothLocus
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] {x : X}
    (hx : x ∈ (X ↘ Spec (.of R)).smoothLocus) :
    Nat.card ((X.singularLocus R).blowupToBase ⁻¹' {x}) = 1 := by
  let f := (X.singularLocus R).blowupToBase
  have := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := R)
  obtain ⟨⟨b, hb⟩, hbx⟩ := (f ∣_ (X ↘ Spec (.of R)).smoothLocus).homeomorph.surjective ⟨x, hx⟩
  have hbx : f b = x := (morphismRestrict_base_coe f _ ⟨b, hb⟩).symm.trans congr(($hbx).val)
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨b, hbx⟩, fun b' ↦ Subtype.ext ?_⟩
  have hb' : f b'.val = x := b'.property
  exact X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus (hb'.trans hbx.symm)
    (by rwa [hb'])

end AlgebraicGeometry.Scheme
