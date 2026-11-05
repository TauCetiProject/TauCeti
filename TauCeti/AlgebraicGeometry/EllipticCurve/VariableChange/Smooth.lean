/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Smooth projection of the Weierstrass coordinate-change scheme

The ring of Weierstrass coordinate changes over a ring `B` is
`ChangeRing B = B[u, u⁻¹, r, s, t]`. Its projection to `Spec B` is smooth of relative
dimension four and faithfully flat. The identity change gives a section, so the projection
is surjective even over rings with nilpotents and in characteristics two and three.

These results hold over an arbitrary commutative coefficient ring. Their application to the
source and target projections of the Weierstrass groupoid is in
`TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/Groupoid.lean`.

The smoothness proof uses Mathlib's standard-smooth presentations of polynomial algebras
and principal localizations.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the Weierstrass
  groupoid and its coefficient and arrow rings.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.WeierstrassChange.ChangeRing

variable (B : Type*) [CommRing B]

/-- The coordinate algebra of Weierstrass changes is standard smooth of relative dimension
four over its coefficient ring. -/
instance isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension 4 B (ChangeRing B) := by
  let := Algebra.IsStandardSmoothOfRelativeDimension.localization_away
    (S := ChangeRing B) (MvPolynomial.X 0 : MvPolynomial (Fin 4) B)
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 4 0 B
    (MvPolynomial (Fin 4) B) (ChangeRing B)

/-- Adjoining a Weierstrass coordinate change is faithfully flat: the identity change
sections the projection on prime spectra. -/
instance faithfullyFlat : Module.FaithfullyFlat B (ChangeRing B) := by
  let e : ChangeRing B →+* B := lift (RingHom.id B, 1)
  have he : e.comp (algebraMap B (ChangeRing B)) = RingHom.id B :=
    lift_comp_algebraMap _
  refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ⟨PrimeSpectrum.comap e p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, he, PrimeSpectrum.comap_id]

/-- The projection from the scheme of coordinate changes is smooth of relative dimension
four. -/
instance smoothOfRelativeDimension_specMap :
    SmoothOfRelativeDimension 4
      (Spec.map (CommRingCat.ofHom (algebraMap B (ChangeRing B)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 4)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 4).mpr inferInstance)

/-- The projection from the scheme of coordinate changes is smooth. -/
instance smooth_specMap :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap B (ChangeRing B)))) :=
  SmoothOfRelativeDimension.smooth 4 _

/-- Every coefficient-ring point has a coordinate change above it. -/
instance surjective_specMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap B (ChangeRing B)))) :=
  ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr (faithfullyFlat B))).2

end TauCeti.WeierstrassChange.ChangeRing
