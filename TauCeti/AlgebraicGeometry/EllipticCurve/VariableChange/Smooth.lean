/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Smooth projections of the Weierstrass groupoid

The ring of Weierstrass coordinate changes over a ring `B` is
`ChangeRing B = B[u, u⁻¹, r, s, t]`. Its projection to `Spec B` is smooth of relative
dimension four and faithfully flat. The identity change gives a section, so the projection
is surjective even over rings with nilpotents and in characteristics two and three.

For the universal coefficient ring, the two projections of the represented Weierstrass
groupoid are the spectra of the left and right units of its Hopf algebroid. Inversion
exchanges them. This file constructs their identity section and inversion isomorphism,
and proves that both projections are smooth of relative dimension four and surjective.
These are properties of the affine groupoid; identifying its quotient with a moduli stack
requires the separate moduli and descent comparisons.

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

end TauCeti.WeierstrassChange.ChangeRing

namespace TauCeti.WeierstrassHopfAlgebroid

open WeierstrassCurve TauCeti.WeierstrassChange

/-- The source projection of the affine Weierstrass groupoid. -/
def source : Spec (.of ArrowRing) ⟶ Spec (.of (MvPolynomial Coeff ℤ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial Coeff ℤ) ArrowRing))

/-- The target projection of the affine Weierstrass groupoid. -/
def target : Spec (.of ArrowRing) ⟶ Spec (.of (MvPolynomial Coeff ℤ)) :=
  Spec.map (CommRingCat.ofHom rightUnit)

/-- The identity section of the affine Weierstrass groupoid. -/
def identity : Spec (.of (MvPolynomial Coeff ℤ)) ⟶ Spec (.of ArrowRing) :=
  Spec.map (CommRingCat.ofHom counit)

/-- Inversion of arrows in the affine Weierstrass groupoid, as an isomorphism of schemes. -/
def inversion : Spec (.of ArrowRing) ≅ Spec (.of ArrowRing) :=
  Scheme.Spec.mapIso (RingEquiv.ofBijective conjugation
    (Function.Involutive.bijective conjugation_conjugation)).toCommRingCatIso.op

/-- The source projection is induced by the left unit of the Hopf algebroid. -/
theorem source_def : source =
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)) := (rfl)

/-- The target projection is induced by the right unit of the Hopf algebroid. -/
theorem target_def : target = Spec.map (CommRingCat.ofHom rightUnit) := (rfl)

/-- The identity section is induced by the counit of the Hopf algebroid. -/
theorem identity_def : identity = Spec.map (CommRingCat.ofHom counit) := (rfl)

/-- Inversion is induced by conjugation in the Hopf algebroid. -/
theorem inversion_hom : inversion.hom = Spec.map (CommRingCat.ofHom conjugation) := (rfl)

/-- The inverse of inversion is also induced by conjugation in the Hopf algebroid. -/
theorem inversion_inv : inversion.inv = Spec.map (CommRingCat.ofHom conjugation) := by
  apply (cancel_mono inversion.hom).1
  rw [inversion.inv_hom_id, inversion_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    conjugation_comp_conjugation]
  simp

/-- The source of an identity arrow is the original curve. -/
@[simp]
theorem identity_source : identity ≫ source = 𝟙 _ := by
  simp [identity_def, source_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The target of an identity arrow is the original curve. -/
@[simp]
theorem identity_target : identity ≫ target = 𝟙 _ := by
  simp [identity_def, target_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Inversion exchanges the source and target projections. -/
@[simp]
theorem inversion_hom_source : inversion.hom ≫ source = target := by
  rw [inversion_hom, source_def, target_def, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) conjugation_comp_algebraMap

/-- Inversion exchanges the target and source projections. -/
@[simp]
theorem inversion_hom_target : inversion.hom ≫ target = source := by
  rw [inversion_hom, source_def, target_def, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) conjugation_comp_rightUnit

/-- Inversion fixes identity arrows. -/
@[simp]
theorem identity_inversion_hom : identity ≫ inversion.hom = identity := by
  simp [identity_def, inversion_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The source projection is smooth of relative dimension four. -/
instance smoothOfRelativeDimension_source : SmoothOfRelativeDimension 4 source := by
  rw [source_def]
  infer_instance

/-- The target projection is smooth of relative dimension four. -/
instance smoothOfRelativeDimension_target : SmoothOfRelativeDimension 4 target := by
  rw [← inversion_hom_source]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 4) (inversion.hom ≫ source))

/-- The source projection is smooth. -/
instance smooth_source : Smooth source := SmoothOfRelativeDimension.smooth 4 _

/-- The target projection is smooth. -/
instance smooth_target : Smooth target := SmoothOfRelativeDimension.smooth 4 _

/-- Every curve is the source of an arrow, namely its identity. -/
instance surjective_source : Surjective source := by
  have : Surjective (identity ≫ source) := identity_source ▸ inferInstance
  exact Surjective.of_comp identity source

/-- Every curve is the target of an arrow, namely its identity. -/
instance surjective_target : Surjective target := by
  have : Surjective (identity ≫ target) := identity_target ▸ inferInstance
  exact Surjective.of_comp identity target

end TauCeti.WeierstrassHopfAlgebroid
