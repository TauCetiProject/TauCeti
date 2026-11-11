/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Smooth
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid

/-!
# Smooth projections of the affine Weierstrass groupoid

The source and target projections of the represented Weierstrass groupoid are the spectra
of the left and right units of its Hopf algebroid. Inversion exchanges them. This file
constructs their identity section and inversion isomorphism, and proves that both projections
are smooth of relative dimension four and surjective, using the arbitrary-coefficient-ring
results of `TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/Smooth.lean`.

These are properties of the affine groupoid; identifying its quotient with a moduli stack
requires the separate moduli and descent comparisons.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the Weierstrass
  groupoid and its coefficient and arrow rings.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.WeierstrassHopfAlgebroid

open _root_.WeierstrassCurve TauCeti.WeierstrassChange

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
def inversion : Spec (.of ArrowRing) ≅ Spec (.of ArrowRing) where
  hom := Spec.map (CommRingCat.ofHom conjugation)
  inv := Spec.map (CommRingCat.ofHom conjugation)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, conjugation_comp_conjugation]
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, conjugation_comp_conjugation]
    simp

/-- The source projection is induced by the left unit of the Hopf algebroid. -/
theorem source_def : source =
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)) := (rfl)

/-- The target projection is induced by the right unit of the Hopf algebroid. -/
theorem target_def : target = Spec.map (CommRingCat.ofHom rightUnit) := (rfl)

/-- The identity section is induced by the counit of the Hopf algebroid. -/
theorem identity_def : identity = Spec.map (CommRingCat.ofHom counit) := (rfl)

/-- Inversion is induced by conjugation in the Hopf algebroid. -/
theorem inversion_hom : inversion.hom = Spec.map (CommRingCat.ofHom conjugation) := (rfl)

/-- Inversion is its own inverse. -/
@[simp]
theorem inversion_inv : inversion.inv = inversion.hom := (rfl)

/-- Inverting an arrow twice returns the original arrow. -/
@[simp]
theorem inversion_hom_inversion_hom : inversion.hom ≫ inversion.hom = 𝟙 _ := by
  simpa only [inversion_inv] using inversion.inv_hom_id

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
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + 4) (inversion.hom ≫ source))

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
