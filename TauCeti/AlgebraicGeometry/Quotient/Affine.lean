/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Affine invariant quotients

For a monoid acting on a commutative ring `A`, the affine invariant quotient is `Spec (Aᴳ)`,
with projection induced by the inclusion of the fixed subring.
This file proves its universal property for affine target schemes. For group actions,
the contravariant spectrum maps are isomorphisms and act on prime ideals by the inverse element.

The universal property for affine targets requires only a monoid action. This file does not
construct the fppf sheaf quotient or prove the universal property for non-affine targets.
The finite-group properties of the projection are developed in
`TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Affine`.

## Main definitions

* `quotient`: the spectrum of the fixed subring.
* `projection`: the invariant-spectrum projection.
* `specComap`: the contravariant spectrum map of an action element.
* `desc`: descent of an invariant morphism to an affine target.

## Main results

* `existsUnique_desc` and `hom_ext`: the affine-target universal property.
* `projection_specAlgebraMap`: the projection lies over every invariant base ring.
* `specComap_base_apply`: the point map of a group element is the inverse spectrum action.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace TauCeti.AffineInvariantQuotient

universe u v

section Monoid

variable (A : Type u) (G : Type v) [CommRing A] [Monoid G] [MulSemiringAction G A]

/-- The spectrum of the fixed subring, the affine invariant quotient of `Spec A`. -/
noncomputable abbrev quotient : Scheme.{u} :=
  Spec (CommRingCat.of (FixedPoints.subring A G))

/-- The quotient projection, induced by the inclusion of invariant functions. -/
noncomputable def projection : Spec (CommRingCat.of A) ⟶ quotient A G :=
  Spec.algebraMap (FixedPoints.subring A G) A

/-- The defining equation for the quotient projection. -/
theorem projection_def : projection A G = Spec.algebraMap (FixedPoints.subring A G) A := (rfl)

/-- The projection contracts prime ideals to the fixed subring. -/
@[simp]
theorem projection_base_apply (x : PrimeSpectrum A) :
    (projection A G).base x = PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) x := by
  rw [projection_def]
  exact Spec.map_apply (CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A)) x

/-- The quotient projection lies over every invariant base ring. -/
@[simp, reassoc]
theorem projection_specAlgebraMap (R : Type u) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] :
    projection A G ≫ Spec.algebraMap R (FixedPoints.subalgebra R A G) =
      Spec.algebraMap R A := by
  rw [projection_def]
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))
    (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A))).symm.trans (by
      rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

/-- The contravariant spectrum map induced by an element of the acting monoid. -/
noncomputable def specComap (g : G) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g))

/-- The defining equation for the contravariant spectrum map. -/
theorem specComap_def (g : G) :
    specComap A G g = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) := (rfl)

/-- Pullback on global sections recovers the ring homomorphism of the action element. -/
@[simp]
theorem preimage_specComap (g : G) :
    Spec.preimage (specComap A G g) =
      CommRingCat.ofHom (MulSemiringAction.toRingHom G A g) := by
  rw [specComap_def, Spec.preimage_map]

@[simp]
theorem specComap_one : specComap A G 1 = 𝟙 _ := by
  rw [specComap_def]
  convert Spec.map_id (CommRingCat.of A) using 1
  congr 1
  ext a
  exact one_smul G a

/-- Pullback reverses composition: these morphisms form a right action on the spectrum. -/
@[simp]
theorem specComap_mul (g h : G) :
    specComap A G (g * h) = specComap A G g ≫ specComap A G h := by
  rw [specComap_def, specComap_def, specComap_def, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact mul_smul g h a

/-- The quotient projection is invariant under every element of the acting monoid. -/
@[reassoc (attr := simp)]
theorem specComap_projection (g : G) :
    specComap A G g ≫ projection A G = projection A G := by
  rw [specComap_def, projection_def, ← Spec.map_comp]
  congr 1
  ext a
  exact a.property g

variable {A G}

/-- An invariant morphism to an affine scheme pulls back functions to invariant functions. -/
private theorem preimage_mem_fixed {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) (a : Γ(Y, ⊤)) :
    (Spec.preimage (f ≫ Y.isoSpec.hom)).hom a ∈ FixedPoints.subring A G := by
  intro g
  have h := congrArg Spec.preimage (congrArg (fun k => k ≫ Y.isoSpec.hom) (hf g))
  simpa only [Category.assoc, Spec.preimage_comp, preimage_specComap, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom, RingHom.comp_apply, MulSemiringAction.toRingHom_apply] using
    congrArg (fun k => k.hom a) h

/-- Descend an invariant morphism to an affine target through the fixed-subring spectrum. -/
noncomputable def desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) : quotient A G ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
      (FixedPoints.subring A G) (preimage_mem_fixed f hf))) ≫ Y.isoSpec.inv

/-- The descended morphism factors the given invariant morphism. -/
@[reassoc (attr := simp)]
theorem projection_desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    projection A G ≫ desc f hf = f := by
  rw [desc, projection_def, ← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom
      ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
        (FixedPoints.subring A G) (preimage_mem_fixed f hf)) ≫
      CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A) =
      Spec.preimage (f ≫ Y.isoSpec.hom) := by
    ext a
    rfl
  rw [h, Spec.map_preimage]
  simp

/-- Morphisms from the invariant quotient to an affine target are determined by their
composition with the projection. -/
@[ext]
theorem hom_ext {Y : Scheme.{u}} [IsAffine Y] {f h : quotient A G ⟶ Y}
    (hfh : projection A G ≫ f = projection A G ≫ h) : f = h := by
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (FixedPoints.subring A G).subtype)
    (Subtype.val_injective) ⊤ (isAffineOpen_top Y) (by simp) (by simp)
  exact hfh

/-- The affine-target universal property: every invariant morphism factors uniquely through
the invariant quotient. -/
theorem existsUnique_desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃! h : quotient A G ⟶ Y, projection A G ≫ h = f := by
  exact ⟨desc f hf, projection_desc f hf, fun h hh =>
    hom_ext (hh.trans (projection_desc f hf).symm)⟩

/-- Descending the pullback of an affine-target morphism recovers that morphism. -/
@[simp]
theorem desc_projection {Y : Scheme.{u}} [IsAffine Y] (f : quotient A G ⟶ Y) :
    desc (projection A G ≫ f) (fun g => by simp) = f := by
  apply hom_ext
  exact projection_desc _ _

end Monoid

section Group

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A]

/-- Every contravariant spectrum map of a group element is an isomorphism. -/
instance (g : G) : IsIso (specComap A G g) := by
  rw [specComap_def]
  exact isIso_SpecMap_iff.mpr (MulSemiringAction.toRingEquiv G A g).bijective

/-- The contravariant spectrum map of `g` is the standard spectrum action by `g⁻¹`. -/
@[simp]
theorem specComap_base_apply (g : G) (x : PrimeSpectrum A) :
    (specComap A G g).base x = g⁻¹ • x := by
  rw [specComap_def]
  refine (Spec.map_apply (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) x).trans ?_
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_smul,
    Ideal.pointwise_smul_eq_comap]
  ext a
  simp only [Ideal.mem_comap, CommRingCat.hom_ofHom, MulSemiringAction.toRingHom_apply,
    MulSemiringAction.toRingAut, MonoidHom.coe_mk, OneHom.coe_mk,
    MulSemiringAction.toRingEquiv_apply_symm_apply, inv_inv]

end Group

end TauCeti.AffineInvariantQuotient
