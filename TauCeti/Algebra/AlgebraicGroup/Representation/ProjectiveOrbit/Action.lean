/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme
public import TauCeti.AlgebraicGeometry.Morphisms.Immersion

/-!
# Translations of projective orbit schemes

Every rational group point induces an automorphism of the projective orbit scheme of
a line. The orbit inclusion intertwines this automorphism with ambient projective
translation, and the map from the group to the orbit intertwines it with left translation.
These are equalities of scheme morphisms, retaining the possibly nonreduced structure
of the orbit. The automorphisms preserve the structural morphism to the base field.

This provides the translations needed to transport local properties of the orbit map
between rational translates. It does not assert flatness or identify the orbit scheme
with the fppf homogeneous quotient.

The construction combines `Comodule.projectiveOrbitMap_leftTranslation`,
`Comodule.toProjectiveOrbit`, and the lifting property of an immersion after a
surjective, scheme-theoretically dominant morphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

private theorem exists_orbitTranslationHom (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    ∃! l : projectiveOrbitScheme (H := H) m hm ⟶ projectiveOrbitScheme (H := H) m hm,
      l ≫ projectiveOrbitι (H := H) m hm =
        projectiveOrbitι (H := H) m hm ≫ (projectivePointTranslation (M := M) g).hom :=
  (projectiveOrbitι (H := H) m hm).existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (projectiveOrbitι (H := H) m hm ≫ (projectivePointTranslation (M := M) g).hom)
    (toProjectiveOrbit (H := H) m hm)
    (Spec.map (CommRingCat.ofHom
      (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) ≫
        toProjectiveOrbit (H := H) m hm)
    (by simpa only [Category.assoc, toProjectiveOrbit_projectiveOrbitι,
      toProjectiveOrbit_projectiveOrbitι_assoc] using
        projectiveOrbitMap_leftTranslation g m hm)

/-- The unique endomorphism of the orbit restricting ambient projective translation. -/
private noncomputable def orbitTranslationHom (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    projectiveOrbitScheme (H := H) m hm ⟶ projectiveOrbitScheme (H := H) m hm :=
  (exists_orbitTranslationHom m hm g).exists.choose

@[reassoc]
private theorem orbitTranslationHom_ι (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    orbitTranslationHom m hm g ≫ projectiveOrbitι (H := H) m hm =
      projectiveOrbitι (H := H) m hm ≫ (projectivePointTranslation (M := M) g).hom :=
  (exists_orbitTranslationHom m hm g).exists.choose_spec

/-- Rational translation on the locally closed projective orbit, with its full
scheme-theoretic image structure. -/
noncomputable def projectiveOrbitTranslation (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    projectiveOrbitScheme (H := H) m hm ≅ projectiveOrbitScheme (H := H) m hm where
  hom := orbitTranslationHom m hm g
  inv := orbitTranslationHom m hm g⁻¹
  hom_inv_id := by
    rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
    simp only [Category.assoc, orbitTranslationHom_ι, orbitTranslationHom_ι_assoc,
      projectivePointTranslation_inv_eq_symm, Iso.symm_hom, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
    simp only [Category.assoc, orbitTranslationHom_ι, orbitTranslationHom_ι_assoc,
      projectivePointTranslation_inv_eq_symm, Iso.symm_hom, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- The orbit inclusion intertwines orbit translation with ambient projective translation. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitTranslation_hom_ι (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    (projectiveOrbitTranslation m hm g).hom ≫ projectiveOrbitι (H := H) m hm =
      projectiveOrbitι (H := H) m hm ≫ (projectivePointTranslation (M := M) g).hom :=
  orbitTranslationHom_ι m hm g

/-- Inverse orbit translation restricts the inverse ambient projective translation. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitTranslation_inv_ι (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    (projectiveOrbitTranslation m hm g).inv ≫ projectiveOrbitι (H := H) m hm =
      projectiveOrbitι (H := H) m hm ≫ (projectivePointTranslation (M := M) g).inv := by
  simpa only [projectiveOrbitTranslation, projectivePointTranslation_inv_eq_symm,
    Iso.symm_hom] using orbitTranslationHom_ι m hm g⁻¹

/-- The orbit factorization intertwines group translation with orbit translation. -/
@[reassoc]
theorem toProjectiveOrbit_projectiveOrbitTranslation_hom
    (m : M) (hm : Module.IsUnimodular k m) (g : WithConv (H →ₐ[k] k)) :
    toProjectiveOrbit (H := H) m hm ≫ (projectiveOrbitTranslation m hm g).hom =
      Spec.map (CommRingCat.ofHom
        (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) ≫
          toProjectiveOrbit (H := H) m hm := by
  rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
  simpa only [Category.assoc, projectiveOrbitTranslation_hom_ι,
    toProjectiveOrbit_projectiveOrbitι_assoc, toProjectiveOrbit_projectiveOrbitι] using
    (projectiveOrbitMap_leftTranslation g m hm).symm

/-- Translation by the identity is the identity orbit isomorphism. -/
@[simp]
theorem projectiveOrbitTranslation_one (m : M) (hm : Module.IsUnimodular k m) :
    projectiveOrbitTranslation (H := H) m hm 1 = Iso.refl _ := by
  apply Iso.ext
  rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
  simp

/-- Translation by a convolution product composes orbit translations in action order. -/
@[simp]
theorem projectiveOrbitTranslation_mul (m : M) (hm : Module.IsUnimodular k m)
    (g h : WithConv (H →ₐ[k] k)) :
    projectiveOrbitTranslation m hm (g * h) =
      (projectiveOrbitTranslation m hm h).trans (projectiveOrbitTranslation m hm g) := by
  apply Iso.ext
  rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
  simp [Category.assoc]

/-- Translation by the inverse point is the inverse orbit isomorphism. -/
@[simp]
theorem projectiveOrbitTranslation_inv_eq_symm (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    projectiveOrbitTranslation m hm g⁻¹ = (projectiveOrbitTranslation m hm g).symm := by
  apply Iso.ext
  rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
  simp

/-- Orbit translations are automorphisms over the base field. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitTranslation_hom_toSpec (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    (projectiveOrbitTranslation m hm g).hom ≫ projectiveOrbitToSpec (H := H) m hm =
      projectiveOrbitToSpec (H := H) m hm := by
  rw [projectiveOrbitToSpec_def, projectiveOrbitTranslation_hom_ι_assoc]
  rw [projectivePointTranslation_hom, SymmetricAlgebra.projToSpec_def,
    Proj.map_toSpecZero_assoc]
  -- The degree-zero coordinate map fixes the scalars defining the base morphism.
  congr 1
  rw [← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  ext r
  simp

/-- Inverse orbit translations also preserve the structural morphism to the base field. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitTranslation_inv_toSpec (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    (projectiveOrbitTranslation m hm g).inv ≫ projectiveOrbitToSpec (H := H) m hm =
      projectiveOrbitToSpec (H := H) m hm :=
  (Iso.inv_comp_eq _).mpr (projectiveOrbitTranslation_hom_toSpec m hm g).symm

end TauCeti.Comodule
