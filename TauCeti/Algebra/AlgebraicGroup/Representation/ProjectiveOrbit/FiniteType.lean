/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

/-!
# Constructibility of projective orbit images

The projective orbit morphism of a unimodular vector in a finite projective Hopf comodule
is quasi-compact over any commutative base ring. It is locally of finite type when the
coordinate Hopf algebra is finitely generated over the base. Over a Noetherian base it is
also locally of finite presentation, so its image in projective space is constructible.

This supplies the constructibility input for realizing homogeneous spaces as locally
closed projective orbits. The image here is the image of the underlying scheme map,
including nonclosed points; it is not merely the orbit of the base-field-valued points.
No smoothness, reducedness, or characteristic assumption is made. Local closedness and
identification with a homogeneous quotient are separate assertions.

The construction combines `Comodule.projectiveOrbitMap`, the structural morphism
`SymmetricAlgebra.projToSpec`, and Mathlib's scheme-theoretic Chevalley theorem
`Scheme.Hom.isConstructible_image`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry Topology

namespace TauCeti.Comodule

universe u

variable {R H M : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M]

/-- The projective orbit morphism commutes with the structural morphisms over the base ring. -/
@[reassoc (attr := simp)]
theorem projectiveOrbitMap_projToSpec (m : M) (hm : Module.IsUnimodular R m) :
    projectiveOrbitMap (H := H) m hm ≫
        TauCeti.SymmetricAlgebra.projToSpec R (Module.Dual R M) =
      Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
  rw [TauCeti.SymmetricAlgebra.projToSpec_def, ← Category.assoc,
    projectiveOrbitMap_toSpecZero, ← Spec.map_comp]
  congr 1
  ext r
  simp

/-- A projective orbit morphism is quasi-compact over any commutative base ring. -/
instance instQuasiCompactProjectiveOrbitMap (m : M) (hm : Module.IsUnimodular R m) :
    QuasiCompact (projectiveOrbitMap (H := H) m hm) := by
  have : QuasiCompact (projectiveOrbitMap (H := H) m hm ≫
      TauCeti.SymmetricAlgebra.projToSpec R (Module.Dual R M)) := by
    rw [projectiveOrbitMap_projToSpec]
    infer_instance
  exact QuasiCompact.of_comp _ (TauCeti.SymmetricAlgebra.projToSpec R (Module.Dual R M))

variable [Algebra.FiniteType R H]

/-- A projective orbit morphism of a finite-type affine group scheme is locally of finite
type over any commutative base ring. -/
instance instLocallyOfFiniteTypeProjectiveOrbitMap (m : M) (hm : Module.IsUnimodular R m) :
    LocallyOfFiniteType (projectiveOrbitMap (H := H) m hm) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R H))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType (projectiveOrbitMap (H := H) m hm ≫
      TauCeti.SymmetricAlgebra.projToSpec R (Module.Dual R M)) := by
    rw [projectiveOrbitMap_projToSpec]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (TauCeti.SymmetricAlgebra.projToSpec R (Module.Dual R M))

variable [IsNoetherianRing R]

/-- Over a Noetherian base, the scheme-theoretic topological image of a finite-type affine
group's projective orbit morphism is constructible, even for nonreduced groups. -/
theorem isConstructible_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular R m) :
    IsConstructible (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  simpa only [Set.image_univ] using
    (projectiveOrbitMap (H := H) m hm).isConstructible_image IsConstructible.univ

end TauCeti.Comodule
