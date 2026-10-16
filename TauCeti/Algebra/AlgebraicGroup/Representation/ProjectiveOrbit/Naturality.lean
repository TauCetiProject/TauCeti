/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Corestrict
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality

/-!
# Projective orbit morphisms under restriction of representations

Restricting a representation along a morphism of affine group schemes pulls back
its projective orbit morphism along that morphism. The result is an equality of
scheme morphisms over arbitrary commutative rings, rather than only an equality
on rational points. It applies in particular to the restriction to a closed subgroup.

The coordinate formula is `CoalgHom.matrixCoefficient_corestrict`. The scheme
comparison combines `Comodule.projectiveOrbitMap` with
`AlgebraicGeometry.Proj.fromOfGlobalSections_naturality`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry

open TauCeti TauCeti.Comodule

namespace BialgHom

universe u v w x

section Coordinates

variable {R : Type u} {H : Type v} {K : Type w} {M : Type x}
  [CommSemiring R] [CommSemiring H] [CommSemiring K]
  [Bialgebra R H] [Bialgebra R K]
  [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Restricting the representation pulls its homogeneous orbit coordinates back along
the coordinate bialgebra morphism. -/
@[simp]
theorem orbitCoordinates_corestrict (f : H →ₐc[R] K) (m : M) :
    (letI : Comodule R K M := Corestrict f.toCoalgHom
     orbitCoordinates (H := K) m) = f.toAlgHom.comp (orbitCoordinates (H := H) m) := by
  let : Comodule R K M := Corestrict f.toCoalgHom
  ext φ
  -- The symmetric-algebra extensionality lemma presents algebra maps as linear maps.
  change orbitCoordinates (H := K) m (SymmetricAlgebra.ι R (Module.Dual R M) φ) =
    f (orbitCoordinates (H := H) m (SymmetricAlgebra.ι R (Module.Dual R M) φ))
  rw [orbitCoordinates_ι, orbitCoordinates_ι, CoalgHom.matrixCoefficient_corestrict]
  rfl

end Coordinates

variable {R H K M : Type u} [CommRing R] [CommRing H] [CommRing K]
  [HopfAlgebra R H] [HopfAlgebra R K]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M]

/-- Restriction along a morphism of affine group schemes pulls back the projective orbit
morphism. This includes restriction to nonreduced closed subgroup schemes. -/
@[reassoc]
theorem projectiveOrbitMap_corestrict (f : H →ₐc[R] K) (m : M)
    (hm : Module.IsUnimodular R m) :
    (letI : Comodule R K M := Corestrict f.toCoalgHom
     projectiveOrbitMap (H := K) m hm) =
      Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
        projectiveOrbitMap (H := H) m hm := by
  let : Comodule R K M := Corestrict f.toCoalgHom
  rw [projectiveOrbitMap_def, projectiveOrbitMap_def,
    Proj.fromOfGlobalSections_naturality]
  congr 1
  rw [orbitCoordinates_corestrict f m]
  apply RingHom.ext
  intro s
  have h := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.toAlgHom.toRingHom))
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]
    using DFunLike.congr_fun h (orbitCoordinates (R := R) (H := H) m s)

end BialgHom
