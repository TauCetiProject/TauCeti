/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.GlobalCoordinates
public import TauCeti.LinearAlgebra.Unimodular

/-!
# Projective orbit morphisms depend only on the chosen generator up to a unit

Rescaling a unimodular vector by a unit preserves its projective orbit morphism. This
identifies the morphisms constructed from different generators of a trivialized line,
as scheme morphisms over arbitrary commutative rings, including nonreduced rings.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {R H M : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

/-- Unit rescaling of a unimodular vector does not change its projective orbit morphism. -/
@[simp]
theorem projectiveOrbitMap_units_smul (m : M) (c : Rˣ)
    (hm : Module.IsUnimodular R m) :
    projectiveOrbitMap (H := H) (c • m) (Module.isUnimodular_units_smul c hm) =
      projectiveOrbitMap (H := H) m hm := by
  rw [projectiveOrbitMap_def, projectiveOrbitMap_def]
  apply TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling
    _ _ _ (c.map ((Scheme.ΓSpecIso (.of H)).inv.hom.comp (algebraMap R H)))
  intro n s hs
  simp only [Units.coe_map, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Units.smul_def,
    orbitCoordinates_smul_of_mem_homogeneousSubmodule m (c : R) hs,
    Algebra.smul_def, map_mul, map_pow]
  rfl

end TauCeti.Comodule
