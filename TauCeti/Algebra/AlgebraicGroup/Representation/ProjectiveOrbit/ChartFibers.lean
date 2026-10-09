/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality

/-!
# Algebra-valued fibers of projective orbit maps on standard charts

For two algebra-valued group points whose orbit images lie on the same standard chart,
the resulting morphisms to projective space agree exactly when their matrix coefficients
at the chosen vector differ by one unit. These are equalities of scheme morphisms, so the
criterion detects infinitesimal information over nonreduced value rings. It supplies the
local fiber comparison between a projective orbit and a quotient by a line stabilizer.

No smoothness, reducedness, field, or finite-type hypothesis is imposed on the group or
the value ring. The chosen vector belongs to a finite projective comodule and is
unimodular, and the chart is specified by a linear functional whose evaluated matrix
coefficient is a unit at both points.

The chart computation follows `Comodule.projectiveOrbitMap` and
`Proj.fromOfGlobalSections_naturality`. Unit rescaling is tested by the degree-zero
localization maps, rather than by the underlying homogeneous prime ideals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace TauCeti.Comodule

universe u

variable {R H M A : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M] [CommRing A] [Algebra R A]

/-- On a chart with a unit evaluated matrix coefficient, an algebra-valued orbit map
is `Spec` of the degree-zero homogeneous coordinate map followed by the chart inclusion. -/
theorem projectiveOrbitMap_SpecMap_eq_awayLift (m : M) (hm : Module.IsUnimodular R m)
    (g : H →ₐ[R] A) (φ : Module.Dual R M) (hg : IsUnit (g (matrixCoefficient (C := H) φ m))) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
      Spec.map (CommRingCat.ofHom (Away.lift
        (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))
        (g.comp (orbitCoordinates (H := H) m)).toRingHom
        (by simpa using hg))) ≫
      Proj.awayι (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))
        (SymmetricAlgebra.ι R (Module.Dual R M) φ)
        (SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) φ) one_pos := by
  rw [projectiveOrbitMap_def, Proj.fromOfGlobalSections_naturality]
  have hcoord :
      (Spec.map (CommRingCat.ofHom g.toRingHom)).appTop.hom.comp
          ((Scheme.ΓSpecIso (.of H)).inv.hom.comp (orbitCoordinates (H := H) m).toRingHom) =
        (Scheme.ΓSpecIso (.of A)).inv.hom.comp
          (g.comp (orbitCoordinates (H := H) m)).toRingHom := by
    apply RingHom.ext
    intro s
    have h := congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g.toRingHom))
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      using (DFunLike.congr_fun h (orbitCoordinates (H := H) m s)).symm
  simpa only [hcoord] using Proj.fromOfGlobalSections_Spec_eq_awayLift
    (g.comp (orbitCoordinates (H := H) m)).toRingHom
    (by rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← Ideal.map_map,
      ← AlgHom.toRingHom_eq_coe (orbitCoordinates (H := H) m),
      map_irrelevant_orbitCoordinates hm, Ideal.map_top])
    one_pos (SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) φ)
    (by simpa using hg)

/-- Two algebra-valued orbit maps on the same linear chart agree exactly when their
matrix coefficients at the chosen vector differ by a common unit. This compares full
scheme morphisms, including their structure-sheaf maps. -/
theorem projectiveOrbitMap_SpecMap_eq_iff_exists_unit (m : M)
    (hm : Module.IsUnimodular R m) (g h : H →ₐ[R] A) (φ : Module.Dual R M)
    (hg : IsUnit (g (matrixCoefficient (C := H) φ m)))
    (hh : IsUnit (h (matrixCoefficient (C := H) φ m))) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫ projectiveOrbitMap (H := H) m hm ↔
      ∃ c : Aˣ, ∀ ψ : Module.Dual R M,
        h (matrixCoefficient (C := H) ψ m) = c * g (matrixCoefficient (C := H) ψ m) := by
  rw [projectiveOrbitMap_SpecMap_eq_awayLift m hm g φ hg,
    projectiveOrbitMap_SpecMap_eq_awayLift m hm h φ hh,
    Proj.SpecMap_awayLift_awayι_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun ψ ↦ ?_⟩
    simpa using hc 1 (SymmetricAlgebra.ι R (Module.Dual R M) ψ)
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) ψ)
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n s hs ↦ ?_⟩
    exact AlgHom.apply_eq_pow_mul_of_forall_ι_eq
      (g.comp (orbitCoordinates (H := H) m)) (h.comp (orbitCoordinates (H := H) m))
      (c : A) (fun ψ ↦ by simpa using hc ψ) hs

end TauCeti.Comodule
