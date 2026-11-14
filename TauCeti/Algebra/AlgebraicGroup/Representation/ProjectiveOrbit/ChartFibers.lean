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
coefficient is a unit at one of the two points (equality of the morphisms then forces it at
the other).

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

/-- The standard chart of a linear coordinate pulls back along an algebra-valued orbit map
to the principal open of the evaluated matrix coefficient. -/
theorem SpecMap_projectiveOrbitMap_preimage_basicOpen_ι (m : M)
    (hm : Module.IsUnimodular R m) (g : H →ₐ[R] A) (φ : Module.Dual R M) :
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm) ⁻¹ᵁ
        Proj.basicOpen _ (SymmetricAlgebra.ι R (Module.Dual R M) φ) =
      (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv
        (g (matrixCoefficient (C := H) φ m))) := by
  rw [Scheme.Hom.comp_preimage, projectiveOrbitMap_preimage_basicOpen_ι,
    Scheme.preimage_basicOpen]
  congr 1
  exact congrArg (fun e : CommRingCat.of H ⟶ Γ(Spec (.of A), ⊤) ↦
    e.hom (matrixCoefficient (C := H) φ m))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g.toRingHom)).symm

/-- Two algebra-valued orbit maps on the same linear chart agree exactly when their
matrix coefficients at the chosen vector differ by a common unit. The chart functional
need only be a unit at the second point. This compares full
scheme morphisms, including their structure-sheaf maps. -/
theorem projectiveOrbitMap_SpecMap_eq_iff_exists_unit (m : M)
    (hm : Module.IsUnimodular R m) (g h : H →ₐ[R] A) (φ : Module.Dual R M)
    (hh : IsUnit (h (matrixCoefficient (C := H) φ m))) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫ projectiveOrbitMap (H := H) m hm ↔
      ∃ c : Aˣ, ∀ ψ : Module.Dual R M,
        h (matrixCoefficient (C := H) ψ m) = c * g (matrixCoefficient (C := H) ψ m) := by
  have hmain (hg : IsUnit (g (matrixCoefficient (C := H) φ m))) :
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
  constructor
  · intro heq
    refine (hmain ?_).mp heq
    have hopen := SpecMap_projectiveOrbitMap_preimage_basicOpen_ι m hm g φ
    rw [heq, SpecMap_projectiveOrbitMap_preimage_basicOpen_ι, basicOpen_eq_of_affine,
      basicOpen_eq_of_affine] at hopen
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).mp hopen.le
    exact isUnit_of_dvd_unit (Ideal.mem_span_singleton.mp hn) (hh.pow n)
  · rintro ⟨c, hc⟩
    refine (hmain ?_).mpr ⟨c, hc⟩
    have := hc φ
    have hu : IsUnit ((c : A) * g (matrixCoefficient (C := H) φ m)) := this ▸ hh
    exact (IsUnit.mul_iff.mp hu).2

end TauCeti.Comodule
