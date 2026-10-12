/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LocalEquality

/-!
# Zariski-local fibers of projective orbit morphisms

Two algebra-valued group points have the same image under a projective orbit morphism
if and only if their matrix coefficients at the chosen vector differ by one unit
locally on an affine open cover of the value scheme. This removes the requirement
that both points lie in one global standard chart. It compares full scheme morphisms
and applies to nonreduced value rings.

The chosen vector is unimodular in a finite projective comodule. Its matrix
coefficients generate the unit ideal, so the linear chart opens cover the value
scheme. The criterion is the projective part of the comparison between orbit fibers
and locally equal cosets of a line stabilizer.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {R H M A : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M] [CommRing A] [Algebra R A]

/-- Equality of projective orbit images is equivalent to Zariski-local unit
proportionality of matrix coefficients. The affine open cover and the unit on each
member are existential; no global chart or reducedness hypothesis is required. -/
theorem projectiveOrbitMap_SpecMap_eq_iff_exists_affineOpenCover_unit
    (m : M) (hm : Module.IsUnimodular R m) (g h : H →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫ projectiveOrbitMap (H := H) m hm ↔
      ∃ 𝒰 : (Spec (.of A)).OpenCover.{u}, (∀ i, IsAffine (𝒰.X i)) ∧
        ∀ i, ∃ c : Γ(𝒰.X i, ⊤)ˣ, ∀ φ : Module.Dual R M,
          (𝒰.f i).appTop ((Scheme.ΓSpecIso (.of A)).inv
              (h (matrixCoefficient (C := H) φ m))) =
            c * (𝒰.f i).appTop ((Scheme.ΓSpecIso (.of A)).inv
              (g (matrixCoefficient (C := H) φ m))) := by
  -- Express both orbit images by pulled-back homogeneous coordinates.
  let 𝒜 := SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)
  let coords (q : H →ₐ[R] A) :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.comp
      (q.comp (orbitCoordinates (H := H) m)).toRingHom
  have hirr (q : H →ₐ[R] A) :
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (coords q) = ⊤ := by
    simpa only [coords, 𝒜, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      ← Ideal.map_map, Ideal.map_top] using
      congrArg (fun I : Ideal H ↦ I.map
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp q.toRingHom))
        (map_irrelevant_orbitCoordinates hm)
  have hcoord (q : H →ₐ[R] A) :
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
        Proj.fromOfGlobalSections 𝒜 (coords q) (hirr q) := by
    rw [projectiveOrbitMap_def, Proj.fromOfGlobalSections_naturality]
    congr 1
    have hn := congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q.toRingHom))
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc,
      coords, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom] using
        congrArg (fun e : H →+* Γ(Spec (.of A), ⊤) ↦
          e.comp (orbitCoordinates (H := H) m).toRingHom) hn.symm
  -- Unimodularity supplies the degree-one cover required by the projective criterion.
  have hspan : Ideal.span (coords g '' (𝒜 1 : Set _)) = ⊤ := by
    have hc : Ideal.span (Set.range fun φ : Module.Dual R M ↦
        coords g (SymmetricAlgebra.ι R (Module.Dual R M) φ)) = ⊤ := by
      have he : (Set.range fun φ : Module.Dual R M ↦
          coords g (SymmetricAlgebra.ι R (Module.Dual R M) φ)) =
          ((Scheme.ΓSpecIso (.of A)).inv.hom.comp g.toRingHom) ''
            (Set.range fun φ : Module.Dual R M ↦ matrixCoefficient (C := H) φ m) := by
        ext z
        simp [coords, Set.mem_image]
      rw [he, ← Ideal.map_span,
        (span_matrixCoefficient_eq_top_iff_isUnimodular m).mpr hm, Ideal.map_top]
    apply top_unique
    rw [← hc]
    apply Ideal.span_mono
    rintro _ ⟨φ, rfl⟩
    exact ⟨_, SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) φ, rfl⟩
  rw [hcoord g, hcoord h,
    Proj.fromOfGlobalSections_eq_iff_exists_affineOpenCover_unit_rescaling
      𝒜 (coords g) (coords h) (hirr g) (hirr h) hspan]
  -- Degree-one proportionality extends to degree n by the symmetric-algebra API.
  constructor
  · rintro ⟨𝒰, haff, hc⟩
    refine ⟨𝒰, haff, fun i ↦ ?_⟩
    obtain ⟨c, hc⟩ := hc i
    refine ⟨c, fun φ ↦ ?_⟩
    simpa [coords] using hc 1 (SymmetricAlgebra.ι R (Module.Dual R M) φ)
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule R (Module.Dual R M) φ)
  · rintro ⟨𝒰, haff, hc⟩
    refine ⟨𝒰, haff, fun i ↦ ?_⟩
    obtain ⟨c, hc⟩ := hc i
    let r : A →+* Γ(𝒰.X i, ⊤) :=
      (𝒰.f i).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
    let : Algebra R Γ(𝒰.X i, ⊤) := (r.comp (algebraMap R A)).toAlgebra
    let rAlg : A →ₐ[R] Γ(𝒰.X i, ⊤) := { r with commutes' := fun _ ↦ rfl }
    refine ⟨c, fun n s hs ↦ ?_⟩
    exact AlgHom.apply_eq_pow_mul_of_forall_ι_eq
      (rAlg.comp (g.comp (orbitCoordinates (H := H) m)))
      (rAlg.comp (h.comp (orbitCoordinates (H := H) m))) (c : Γ(𝒰.X i, ⊤))
      (fun φ ↦ by simpa [rAlg, r] using hc φ) hs

end TauCeti.Comodule
