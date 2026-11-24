/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.ProjectiveClosure
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion

/-!
# Projective models of affine schemes of finite type

An affine scheme of finite type over an affine base admits an open immersion into a scheme
that embeds as a closed subscheme of a finite polynomial projective spectrum. The model is the
projective closure of a polynomial quotient presentation of its coordinate ring.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace TauCeti

private theorem exists_projectiveClosureEmbedding {R : Type u} [CommRing R] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) R)) :
    ∃ e : Over.mk (DenseCompactification.projectiveClosure J).obj.p ⟶
      Over.mk (Proj.toSpecCoeff (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R)),
      IsClosedImmersion e.left := by
  let I := J.homogenization 0
  let ρ := (rename (ULift.down : ULift.{u} (Fin (n + 1)) → Fin (n + 1)) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) R →ₐ[R] MvPolynomial (Fin (n + 1)) R)
  let ψ : homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R →+*ᵍ I.quotientGrading :=
    { __ := (Ideal.Quotient.mk I.toIdeal).comp ρ.toRingHom
      map_mem hx := GradedAlgebra.mk_mem_quotientPiece _ _
        ((mem_homogeneousSubmodule _ _).mpr
          (((mem_homogeneousSubmodule _ _).mp hx).rename_isHomogeneous)) }
  have hψ : Function.Surjective ψ :=
    Ideal.Quotient.mk_surjective.comp (rename_surjective _ ULift.down_surjective)
  let hI := HomogeneousIdeal.irrelevant_le_map_of_surjective ψ hψ
  let E := Proj.map ψ hI
  have hER : E ≫ Proj.toSpecCoeff (homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R) =
      (DenseCompactification.projectiveClosure J).obj.p := by
    exact Proj.map_toSpecCoeff _ ψ hI fun r ↦ Subtype.ext (by
      -- After forgetting the degree-zero subtype, coefficient compatibility is a ring equation.
      change ψ (algebraMap R _ r) = algebraMap R _ r
      -- The local presentation is quotient after renaming, so their scalar laws apply here.
      change (Ideal.Quotient.mk I.toIdeal) (ρ (algebraMap R _ r)) = _
      rw [ρ.commutes]
      exact (Ideal.Quotient.mkₐ R I.toIdeal).commutes r)
  exact ⟨Over.homMk E hER, Proj.isClosedImmersion_map ψ hI hψ⟩

/-- An affine scheme of finite type over `Spec R` is open in a closed subscheme of a finite
polynomial projective spectrum over `Spec R`. -/
theorem exists_projectiveClosedModel {R : Type u} [CommRing R] {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    ∃ (σ : Type u) (_ : Finite σ) (P : Over (Spec (.of R)))
      (j : Over.mk f ⟶ P)
      (e : P ⟶ Over.mk (Proj.toSpecCoeff (homogeneousSubmodule σ R))),
      IsOpenImmersion j.left ∧ IsClosedImmersion e.left := by
  let α : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom
  have hα : α.FiniteType :=
    ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
      inferInstance).comp (.of_surjective _
        (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective)
  let := α.toAlgebra
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hα
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let C := DenseCompactification.projectiveClosure (RingHom.ker π)
  obtain ⟨E, hE⟩ := exists_projectiveClosureEmbedding (RingHom.ker π)
  let j := X.isoSpec.hom ≫ Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ C.obj.j
  have hj : j ≫ C.obj.p = f := by
    have hC := C.obj.obj.ι_π
    have he : CommRingCat.ofHom (algebraMap R _) ≫ e.toRingEquiv.toCommRingCatIso.hom =
        CommRingCat.ofHom α := by
      ext1
      exact e.toAlgHom.comp_algebraMap
    dsimp only [j]
    rw [Category.assoc, Category.assoc, hC, ← Spec.map_comp, he]
    -- The affine identification has underlying map `toSpecΓ`, the form used by naturality.
    change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine ⟨ULift.{u} (Fin (n + 1)), inferInstance, Over.mk C.obj.p, Over.homMk j hj, E, ?_, hE⟩
  -- Forget the `Over` wrapper: openness is a property of its underlying scheme morphism `j`.
  change IsOpenImmersion j
  dsimp only [j]
  infer_instance

end TauCeti
