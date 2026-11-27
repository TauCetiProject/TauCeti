/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveBundle.Basic
import TauCeti.AlgebraicGeometry.LineBundle.Epimorphism
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# The projective bundle of a line bundle

The projection from the projective bundle of an invertible sheaf to its base is an isomorphism.
Over a trivializing affine open the graded algebra of sections is a polynomial algebra with one
degree-one variable. The coefficient projection is an isomorphism by
`AlgebraicGeometry.Proj.isIso_toSpecCoeff_unique`, since the single standard affine chart covers
the projective spectrum.
The inverse of the projection gives a canonical section without choosing a trivialization.
The tautological quotient identifies the pullback of the original line bundle with the twist
`𝒪(1)` on its projective bundle.

## References

* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} {E : S.Modules}

/-- If the sections of a quasi-coherent module `E` on an affine open `U` are free of rank one,
the projection of its projective bundle restricted over `U` is an isomorphism. -/
theorem isIso_projection_morphismRestrict_of_linearEquiv [E.IsQuasicoherent] {U : S.Opens}
    (hU : IsAffineOpen U) (e : Γ(E, U) ≃ₗ[Γ(S, U)] Γ(S, U)) : IsIso (projection S E ∣_ U) := by
  let F : QuasicoherentSheaf S := ⟨E, inferInstance⟩
  let A := ((gradedSymmetricAlgebra S).obj F).obj
  let b : Module.Basis PUnit.{u + 1} Γ(S, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj) :=
    (Module.Basis.singleton PUnit.{u + 1} Γ(S, U)).map e.symm
  let p := _root_.SymmetricAlgebra.equivMvPolynomial b
  let a := gradedSymmetricAlgebraSectionsEquiv F hU
  have hgrade (n : ℕ) (x : MvPolynomial PUnit.{u + 1} Γ(S, U))
      (hx : x ∈ MvPolynomial.homogeneousSubmodule PUnit.{u + 1} Γ(S, U) n) :
      (p.symm.trans a) x ∈ A.gradedSectionsGrading U n := by
    rw [AlgEquiv.trans_apply]
    apply (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F hU n _).2
    apply (_root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff _ _ b n _).1
    simpa [p] using (MvPolynomial.mem_homogeneousSubmodule _ _).1 hx
  let c := p.symm.trans a
  let f : MvPolynomial.homogeneousSubmodule PUnit.{u + 1} Γ(S, U) →+*ᵍ A.gradedSectionsGrading U :=
    ⟨c.toRingHom, hgrade _ _⟩
  -- The coordinate isomorphism presents the affine chart as projective space over the same ring.
  have hf : f.toRingHom = c.toRingHom := rfl
  have hfR : ∀ r : Γ(S, U), f (algebraMap Γ(S, U) _ r) = algebraMap Γ(S, U) _ r := by
    rw [← GradedRingHom.coe_toRingHom, hf]
    exact c.commutes
  have hc : IsBaseChange Γ(S, U) (AlgHom.mk f.toRingHom hfR).toLinearMap := by
    apply IsBaseChange.of_surjective_algebraMap Function.surjective_id
    rw [AlgHom.coe_toLinearMap, AlgHom.coe_mk, hf]
    exact c.bijective
  have hchart := (Proj.isPullback_map_of_isBaseChange _ f hfR hc).isIso_snd_of_isIso
  rw [projection_def]
  exact (A.relativeProjToBase_morphismRestrict_iff (.isomorphisms _) hU).mpr hchart

/-- The projection `P(L) ⟶ S` of the projective bundle of an invertible module is an isomorphism. -/
instance isIso_projection_of_isInvertible [SheafOfModules.isInvertible S E] :
    IsIso (projection S E) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x ↦ ?_
  obtain ⟨V, t, hx⟩ := Scheme.Modules.exists_mem_trivialization E x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨U, hxU, isIso_projection_morphismRestrict_of_linearEquiv hU
    (Scheme.Modules.trivializationCoordinate E t (homOfLE hUV))⟩

/-- The canonical isomorphism from the projective bundle of an invertible sheaf to its base. -/
noncomputable def rankOne (L : InvertibleSheaf S) : projectiveBundle S L.obj ≅ S :=
  asIso (projection S L.obj)

/-- The forward map of the rank-one comparison is the projective-bundle projection. -/
@[simp]
theorem rankOne_hom (L : InvertibleSheaf S) : (rankOne L).hom = projection S L.obj :=
  asIso_hom _

/-- On the projective bundle of a line bundle, the tautological quotient is the isomorphism
from its pullback to `𝒪(1)`. -/
instance isIso_universalQuotient_of_isInvertible [SheafOfModules.isInvertible S E] :
    IsIso (universalQuotient S E) :=
  Scheme.Modules.Hom.isIso_of_epi_of_isInvertible _

end TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle
