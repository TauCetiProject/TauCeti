/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum
public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic

/-!
# Relative spectra of trivial algebras

If the unit `𝒪_X ⟶ A` of a quasi-coherent commutative `𝒪_X`-algebra `A` is an isomorphism, the
structure morphism `Spec_X A ⟶ X` of its relative spectrum is an isomorphism
(`CategoryTheory.CommMon.isIso_relativeSpecToBase_of_isIso_one`): over every affine open `U` of
`X`, the relative spectrum is `Spec Γ(A, U)`, and the structure map `Γ(X, U) ⟶ Γ(A, U)` is the
unit on sections over `U`, hence bijective.

For a graded quasi-coherent algebra `A = (Aₙ)ₙ`, the unit of the direct sum `⨁ₙ Aₙ` is an
isomorphism as soon as the unit `𝒪_X ⟶ A₀` is one and every component of positive degree vanishes
(`TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_one_toQuasicoherentAlgebra`). This is
the case of the normal cone algebra and of the symmetric algebra of the conormal sheaf of an open
immersion.

## Main declarations

* `CategoryTheory.CommMon.isIso_relativeSpecToBase_of_isIso_one`: a quasi-coherent algebra whose
  unit is an isomorphism has relative spectrum isomorphic to the base.
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_ιTotal_zero` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isIso_one_toQuasicoherentAlgebra`: a
  graded algebra concentrated in degree zero is its degree-zero component, and its direct sum has
  invertible unit when `A₀` does.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry MonObj

universe u

noncomputable section

namespace CategoryTheory.CommMon

variable {X : Scheme.{u}} (A : CommMon X.Modules)

/-- If the unit `𝒪_X ⟶ A` is an isomorphism, the structure map `Γ(X, U) ⟶ Γ(A, U)` is bijective
on every open `U`: it is the unit on sections over `U`. -/
theorem bijective_algebraMap_of_isIso_one [IsIso η[A.X]] (U : X.Opens) :
    Function.Bijective (algebraMap Γ(X, U) Γ(A.X, U)) := by
  have h : ∀ r : Γ(X, U), algebraMap Γ(X, U) Γ(A.X, U) r = (η[A.X]).app U r := fun r ↦ by
    rw [CommMon.sections_algebraMap_def, Scheme.Modules.sectionsFunctor_ε]
    rfl
  rw [show (algebraMap Γ(X, U) Γ(A.X, U) : Γ(X, U) → Γ(A.X, U)) = (η[A.X]).app U from funext h]
  exact ConcreteCategory.bijective_of_isIso _

/-- **The relative spectrum of a trivial algebra is the base.** If the unit `𝒪_X ⟶ A` of a
quasi-coherent commutative `𝒪_X`-algebra is an isomorphism, the structure morphism
`Spec_X A ⟶ X` is an isomorphism: over an affine open `U`, it is `Spec` of the structure map
`Γ(X, U) ⟶ Γ(A, U)`, which is bijective. -/
theorem isIso_relativeSpecToBase_of_isIso_one [A.X.IsQuasicoherent] [IsIso η[A.X]] :
    IsIso A.relativeSpecToBase := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ (iSup_affineOpens_eq_top X) fun U ↦ ?_
  let V : X.AffineZariskiSite := ⟨U.val, U.property⟩
  have hφ : IsIso (A.toSectionsPresheaf.app (op V.val)) := by
    rw [CommMon.toSectionsPresheaf_app]
    exact (ConcreteCategory.isIso_iff_bijective _).2 (A.bijective_algebraMap_of_isIso_one V.val)
  have hpb := A.isPullback_relativeSpecCover V
  have hpb' := isPullback_morphismRestrict A.relativeSpecToBase V.val
  have he : A.relativeSpecToBase ∣_ V.val = (hpb.isoIsPullback _ _ hpb').inv ≫
      Spec.map (A.toSectionsPresheaf.app (op V.val)) ≫ V.property.isoSpec.inv :=
    (Iso.eq_inv_comp _).2 (hpb.isoIsPullback_hom_fst _ _ hpb')
  change IsIso (A.relativeSpecToBase ∣_ V.val)
  rw [he]
  infer_instance

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

variable {X : Scheme.{u}} (A : GradedQuasicoherentAlgebra X)

/-- If every homogeneous component of positive degree vanishes, the inclusion of the degree-zero
component into the direct sum `⨁ₙ Aₙ` is an isomorphism. -/
theorem isIso_ιTotal_zero (h : ∀ n, n ≠ 0 → IsZero (A.obj.X n)) : IsIso (ιTotal A 0) := by
  let p : (toQuasicoherentAlgebra.obj A).obj.X ⟶ A.obj.X 0 :=
    Cofan.IsColimit.desc (isColimitιTotal A) fun n ↦
      if hn : n = 0 then eqToHom (by rw [hn]) else (h n hn).to_ _
  have hp : ιTotal A 0 ≫ p = 𝟙 _ := by
    simpa [p] using Cofan.IsColimit.fac (isColimitιTotal A) (fun n ↦
      if hn : n = 0 then eqToHom (by rw [hn]) else (h n hn).to_ (A.obj.X 0)) 0
  refine ⟨p, hp, toQuasicoherentAlgebra_hom_ext fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    rw [reassoc_of% hp, Category.comp_id]
  · exact (h n hn).eq_of_src _ _

/-- **A graded algebra concentrated in degree zero has trivial direct sum.** If the unit
`𝒪_X ⟶ A₀` is an isomorphism and every homogeneous component of positive degree vanishes, the
unit of the direct-sum algebra `⨁ₙ Aₙ` is an isomorphism. -/
theorem isIso_one_toQuasicoherentAlgebra [IsIso A.obj.toMon.one]
    (h : ∀ n, n ≠ 0 → IsZero (A.obj.X n)) :
    IsIso η[(toQuasicoherentAlgebra.obj A).obj.X] := by
  have := A.isIso_ιTotal_zero h
  rw [← one_ιTotal]
  exact IsIso.comp_isIso' inferInstance this

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
